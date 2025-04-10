Require Import DirCache.
Require Import Balloc.
Require Import Prog ProgMonad.
Require Import BasicProg.
Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import FSLayout.
Require Import Pred.
Require Import Arith.
Require Import GenSepN.
Require Import List ListUtils.
Require Import Hoare.
Require Import Log.
Require Import SepAuto.
Require Import Array.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import GenSepAuto.
Require Import Lock.
Require Import Errno.
Import ListNotations.
Require Import DirTreePath.
Require Import DirTreeDef.
Require Import DirTreePred.
Require Import DirTreeRep.
Require Import DirTreeSafe.
Require Import DirTreeNames.
Require Import DirTreeInodes.
Set Implicit Arguments.
Module SDIR := CacheOneDir.
Module DIRTREE.
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSICache := BFILE.MSICache.
Notation MSCache := BFILE.MSCache.
Notation MSDBlocks := BFILE.MSDBlocks.
Definition namei fsxp dnum (fnlist : list string) mscs :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, inum, isdir, valid) <- ForEach fn fnrest fnlist
      Hashmap hm
      Ghost [ mbase m sm F Fm IFs Ftop treetop freeinodes freeinode_pred ilist freeblocks mscs0 ]
      Loopvar [ mscs inum isdir valid ]
      Invariant
        LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
        exists tree bflist fndone,
        [[ fndone ++ fnrest = fnlist ]] *
        [[ valid = OK tt ->
           (Ftop * tree_pred_except ibxp fndone treetop * tree_pred ibxp tree * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ isError valid ->
           (Ftop * tree_pred ibxp treetop * freeinode_pred)%pred (list2nmem bflist) ]] *
        [[ (Fm * BFILE.rep bxp IFs ixp bflist ilist freeblocks (MSAllocC mscs) (MSCache mscs) (MSICache mscs) (MSDBlocks mscs) *
            IAlloc.rep BFILE.freepred ibxp freeinodes freeinode_pred (IAlloc.mk_memstate (MSLL mscs) (MSIAllocC mscs)))%pred
           (list2nmem m) ]] *
        [[ dnum = dirtree_inum treetop ]] *
        [[ valid = OK tt -> inum = dirtree_inum tree ]] *
        [[ valid = OK tt -> isdir = dirtree_isdir tree ]] *
        [[ valid = OK tt -> find_subtree fnlist treetop = find_subtree fnrest tree ]] *
        [[ valid = OK tt -> find_subtree fndone treetop = Some tree ]] *
        [[ isError valid -> find_subtree fnlist treetop = None ]] *
        [[ MSAlloc mscs = MSAlloc mscs0 ]] *
        [[ MSAllocC mscs = MSAllocC mscs0 ]] *
        [[ MSDBlocks mscs = MSDBlocks mscs0 ]]
      OnCrash
        LOG.intact fsxp.(FSXPLog) F mbase sm hm
      Begin
        match valid with
        | Err e =>
          Ret ^(mscs, inum, isdir, Err e)
        | OK _ =>
          If (bool_dec isdir true) {
            let^ (mscs, r) <- SDIR.lookup lxp ixp inum fn mscs;
            match r with
            | Some (inum, isdir) => Ret ^(mscs, inum, isdir, OK tt)
            | None => Ret ^(mscs, inum, isdir, Err ENOENT)
            end
          } else {
            Ret ^(mscs, inum, isdir, Err ENOTDIR)
          }
        end
    Rof ^(mscs, dnum, true, OK tt);
    match valid with
    | OK _ =>
      Ret ^(mscs, OK (inum, isdir))
    | Err e =>
      Ret ^(mscs, Err e)
    end.
Definition mkfile fsxp dnum name fms :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let '(al, alc, ialc, ms, icache, cache, dbcache) := (MSAlloc fms, MSAllocC fms, MSIAllocC fms, MSLL fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (ms, oi) <- IAlloc.alloc lxp ibxp (IAlloc.mk_memstate ms ialc);
    let fms := BFILE.mk_memstate al (IAlloc.MSLog ms) alc (IAlloc.MSCache ms) icache cache dbcache in
    match oi with
    | None => Ret ^(fms, Err ENOSPCINODE)
    | Some inum =>
      let^ (fms, ok) <- SDIR.link lxp bxp ixp dnum name inum false fms;
      match ok with
      | OK _ =>
        Ret ^(fms, OK (inum : addr))
      | Err e =>
        Ret ^(fms, Err e)
      end
    end.
Definition mkdir fsxp dnum name fms :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let '(al, alc, ialc, ms, icache, cache, dbcache) := (MSAlloc fms, MSAllocC fms, MSIAllocC fms, MSLL fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (ms, oi) <- IAlloc.alloc lxp ibxp (IAlloc.mk_memstate ms ialc);
    let fms := BFILE.mk_memstate al (IAlloc.MSLog ms) alc (IAlloc.MSCache ms) icache cache dbcache in
    match oi with
    | None => Ret ^(fms, Err ENOSPCINODE)
    | Some inum =>
      let^ (fms, ok) <- SDIR.link lxp bxp ixp dnum name inum true fms;
      match ok with
      | OK _ =>
        Ret ^(fms, OK (inum : addr))
      | Err e =>
        Ret ^(fms, Err e)
      end
    end.
Definition delete fsxp dnum name mscs :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, oi) <- SDIR.lookup lxp ixp dnum name mscs;
    match oi with
    | None => Ret ^(mscs, Err ENOENT)
    | Some (inum, isdir) =>
      let^ (mscs, ok) <- If (bool_dec isdir false) {
        Ret ^(mscs, true)
      } else {
        let^ (mscs, l) <- SDIR.readdir lxp ixp inum mscs;
        match l with
        | nil => Ret ^(mscs, true)
        | _ => Ret ^(mscs, false)
        end
      };
      If (bool_dec ok false) {
        Ret ^(mscs, Err ENOTEMPTY)
      } else {
        let^ (mscs, ok) <- SDIR.unlink lxp ixp dnum name mscs;
        match ok with
        | OK _ =>
          mscs <- BFILE.reset lxp bxp ixp inum mscs;
          mscs' <- IAlloc.free lxp ibxp inum (IAlloc.mk_memstate (MSLL mscs) (MSIAllocC mscs));
          Ret ^(BFILE.mk_memstate (MSAlloc mscs) (IAlloc.MSLog mscs') (MSAllocC mscs) (IAlloc.MSCache mscs') (MSICache mscs) (MSCache mscs) (MSDBlocks mscs), OK tt)
        | Err e =>
          Ret ^(mscs, Err e)
        end
     }
    end.
Definition rename fsxp dnum srcpath srcname dstpath dstname mscs :=
    let '(lxp, bxp, ibxp, ixp) := ((FSXPLog fsxp), (FSXPBlockAlloc fsxp),
                                   fsxp, (FSXPInode fsxp)) in
    let^ (mscs, osrcdir) <- namei fsxp dnum srcpath mscs;
    match osrcdir with
    | Err _ => Ret ^(mscs, Err ENOENT)
    | OK (_, false) => Ret ^(mscs, Err ENOTDIR)
    | OK (dsrc, true) =>
      let^ (mscs, osrc) <- SDIR.lookup lxp ixp dsrc srcname mscs;
      match osrc with
      | None => Ret ^(mscs, Err ENOENT)
      | Some (inum, inum_isdir) =>
        let^ (mscs, _) <- SDIR.unlink lxp ixp dsrc srcname mscs;
        let^ (mscs, odstdir) <- namei fsxp dnum dstpath mscs;
        match odstdir with
        | Err _ => Ret ^(mscs, Err ENOENT)
        | OK (_, false) => Ret ^(mscs, Err ENOTDIR)
        | OK (ddst, true) =>
          let^ (mscs, odst) <- SDIR.lookup lxp ixp ddst dstname mscs;
          match odst with
          | None =>
            let^ (mscs, ok) <- SDIR.link lxp bxp ixp ddst dstname inum inum_isdir mscs;
            Ret ^(mscs, ok)
          | Some _ =>
            let^ (mscs, ok) <- delete fsxp ddst dstname mscs;
            match ok with
            | OK _ =>
              let^ (mscs, ok) <- SDIR.link lxp bxp ixp ddst dstname inum inum_isdir mscs;
              Ret ^(mscs, ok)
            | Err e =>
              Ret ^(mscs, Err e)
            end
          end
        end
      end
    end.
Definition read fsxp inum off mscs :=
    let^ (mscs, v) <- BFILE.read (FSXPLog fsxp) (FSXPInode fsxp) inum off mscs;
    Ret ^(mscs, v).
Definition write fsxp inum off v mscs :=
    mscs <- BFILE.write (FSXPLog fsxp) (FSXPInode fsxp) inum off v mscs;
    Ret mscs.
Definition dwrite fsxp inum off v mscs :=
    mscs <- BFILE.dwrite (FSXPLog fsxp) (FSXPInode fsxp) inum off v mscs;
    Ret mscs.
Definition datasync fsxp inum mscs :=
    mscs <- BFILE.datasync (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    Ret mscs.
Definition sync fsxp mscs :=
    mscs <- BFILE.sync (FSXPLog fsxp) (FSXPInode fsxp) mscs;
    Ret mscs.
Definition sync_noop fsxp mscs :=
    mscs <- BFILE.sync_noop (FSXPLog fsxp) (FSXPInode fsxp) mscs;
    Ret mscs.
Definition truncate fsxp inum nblocks mscs :=
    let^ (mscs, ok) <- BFILE.truncate (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp)
                                     inum nblocks mscs;
    Ret ^(mscs, ok).
Definition getlen fsxp inum mscs :=
    let^ (mscs, len) <- BFILE.getlen (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    Ret ^(mscs, len).
Definition getattr fsxp inum mscs :=
    let^ (mscs, attr) <- BFILE.getattrs (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    Ret ^(mscs, attr).
Definition setattr fsxp inum attr mscs :=
    mscs <- BFILE.setattrs (FSXPLog fsxp) (FSXPInode fsxp) inum attr mscs;
    Ret mscs.
Definition updattr fsxp inum kv mscs :=
    mscs <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum kv mscs;
    Ret mscs.
Local Hint Unfold SDIR.rep_macro rep : hoare_unfold.
Theorem namei_ok : forall fsxp dnum fnlist mscs,
    {< F mbase m sm Fm Ftop tree ilist freeblocks,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist freeblocks mscs sm)%pred (list2nmem m) ]] *
           [[ dnum = dirtree_inum tree ]] *
           [[ dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs') sm hm' *
           [[ (Fm * rep fsxp Ftop tree ilist freeblocks mscs' sm)%pred (list2nmem m) ]] *
           [[ (isError r /\ None = find_name fnlist tree) \/
              (exists v, (r = OK v /\ Some v = find_name fnlist tree))%type ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} namei fsxp dnum fnlist mscs.
Proof.
(* original proof tokens: 1347 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (namei _ _ _ _) _) => apply namei_ok : prog.
Theorem mkdir_ok' : forall fsxp dnum name mscs,
    {< F mbase m sm Fm Ftop tree tree_elem ilist freeblocks,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist freeblocks mscs sm)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            exists inum ilist' freeblocks',
            let tree' := TreeDir dnum ((name, TreeDir inum nil) :: tree_elem) in
            [[ r = OK inum ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' freeblocks' mscs' sm)%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc freeblocks  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc freeblocks' (MSAlloc mscs')) tree' ]] )
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} mkdir fsxp dnum name mscs.
(* hint proof tokens: 281 *)
Proof.
    unfold mkdir, rep.
    step.
    subst; simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    unfold IAlloc.MSLog in *.
    step.
    eapply IAlloc.ino_valid_goodSize; eauto.
    destruct_branch; [ | step ].
    prestep; norml; inv_option_eq; msalloc_eq.

    cancel.
    match goal with a: IAlloc.Alloc.memstate |- _
      => destruct a; cbn in *; subst
    end.
    or_r; cancel.

    unfold tree_dir_names_pred at 1. cancel; eauto.
    denote (dummy1 =p=> _) as Hx. rewrite Hx.
    unfold tree_dir_names_pred; cancel.
    denote (BFILE.freepred _) as Hy. unfold BFILE.freepred in Hy. subst.
    apply SDIR.bfile0_empty.
    apply emp_empty_mem.
    apply sep_star_comm. apply ptsto_upd_disjoint. auto. auto.

    msalloc_eq.
    eapply dirlist_safe_mkdir; auto.

    Unshelve.
    all: try eauto; exact emp; try exact nil; try exact empty_mem; try exact BFILE.bfile0.
  Qed.
Theorem mkdir_ok : forall fsxp dnum name mscs,
    {< F mbase sm m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            exists inum tree' ilist' frees', [[ r = OK inum ]] *
            [[ tree' = update_subtree pathname (TreeDir dnum
                      ((name, TreeDir inum nil) :: tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] )
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} mkdir fsxp dnum name mscs.
(* hint proof tokens: 87 *)
Proof.
    intros; eapply pimpl_ok2. apply mkdir_ok'.
    unfold rep; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0 := tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
    eapply dirlist_safe_subtree; eauto.
  Qed.
Theorem mkfile_ok' : forall fsxp dnum name mscs,
    {< F mbase sm m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r) exists m',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            exists inum ilist' tree' frees',
            [[ r = OK inum ]] * [[ ~ In name (map fst tree_elem) ]] *
            [[ tree' = update_subtree pathname (TreeDir dnum
                        (tree_elem ++ [(name, (TreeFile inum dirfile0))] )) tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} mkfile fsxp dnum name mscs.
Proof.
(* original proof tokens: 398 *)

(* No more tactics to try *)
Admitted.

Hint Extern 0 (okToUnify (rep _ _ _ _ _ _ _) (rep _ _ _ _ _ _ _)) => constructor : okToUnify.
Theorem mkfile_ok : forall fsxp dnum name mscs,
    {< F mbase sm m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r) exists m',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            exists inum ilist' tree' frees',
            [[ r = OK inum ]] *
            [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} mkfile fsxp dnum name mscs.
(* hint proof tokens: 68 *)
Proof.
    unfold mkfile; intros.
    eapply pimpl_ok2. apply mkfile_ok'.
    cancel.
    eauto.
    step.

    or_r; cancel.
    rewrite tree_graft_not_in_dirents; auto.
    rewrite <- tree_graft_not_in_dirents; auto.
  Qed.
Hint Extern 1 ({{_}} Bind (mkdir _ _ _ _) _) => apply mkdir_ok : prog.
Hint Extern 1 ({{_}} Bind (mkfile _ _ _ _) _) => apply mkfile_ok : prog.
Lemma false_False_true : forall x,
    (x = false -> False) -> x = true.
(* hint proof tokens: 14 *)
Proof.
    destruct x; tauto.
  Qed.
Lemma true_False_false : forall x,
    (x = true -> False) -> x = false.
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 15 *)

destruct x; auto; tauto.
Qed.

Ltac subst_bool :=
    repeat match goal with
    | [ H : ?x = true |- _ ] => is_var x; subst x
    | [ H : ?x = false |- _ ] => is_var x; subst x
    | [ H : ?x = false -> False  |- _ ] => is_var x; apply false_False_true in H; subst x
    | [ H : ?x = true -> False   |- _ ] => is_var x; apply true_False_false in H; subst x
    end.
Hint Extern 0 (okToUnify (tree_dir_names_pred _ _ _) (tree_dir_names_pred _ _ _)) => constructor : okToUnify.
Theorem delete_ok' : forall fsxp dnum name mscs,
    {< F mbase sm m Fm Ftop tree tree_elem frees ilist,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            [[ r = OK tt ]] * exists frees' ilist',
            let tree' := delete_from_dir name tree in
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
            [[ forall inum def', inum <> dnum ->
                 (In inum (tree_inodes tree') \/ (~ In inum (tree_inodes tree))) ->
                 selN ilist inum def' = selN ilist' inum def' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} delete fsxp dnum name mscs.
(* hint proof tokens: 1169 *)
Proof.
    unfold delete, rep.

    
    intros; eapply pimpl_ok2; monad_simpl; eauto with prog; intros; norm'l.
    assert (tree_inodes_distinct (TreeDir dnum tree_elem)) as HiID.
    eapply rep_tree_inodes_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.
    assert (tree_names_distinct (TreeDir dnum tree_elem)) as HdID.
    eapply rep_tree_names_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.

    
    subst; simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    safecancel. 2: eauto.
    unfold SDIR.rep_macro.
    cancel; eauto.

    denote! (_ (list2nmem m)) as Hm0; rewrite <- locked_eq in Hm0.
    step.
    step.
    step.

    
    step.

    
    prestep. norml.
    denote dirlist_pred as Hx.
    erewrite dirlist_extract with (inum := a0) in Hx; eauto.
    destruct_lift Hx.
    destruct dummy4; simpl in *; try congruence; subst.
    denote dirlist_pred_except as Hx; destruct_lift Hx; auto.
    cancel.

    
    prestep. norml; msalloc_eq.
    denote dirlist_pred as Hx.
    erewrite dirlist_extract with (inum := n) in Hx; eauto.
    destruct_lift Hx.
    denote dirlist_pred_except as Hx; destruct_lift Hx; auto.
    unfold IAlloc.MSLog in *; cancel.
    match goal with H: (_ * ptsto ?a _)%pred ?m |- context [ptsto ?a]
      => exists m; solve [pred_apply; cancel]
    end.

    
    step.
    or_r; safecancel.
    denote (pimpl _ freepred') as Hx; rewrite <- Hx.
    rewrite dir_names_delete with (dnum := dnum); eauto.
    rewrite dirlist_pred_except_delete; eauto.
    cancel.
    eauto.
    apply dirlist_safe_delete; auto.

    
    denote! (tree_dir_names_pred' _ _) as Hy.
    eapply find_dirlist_exists in Hy as Hy'.
    deex.
    denote dirlist_combine as Hx.
    eapply tree_inodes_distinct_delete in Hx as Hx'; eauto.
    eassumption.

    
    denote! (forall _ _, (_ = _ -> False) -> _ = _) as Hz.
    eapply Hz.
    intro; subst.
    denote! (In _ _ -> False) as Hq.
    eapply Hq.
    denote ((name |-> (_, false))%pred) as Hy.
    eapply find_dirlist_exists in Hy as Hy'; eauto.
    deex.
    denote (dirtree_inum _ = dirtree_inum _ ) as Hd.
    rewrite Hd.
    eapply find_dirlist_tree_inodes; eauto.

    cancel.
    cancel.

    unfold IAlloc.MSLog in *; cancel.
    or_l. cancel.

    
    prestep.
    intros; norm'l.
    denote dirlist_pred as Hx; subst_bool.
    rewrite dirlist_extract_subdir in Hx; eauto; simpl in Hx.
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel. eauto.

    step.
    step.
    step.
    step.
    step. msalloc_eq.
    cancel.
    exists (list2nmem flist'). eexists.
    pred_apply. cancel.
    unfold IAlloc.MSLog in *.
    step.

    
    or_r; cancel.
    denote (pimpl _ freepred') as Hx; rewrite <- Hx.
    denote (tree_dir_names_pred' _ _) as Hz.
    erewrite (@dlist_is_nil _ _ _ _ _ Hz); eauto.
    rewrite dirlist_pred_except_delete; eauto.
    rewrite dir_names_delete with (dnum := dnum).
    cancel. eauto. eauto. eauto.
    reflexivity.
    apply dirlist_safe_delete; auto.

    
    eapply find_dirlist_exists in H9 as H9'.
    deex.
    denote dirlist_combine as Hx.
    eapply tree_inodes_distinct_delete in Hx as Hx'; eauto.
    eassumption.

    
    denote (selN _ _ _ = selN _ _ _) as Hs.
    denote (In _ (dirlist_combine _ _)) as Hi.
    denote (tree_dir_names_pred' tree_elem) as Ht.
    apply Hs.
    intro; subst.
    eapply Hi.
    eapply find_dirlist_exists with (inum := a0) in Ht as Ht'.
    deex.
    eapply find_dirlist_tree_inodes; eauto.
    eassumption.

    step.
    step.
    cancel; auto.
    cancel; auto.

    Unshelve.
    all: try match goal with | [ |- DirTreePred.SDIR.rep _ _ ] => eauto end.
    all: try exact unit.
    all: try solve [repeat constructor].
    all: eauto.
    all: try exact string_dec.
  Qed.
Theorem read_ok : forall fsxp inum off mscs,
    {< F mbase sm m pathname Fm Ftop tree f B v ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ (B * off |-> v)%pred (list2nmem (DFData f)) ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs') sm hm' *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs' sm)%pred (list2nmem m) ]] *
           [[ r = fst v /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} read fsxp inum off mscs.
(* hint proof tokens: 92 *)
Proof.
    unfold read, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.

    eapply list2nmem_inbound; eauto.
    step; msalloc_eq.
    cancel.

    rewrite <- subtree_fold by eauto.
    pred_apply. cancel.

    cancel; eauto.
  Qed.
Theorem dwrite_ok : forall fsxp inum off v mscs,
    {< F ds sm pathname Fm Ftop tree f Fd vs ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds ds!!) (MSLL mscs) sm hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist frees mscs sm ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]] *
           [[ PredCrash.sync_invariant F ]]
    POST:hm' RET:mscs'
           exists ds' tree' f' sm' bn,
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds' ds'!!) (MSLL mscs') sm' hm' *
           [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
           [[ BFILE.block_belong_to_file ilist bn inum off ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ MSCache mscs' = MSCache mscs ]] *
           [[ MSAllocC mscs' = MSAllocC mscs ]] *
           [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
           
           [[[ ds'!! ::: (Fm  * rep fsxp Ftop tree' ilist frees mscs' sm') ]]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[[ (DFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
           [[ f' = mk_dirfile (updN (DFData f) off (v, vsmerge vs)) (DFAttr f) ]] *
           [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                           ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
    XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm' \/
           exists bn, [[ BFILE.block_belong_to_file ilist bn inum off ]] *
           LOG.recover_any fsxp.(FSXPLog) F (dsupd ds bn (v, vsmerge vs)) hm'
    >} dwrite fsxp inum off v mscs.
Proof.
(* original proof tokens: 119 *)

(* No more tactics to try *)
Admitted.

Theorem datasync_ok : forall fsxp inum mscs,
    {< F ds sm pathname Fm Ftop tree f ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds ds!!) (MSLL mscs) sm hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist frees mscs sm ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[ PredCrash.sync_invariant F ]]
    POST:hm' RET:mscs'
           exists ds' sm' tree' al,
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds' ds'!!) (MSLL mscs') sm' hm' *
           [[ tree' = update_subtree pathname (TreeFile inum (synced_dirfile f)) tree ]] *
           [[ ds' = dssync_vecs ds al ]] *
           [[[ ds'!! ::: (Fm * rep fsxp Ftop tree' ilist frees mscs' sm') ]]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ MSCache mscs' = MSCache mscs ]] *
           [[ MSAllocC mscs' = MSAllocC mscs ]] *
           [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
           [[ length al = length (DFData f) /\ forall i, i < length al ->
              BFILE.block_belong_to_file ilist (selN al i 0) inum i ]] *
           [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                           ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
    CRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm'
    >} datasync fsxp inum mscs.
Proof.
(* original proof tokens: 94 *)

(* No more tactics to try *)
Admitted.

Theorem sync_ok : forall fsxp mscs,
    {< F ds sm Fm Ftop tree ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist frees mscs sm ]]] *
           [[ PredCrash.sync_invariant F ]]
    POST:hm' RET:mscs'
           LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn (ds!!, nil)) (MSLL mscs') sm hm' *
           [[ MSCache mscs' = MSCache mscs ]] *
           [[ MSAlloc mscs' = negb (MSAlloc mscs) ]] *
           [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
           [[ MSAllocC mscs' = MSAllocC mscs ]] *
           [[ MSICache mscs' = MSICache mscs ]] *
           [[ MSDBlocks mscs' = MSDBlocks mscs ]]
    XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm'
     >} sync fsxp mscs.
(* hint proof tokens: 17 *)
Proof.
    unfold sync, rep.
    hoare.
  Qed.
Theorem sync_noop_ok : forall fsxp mscs,
    {< F ds sm Fm Ftop tree ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[[ ds!! ::: Fm * rep fsxp Ftop tree ilist frees mscs sm ]]] *
           [[ PredCrash.sync_invariant F ]]
    POST:hm' RET:mscs'
           LOG.rep fsxp.(FSXPLog) F (LOG.NoTxn ds) (MSLL mscs') sm hm' *
           [[ MSCache mscs' = MSCache mscs ]] *
           [[ MSAlloc mscs' = negb (MSAlloc mscs) ]]
    XCRASH:hm'
           LOG.recover_any fsxp.(FSXPLog) F ds hm'
     >} sync_noop fsxp mscs.
(* hint proof tokens: 19 *)
Proof.
    unfold sync_noop, rep.
    hoare.
  Qed.
Theorem truncate_ok : forall fsxp inum nblocks mscs,
    {< F ds sm d pathname Fm Ftop tree f frees ilist,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) (MSLL mscs) sm hm *
           [[[ d ::: Fm * rep fsxp Ftop tree ilist frees mscs sm ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs', ok)
           exists d',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d') (MSLL mscs') sm hm' *
           [[ MSCache mscs' = MSCache mscs ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
          ([[ isError ok ]] \/
           [[ ok = OK tt ]] *
           exists tree' f' ilist' frees',
           [[[ d' ::: Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm ]]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = mk_dirfile (setlen (DFData f) nblocks ($0, nil)) (DFAttr f) ]] *
           [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                           ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
           [[ nblocks >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F ds sm hm'
    >} truncate fsxp inum nblocks mscs.
(* hint proof tokens: 96 *)
Proof.
    unfold truncate, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.
    step; msalloc_eq.
    or_r.
    cancel.
    rewrite <- subtree_absorb by eauto. cancel.

    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file_trans; auto.
  Qed.
Theorem getlen_ok : forall fsxp inum mscs,
    {< F mbase sm m pathname Fm Ftop tree f frees ilist,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs') sm hm' *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs' sm)%pred (list2nmem m) ]] *
           [[ r = length (DFData f) ]] *
           [[ MSCache mscs' = MSCache mscs ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} getlen fsxp inum mscs.
Proof.
(* original proof tokens: 79 *)

(* No more tactics to try *)
Admitted.

Theorem getattr_ok : forall fsxp inum mscs,
    {< F ds sm d pathname Fm Ftop tree f ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) (MSLL mscs) sm hm *
           [[[ d ::: Fm * rep fsxp Ftop tree ilist frees mscs sm ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs',r)
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn ds d) (MSLL mscs') sm hm' *
           [[[ d ::: Fm * rep fsxp Ftop tree ilist frees mscs' sm ]]] *
           [[ MSCache mscs' = MSCache mscs ]] *
           [[ r = DFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F ds sm hm'
    >} getattr fsxp inum mscs.
Proof.
(* original proof tokens: 78 *)

(* No more tactics to try *)
Admitted.

Theorem setattr_ok : forall fsxp inum attr mscs,
    {< F mbase sm m pathname Fm Ftop tree f ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] 
    POST:hm' RET:mscs'
           exists m' tree' f' ilist',
           LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm)%pred (list2nmem m') ]] *
           [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
           [[ f' = mk_dirfile (DFData f) attr ]] *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                           ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
           [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} setattr fsxp inum attr mscs.
Proof.
(* original proof tokens: 96 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (read _ _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _) _) => apply dwrite_ok : prog.
Hint Extern 1 ({{_}} Bind (datasync _ _ _) _) => apply datasync_ok : prog.
Hint Extern 1 ({{_}} Bind (sync _ _) _) => apply sync_ok : prog.
Hint Extern 1 ({{_}} Bind (sync_noop _ _) _) => apply sync_noop_ok : prog.
Hint Extern 1 ({{_}} Bind (truncate _ _ _ _) _) => apply truncate_ok : prog.
Hint Extern 1 ({{_}} Bind (getlen _ _ _) _) => apply getlen_ok : prog.
Hint Extern 1 ({{_}} Bind (getattr _ _ _) _) => apply getattr_ok : prog.
Hint Extern 1 ({{_}} Bind (setattr _ _ _ _) _) => apply setattr_ok : prog.
Theorem delete_ok : forall fsxp dnum name mscs,
    {< F mbase sm m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            [[ r = OK tt ]] * exists tree' ilist' frees',
            [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
            [[ forall inum def', inum <> dnum ->
                 (In inum (tree_inodes tree') \/ (~ In inum (tree_inodes tree))) ->
                selN ilist inum def' = selN ilist' inum def' ]])
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} delete fsxp dnum name mscs.
(* hint proof tokens: 543 *)
Proof.
    intros; eapply pimpl_ok2. apply delete_ok'.

    intros; norml; unfold stars; simpl.
    rewrite rep_tree_distinct_impl in *.
    unfold rep in *; cancel.

    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0:=tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
    eapply dirlist_safe_subtree; eauto.
    denote (dirlist_combine tree_inodes _) as Hx.
    specialize (Hx inum def' H4).
    intuition; try congruence.

    destruct_lift H0.
    edestruct tree_inodes_pathname_exists. 3: eauto.
    eapply tree_names_distinct_update_subtree; eauto.
    eapply tree_names_distinct_delete_from_list.
    eapply tree_names_distinct_subtree; eauto.

    eapply tree_inodes_distinct_update_subtree; eauto.
    eapply tree_inodes_distinct_delete_from_list.
    eapply tree_inodes_distinct_subtree; eauto.
    simpl. eapply incl_cons2.
    eapply tree_inodes_incl_delete_from_list.

    

    repeat deex.
    destruct (pathname_decide_prefix pathname x); repeat deex.

    
    erewrite find_subtree_app in *; eauto.
    eapply H11.

    eapply find_subtree_inum_present in H16; simpl in *.
    intuition. exfalso; eauto.

    
    eapply H9.
    intro.
    edestruct tree_inodes_pathname_exists with (tree := TreeDir dnum tree_elem) (inum := dirtree_inum subtree).
    3: eassumption.

    eapply tree_names_distinct_subtree; eauto.
    eapply tree_inodes_distinct_subtree; eauto.

    destruct H20.
    destruct H20.

    eapply H6.
    exists x0.

    edestruct find_subtree_before_prune_general; eauto.

    eapply find_subtree_inode_pathname_unique.
    eauto. eauto.
    intuition eauto.
    erewrite find_subtree_app; eauto.
    intuition congruence.

    
    eapply H11; eauto.
    right.
    contradict H7; intuition eauto. exfalso; eauto.
    eapply tree_inodes_find_subtree_incl; eauto.
    simpl; intuition.
  Unshelve.
    all: eauto.
  Qed.
Hint Extern 1 ({{_}} Bind (delete _ _ _ _) _) => apply delete_ok : prog.
Theorem rename_cwd_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< F mbase m sm Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ tree = TreeDir dnum tree_elem ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            [[ r = OK tt ]] * exists snum sents dnum dents subtree pruned tree' ilist' frees',
            [[ find_subtree srcpath tree = Some (TreeDir snum sents) ]] *
            [[ find_dirlist srcname sents = Some subtree ]] *
            [[ pruned = tree_prune snum sents srcpath srcname tree ]] *
            [[ find_subtree dstpath pruned = Some (TreeDir dnum dents) ]] *
            [[ tree' = tree_graft dnum dents dstpath dstname subtree pruned ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
            [[ forall inum' def', inum' <> snum -> inum' <> dnum ->
               (In inum' (tree_inodes tree') \/ (~ In inum' (tree_inodes tree))) ->
               selN ilist inum' def' = selN ilist' inum' def' ]] )
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
Proof.
(* original proof tokens: 2044 *)

(* No more tactics to try *)
Admitted.

Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< F mbase sm m pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m) (MSLL mscs) sm hm *
           [[ (Fm * rep fsxp Ftop tree ilist frees mscs sm)%pred (list2nmem m) ]] *
           [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
           exists m', LOG.rep fsxp.(FSXPLog) F (LOG.ActiveTxn mbase m') (MSLL mscs') sm hm' *
           [[ MSAlloc mscs' = MSAlloc mscs ]] *
           ([[ isError r ]] \/
            [[ r = OK tt ]] *
            exists srcnum srcents dstnum dstents subtree pruned renamed tree' ilist' frees',
            [[ find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ]] *
            [[ find_dirlist srcname srcents = Some subtree ]] *
            [[ pruned = tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) ]] *
            [[ find_subtree dstpath pruned = Some (TreeDir dstnum dstents) ]] *
            [[ renamed = tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
            [[ tree' = update_subtree pathname renamed tree ]] *
            [[ (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)%pred (list2nmem m') ]] *
            [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                            ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
            [[ forall inum' def', inum' <> srcnum -> inum' <> dstnum ->
               In inum' (tree_inodes tree') ->
               selN ilist inum' def' = selN ilist' inum' def' ]] )
    CRASH:hm'
           LOG.intact fsxp.(FSXPLog) F mbase sm hm'
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
Proof.
(* original proof tokens: 733 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.
End DIRTREE.
