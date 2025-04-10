Require Import Mem.
Require Import Word.
Require Import Ascii.
Require Import String.
Require Import Dir.
Require Import Lia.
Require Import Prog.
Require Import BasicProg.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import Log.
Require Import BFile.
Require Import GenSepN.
Require Import ListPred.
Require Import MemMatch.
Require Import FunctionalExtensionality.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import Errno.
Require Import DirName.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import StringUtils.
Require Import MapUtils.
Require List.
Set Implicit Arguments.
Module CacheOneDir.
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSCache := BFILE.MSCache.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSDBlocks := BFILE.MSDBlocks.
Definition empty_cache : Dcache_type := Dcache.empty _.
Fixpoint fill_cache' (files: (list (string * (addr * bool)))) ocache : Dcache_type  :=
    match files with
    | nil => ocache
    | f::files' => fill_cache' files' (Dcache.add (fst f) (snd f) ocache)
    end.
Definition fill_cache files := fill_cache' files empty_cache.
Definition init_cache lxp ixp dnum ms :=
    let^ (ms, files) <- SDIR.readdir lxp ixp dnum ms;
    let ocache := fill_cache files in
    ms <- BFILE.cache_put dnum (ocache, 0) ms;
    AlertModified;;
    Ret ^(ms, (ocache, 0)).
Definition get_dcache' (lxp:FSLayout.log_xparams) (ixp:Inode.INODE.IRecSig.xparams) dnum ms :=
    let^ (ms, ocache) <- BFILE.cache_get dnum ms;
    match ocache with
    | None =>
      ms <- BFILE.cache_put dnum (Dcache.empty _, 0) ms;
      Ret ^(ms, (Dcache.empty _, 0))
    | Some r =>
      Ret ^(ms, r)
    end.
Definition get_dcache lxp ixp dnum ms :=
    let^ (ms, ocache) <- BFILE.cache_get dnum ms;
    match ocache with
    | None =>
      let^ (ms, r0) <- init_cache lxp ixp dnum ms;
      Ret ^(ms, r0)
    | Some r =>
      Ret ^(ms, r)
    end.
Definition lookup lxp ixp dnum name ms :=
    let^ (ms, cache) <- get_dcache lxp ixp dnum ms;
    let r := Dcache.find name (fst cache) in
    Ret ^(ms, r).
Definition unlink lxp ixp dnum name ms :=
    let^ (ms, cache) <- get_dcache lxp ixp dnum ms;
    match (Dcache.find name (fst cache)) with
    | None => Ret ^(ms, Err ENOENT)
    | Some _ =>
      let^ (ms, ix, r) <- SDIR.unlink lxp ixp dnum name ms;
      ms <- BFILE.cache_put dnum (Dcache.remove name (fst cache), ix) ms;
      Ret ^(ms, r)
    end.
Definition link' lxp bxp ixp dnum name inum isdir ms :=
    let^ (ms, cache) <- get_dcache lxp ixp dnum ms;
    let^ (ms, ix, r) <- SDIR.link lxp bxp ixp dnum name inum isdir (snd cache) ms;
    match r with
    | Err _ =>
      Ret ^(ms, r)
    | OK _ =>
      ms <- BFILE.cache_put dnum (Dcache.add name (inum, isdir) (fst cache), ix) ms;
      Ret ^(ms, r)
    end.
Definition link lxp bxp ixp dnum name inum isdir ms :=
    let^ (ms, lookup_res) <- lookup lxp ixp dnum name ms;
    match lookup_res with
    | Some _ =>
      Ret ^(ms, Err EEXIST)
    | None =>
      let^ (ms, r) <- link' lxp bxp ixp dnum name inum isdir ms;
      Ret ^(ms, r)
    end.
Definition readdir lxp ixp dnum ms :=
    let^ (ms, r) <- SDIR.readdir lxp ixp dnum ms;
    Ret ^(ms, r).
Definition rep f (dsmap : @mem string string_dec (addr * bool)) : Prop :=
    SDIR.rep f dsmap /\
    (forall cache hint, BFILE.BFCache f = Some (cache, hint) ->
    forall name, Dcache.find name cache = dsmap name).
Definition rep_macro Fi Fm m bxp ixp (inum : addr) dsmap ilist frees f ms sm : @pred _ addr_eq_dec valuset :=
    (exists flist,
     [[[ m ::: Fm * BFILE.rep bxp sm ixp flist ilist frees (BFILE.MSAllocC ms) (BFILE.MSCache ms) (BFILE.MSICache ms) (BFILE.MSDBlocks ms) ]]] *
     [[[ flist ::: Fi * inum |-> f ]]] *
     [[ rep f dsmap ]])%pred.
Local Hint Unfold rep rep_macro SDIR.rep_macro : hoare_unfold.
Lemma rep_mem_eq : forall f m1 m2,
    rep f m1 -> rep f m2 -> m1 = m2.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Theorem bfile0_empty : rep BFILE.bfile0 empty_mem.
(* hint proof tokens: 31 *)
Proof.
    unfold rep; intuition.
    apply SDIR.bfile0_empty.
    cbn in *. congruence.
  Qed.
Theorem crash_rep : forall f f' m,
    BFILE.file_crash f f' ->
    rep f m ->
    rep f' m.
(* hint proof tokens: 42 *)
Proof.
    unfold rep; intuition.
    eapply SDIR.crash_rep; eauto.
    inversion H; intuition subst; cbn in *.
    congruence.
  Qed.
Hint Resolve Dcache.find_2.
Lemma readmatch_neq: forall F a b m,
    (F * SDIR.readmatch a * SDIR.readmatch b)%pred m ->
    fst a <> fst b.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma fill_cache'_add_comm : forall entries a cache F,
    F * listpred SDIR.readmatch (a :: entries) =p=>
    F * listpred SDIR.readmatch (a :: entries) *
    [[ Dcache.Equal (fill_cache' (a :: entries) cache)
      (Dcache.add (fst a) (snd a) (fill_cache' entries cache)) ]].
(* hint proof tokens: 223 *)
Proof.
    unfold Dcache.Equal; simpl.
    induction entries; intros; simpl.
    cancel.
    do 2 intro; pred_apply; cancel.
    enough (fst a <> fst a0).
    all : repeat match goal with
    | _ => reflexivity
    | [ H: _ |- _ ] => rewrite H; clear H
    | [ |- context [Dcache.find ?k1 (Dcache.add ?k2 _ _)] ] =>
      progress (rewrite ?DcacheDefs.MapFacts.add_eq_o,
                       ?DcacheDefs.MapFacts.add_neq_o by auto)
      || destruct (string_dec k1 k2); subst
    | [ |- context [Dcache.find _ (fill_cache' _ (Dcache.add (fst ?a) _ _))] ] =>
      eapply pimpl_trans in H as ?; [ | | apply (IHentries a)]; try cancel; destruct_lifts
    end.
    eapply readmatch_neq with (m := m).
    pred_apply; cancel.
  Qed.
Lemma fill_cache_correct: forall entries dmap,
    let cache := (fill_cache entries) in
    listpred SDIR.readmatch entries dmap ->
    forall name, Dcache.find name cache = dmap name.
Proof.
(* original proof tokens: 135 *)
intros; unfold fill_cache, listpred; simpl.
induction entries; simpl; intros; auto.
(* No more tactics to try *)
Admitted.

Ltac subst_cache :=
    repeat match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
    | [ H1 : BFILE.BFCache ?f = _ , H2 : BFILE.BFCache ?F = _ |- _ ] => rewrite H1 in H2
    end.
Theorem init_cache_ok : forall bxp lxp ixp dnum ms,
    {< F Fi Fm m0 sm m dmap ilist frees f,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', cache)
           exists f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f' ms' sm *
           [[ BFILE.BFCache f' = Some cache ]] *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]] *
           [[ MSIAllocC ms' = MSIAllocC ms ]] *
           [[ MSDBlocks ms' = MSDBlocks ms ]]
    CRASH:hm'
           LOG.intact lxp F m0 sm hm'
    >} init_cache lxp ixp dnum ms.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (init_cache _ _ _ _) _) => apply init_cache_ok : prog.
Theorem get_dcache_ok : forall lxp ixp dnum ms,
    {< F Fi Fm m0 sm m dmap ilist frees bxp f,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', cache)
           exists f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f' ms' sm *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]] *
           [[ MSIAllocC ms' = MSIAllocC ms ]] *
           [[ MSDBlocks ms' = MSDBlocks ms ]] *
           [[ BFILE.BFCache f' = Some cache ]]
    CRASH:hm'
           LOG.intact lxp F m0 sm hm'
    >} get_dcache lxp ixp dnum ms.
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (get_dcache _ _ _ _) _) => apply get_dcache_ok : prog.
Theorem lookup_ok : forall lxp bxp ixp dnum name ms,
    {< F Fi Fm m0 sm m dmap ilist frees f,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', r)
           exists f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f' ms' sm *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]] *
           [[ MSIAllocC ms' = MSIAllocC ms ]] *
           [[ MSDBlocks ms' = MSDBlocks ms ]] *
         ( [[ r = None /\ notindomain name dmap ]] \/
           exists inum isdir Fd,
           [[ r = Some (inum, isdir) /\ inum <> 0 /\
                   (Fd * name |-> (inum, isdir))%pred dmap ]]) *
           [[ True ]]
    CRASH:hm'
           LOG.intact lxp F m0 sm hm'
    >} lookup lxp ixp dnum name ms.
Proof.
(* original proof tokens: 162 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (lookup _ _ _ _ _) _) => apply lookup_ok : prog.
Theorem readdir_ok : forall lxp bxp ixp dnum ms,
    {< F Fi Fm m0 sm m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', r)
             rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f ms' sm *
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
             [[ listpred SDIR.readmatch r dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSCache ms' = MSCache ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
             [[ True ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} readdir lxp ixp dnum ms.
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Theorem unlink_ok : forall lxp bxp ixp dnum name ms,
    {< F Fi Fm m0 sm m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', r) exists m' dmap' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             rep_macro Fi Fm m' bxp ixp dnum dmap' ilist frees f' ms' sm *
             [[ dmap' = mem_except dmap name ]] *
             [[ notindomain name dmap' ]] *
             [[ r = OK tt -> indomain name dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
             [[ True ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} unlink lxp ixp dnum name ms.
(* hint proof tokens: 176 *)
Proof.
    unfold unlink.
    hoare; msalloc_eq; cbn in *; subst_cache.
    - cancel.
    - unfold mem_except; cbn [fst snd].
      rewrite DcacheDefs.MapFacts.remove_o.
      denote (Dcache.find) as Hf.
      repeat destruct string_dec; (congruence || eauto).
    - cbn in *.
      rewrite mem_except_none; eauto.
      denote (Dcache.find) as Hf.
      erewrite Hf in *; eauto.
    - intros m' ?.
      replace m' with dmap in * by (eauto using SDIR.rep_mem_eq).
      denote (Dcache.find) as Hf.
      erewrite Hf in *; eauto.
  Unshelve.
    all: eauto.
  Qed.
Lemma sdir_rep_cache : forall f c m,
    SDIR.rep f m ->
    SDIR.rep {| BFILE.BFData := BFILE.BFData f; BFILE.BFAttr := BFILE.BFAttr f; BFILE.BFCache := c |} m.
(* hint proof tokens: 39 *)
Proof.
    unfold SDIR.rep, DIR.rep, DIR.Dent.rep, DIR.Dent.items_valid, DIR.Dent.RA.RALen; eauto.
  Qed.
Hint Resolve sdir_rep_cache.
Theorem link'_ok : forall lxp bxp ixp dnum name inum isdir ms,
    {< F Fi Fm m0 sm m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f ms sm *
             [[ notindomain name dmap ]] *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:hm' RET:^(ms', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] *
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm')
        \/  ([[ r = OK tt ]] *
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             rep_macro Fi Fm m' bxp ixp dnum dmap' ilist' frees' f' ms' sm *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} link' lxp bxp ixp dnum name inum isdir ms.
(* hint proof tokens: 101 *)
Proof.
    unfold link'.
    hoare.

    msalloc_eq. subst_cache.
    or_r. cancel; eauto.
    cbn in *; subst_cache.
    cbv [fst snd upd].
    rewrite DcacheDefs.MapFacts.add_o.
    repeat destruct string_dec; (congruence || eauto).
  Unshelve.
    all : try exact Balloc.BALLOCC.Alloc.freelist0.
    all : eauto.
  Qed.
Hint Extern 0 ({{ _ }} Bind (link' _ _ _ _ _ _ _ _) _) => apply link'_ok : prog.
Theorem link_ok : forall lxp bxp ixp dnum name inum isdir ms,
    {< F Fi Fm m0 sm m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             rep_macro Fi Fm m bxp ixp dnum dmap ilist frees f ms sm *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:hm' RET:^(ms', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] *
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm')
        \/  ([[ r = OK tt ]] *
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             rep_macro Fi Fm m' bxp ixp dnum dmap' ilist' frees' f' ms' sm *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} link lxp bxp ixp dnum name inum isdir ms.
(* hint proof tokens: 26 *)
Proof.
    unfold link.
    hoare.
  Unshelve.
    all: eauto.
  Qed.
Hint Extern 1 ({{_}} Bind (unlink _ _ _ _ _) _) => apply unlink_ok : prog.
Hint Extern 1 ({{_}} Bind (link _ _ _ _ _ _ _ _) _) => apply link_ok : prog.
Hint Extern 1 ({{_}} Bind (readdir _ _ _ _) _) => apply readdir_ok : prog.
End CacheOneDir.
