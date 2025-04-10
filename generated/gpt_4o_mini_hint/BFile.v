Require Import Arith.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Lia.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Inode.
Require Import GenSepAuto.
Require Import DiskSet.
Require Import Errno.
Require Import Lock.
Require Import MSets.
Require Import FMapAVL.
Require Import FMapMem.
Require Import MapUtils.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import StringUtils.
Require Import Balloc.
Require Import SyncedMem.
Import ListNotations.
Set Implicit Arguments.
Module Dcache := FMapAVL.Make(String_as_OT).
Module DcacheDefs := MapDefs String_as_OT Dcache.
Definition Dcache_type := Dcache.t (addr * bool).
Module BFcache := AddrMap.Map.
Module AddrMap := AddrMap.
Definition BFcache_type := BFcache.t (Dcache_type * addr).
Module BFM := MapMem Nat_as_OT BFcache.
Import AddrMap.
Import AddrSet.
Definition DBlocks_type := Map.t (SS.t).
Module M := MapMem Nat_as_OT Map.
Module BFILE.
Record memstate := mk_memstate {
    MSAlloc : bool;         
    MSLL : LOG.memstate;    
    MSAllocC: (BALLOCC.BmapCacheType * BALLOCC.BmapCacheType);
    MSIAllocC : IAlloc.BmapCacheType;
    MSICache : INODE.IRec.Cache_type;
    MSCache : BFcache_type;
    MSDBlocks: DBlocks_type;
  }.
Definition ms_empty msll : memstate := mk_memstate
    true
    msll
    (BALLOCC.Alloc.freelist0, BALLOCC.Alloc.freelist0)
    IAlloc.Alloc.freelist0
    INODE.IRec.cache0
    (BFcache.empty _) (Map.empty _).
Definition MSinitial ms :=
    MSAlloc ms = true /\
    MSAllocC ms = (BALLOCC.Alloc.freelist0, BALLOCC.Alloc.freelist0) /\
    MSIAllocC ms = IAlloc.Alloc.freelist0 /\
    MSICache ms = INODE.IRec.cache0 /\
    MSCache ms = (BFcache.empty _) /\
    MSDBlocks ms = (Map.empty _).
Definition MSIAlloc ms :=
    IAlloc.mk_memstate (MSLL ms) (MSIAllocC ms).
Definition getlen lxp ixp inum fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms, n) <- INODE.getlen lxp ixp inum icache ms;
    Ret ^(mk_memstate al ms alc ialc icache cache dblocks, n).
Definition getattrs lxp ixp inum fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms, n) <- INODE.getattrs lxp ixp inum icache ms;
    Ret ^(mk_memstate al ms alc ialc icache cache dblocks, n).
Definition setattrs lxp ixp inum a fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms) <- INODE.setattrs lxp ixp inum a icache ms;
    Ret (mk_memstate al ms alc ialc icache cache dblocks).
Definition updattr lxp ixp inum kv fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms) <- INODE.updattr lxp ixp inum kv icache ms;
    Ret (mk_memstate al ms alc ialc icache cache dblocks).
Definition read lxp ixp inum off fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms, bn) <-INODE.getbnum lxp ixp inum off icache ms;
    let^ (ms, v) <- LOG.read lxp (# bn) ms;
    Ret ^(mk_memstate al ms alc ialc icache cache dblocks, v).
Definition get_dirty inum (dblocks : DBlocks_type) :=
    match Map.find inum dblocks with
    | None => SS.empty
    | Some l => l
    end.
Definition put_dirty inum bn (dblocks : DBlocks_type) :=
    let dirty := get_dirty inum dblocks in
    Map.add inum (SS.add bn dirty) dblocks.
Definition remove_dirty inum bn (dblocks : DBlocks_type) :=
    match Map.find inum dblocks with
    | None => dblocks
    | Some dirty =>
      let dirty' := SS.remove bn dirty in
      Map.add inum dirty' dblocks
    end.
Definition remove_dirty_vec inum bns (dblocks : DBlocks_type) :=
    match Map.find inum dblocks with
    | None => dblocks
    | Some dirty =>
      let dirty' := (fold_right SS.remove dirty bns) in
      Map.add inum dirty' dblocks
    end.
Definition clear_dirty inum (dblocks : DBlocks_type) :=
    Map.remove inum dblocks.
Definition write lxp ixp inum off v fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms, bn) <-INODE.getbnum lxp ixp inum off icache ms;
    ms <- LOG.write lxp (# bn) v ms;
    Ret (mk_memstate al ms alc ialc icache cache dblocks).
Definition dwrite lxp ixp inum off v fms :=

    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms, bn) <- INODE.getbnum lxp ixp inum off icache ms;
    ms <- LOG.dwrite lxp (# bn) v ms;
    let dblocks := put_dirty inum (# bn) dblocks in

    Ret (mk_memstate al ms alc ialc icache cache dblocks).
Definition datasync lxp (ixp : INODE.IRecSig.xparams) inum fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in

    let bns := (SS.elements (get_dirty inum dblocks)) in
    ms <- LOG.dsync_vecs lxp bns ms;
    let dblocks := clear_dirty inum dblocks in

    Ret (mk_memstate al ms alc ialc icache cache dblocks).
Definition sync lxp (ixp : INODE.IRecSig.xparams) fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    ms <- LOG.flushall lxp ms;
    Ret (mk_memstate (negb al) ms alc ialc icache cache dblocks).
Definition sync_noop lxp (ixp : INODE.IRecSig.xparams) fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    ms <- LOG.flushall_noop lxp ms;
    Ret (mk_memstate (negb al) ms alc ialc icache cache dblocks).
Definition pick_balloc A (a : A * A) (flag : bool) :=
    if flag then fst a else snd a.
Definition upd_balloc A (a : A * A) (new : A) (flag : bool) :=
    (if flag then new else fst a,
     if flag then snd a else new).
Theorem pick_upd_balloc_negb : forall A flag p (new : A),
    pick_balloc p flag = pick_balloc (upd_balloc p new (negb flag)) flag.
Proof.
(* original proof tokens: 18 *)
(* generated proof tokens: 16 *)

Proof.
  destruct flag; simpl; auto.
Qed.

Theorem pick_negb_upd_balloc : forall A flag p (new : A),
    pick_balloc p (negb flag) = pick_balloc (upd_balloc p new flag) (negb flag).
(* hint proof tokens: 18 *)
Proof.
    destruct flag, p; intros; reflexivity.
  Qed.
Theorem pick_upd_balloc_lift : forall A flag p (new : A),
    new = pick_balloc (upd_balloc p new flag) flag.
(* hint proof tokens: 18 *)
Proof.
    destruct flag, p; intros; reflexivity.
  Qed.
Definition grow lxp bxps ixp inum v fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms, len) <- INODE.getlen lxp ixp inum icache ms;
    If (lt_dec len INODE.NBlocks) {
      let^ (cms, r) <- BALLOCC.alloc lxp (pick_balloc bxps al) (BALLOCC.mk_memstate ms (pick_balloc alc al));
      match r with
      | None => Ret ^(mk_memstate al (BALLOCC.MSLog cms) (upd_balloc alc (BALLOCC.MSCache cms) al) ialc icache cache dblocks, Err ENOSPCBLOCK)
      | Some bn =>
           let^ (icache, cms, succ) <- INODE.grow lxp (pick_balloc bxps al) ixp inum bn icache cms;
           match succ with
           | Err e =>
             Ret ^(mk_memstate al (BALLOCC.MSLog cms) (upd_balloc alc (BALLOCC.MSCache cms) al) ialc icache cache dblocks, Err e)
           | OK _ =>
             ms <- LOG.write lxp bn v (BALLOCC.MSLog cms);
             let dblocks := put_dirty inum bn dblocks in
             Ret ^(mk_memstate al ms (upd_balloc alc (BALLOCC.MSCache cms) al) ialc icache cache dblocks, OK tt)
           end
      end
    } else {
      Ret ^(mk_memstate al ms alc ialc icache cache dblocks, Err EFBIG)
    }.
Definition shrink lxp bxps ixp inum nr fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms, bns) <- INODE.getallbnum lxp ixp inum icache ms;
    let l := map (@wordToNat _) (skipn ((length bns) - nr) bns) in
    let dblocks := remove_dirty_vec inum l dblocks in
    cms <- BALLOCC.freevec lxp (pick_balloc bxps (negb al)) l (BALLOCC.mk_memstate ms (pick_balloc alc (negb al)));
    let^ (icache, cms) <- INODE.shrink lxp (pick_balloc bxps (negb al)) ixp inum nr icache cms;
    Ret (mk_memstate al (BALLOCC.MSLog cms) (upd_balloc alc (BALLOCC.MSCache cms) (negb al)) ialc icache cache dblocks).
Definition shuffle_allocs lxp bxps ms cms :=
    let^ (ms, cms) <- ForN 1 <= i < (BmapNBlocks (fst bxps) * valulen / 2)
    Hashmap hm
    Ghost [ F Fm Fs crash m0 sm ]
    Loopvar [ ms cms ]
    Invariant
         exists m' frees,
         LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm *
         [[[ m' ::: (Fm * BALLOCC.rep (fst bxps) (fst frees) (BALLOCC.mk_memstate ms (fst cms))   *
                         BALLOCC.rep (snd bxps) (snd frees) (BALLOCC.mk_memstate ms (snd cms))) ]]] *
         [[ (Fs * BALLOCC.smrep (fst frees) * BALLOCC.smrep (snd frees))%pred sm ]] *
         [[ forall bn, bn < (BmapNBlocks (fst bxps)) * valulen /\ bn >= i
             -> In bn (fst frees) ]]
    OnCrash crash
    Begin
      fcms <- BALLOCC.steal lxp (fst bxps) i (BALLOCC.mk_memstate ms (fst cms));
      scms <- BALLOCC.free lxp (snd bxps) i (BALLOCC.mk_memstate (BALLOCC.MSLog fcms) (snd cms));
      Ret ^((BALLOCC.MSLog scms), ((BALLOCC.MSCache fcms), (BALLOCC.MSCache scms)))
    Rof ^(ms, cms);
    Ret ^(ms, cms).
Definition init lxp bxps bixp ixp ms :=
    fcms <- BALLOCC.init_nofree lxp (snd bxps) ms;
    scms <- BALLOCC.init lxp (fst bxps) (BALLOCC.MSLog fcms);
    ialc_ms <- IAlloc.init lxp bixp (BALLOCC.MSLog scms);
    ms <- INODE.init lxp ixp (IAlloc.Alloc.MSLog ialc_ms);
    let^ (ms, cms) <- shuffle_allocs lxp bxps ms (BALLOCC.MSCache scms, BALLOCC.MSCache fcms);
    Ret (mk_memstate true ms cms (IAlloc.MSCache ialc_ms) INODE.IRec.cache0 (BFcache.empty _) (Map.empty _)).
Definition recover ms :=
    Ret (mk_memstate true ms (BALLOCC.Alloc.freelist0, BALLOCC.Alloc.freelist0) IAlloc.Alloc.freelist0 INODE.IRec.cache0 (BFcache.empty _) (Map.empty _)).
Definition cache_get inum fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    Ret ^(mk_memstate al ms alc ialc icache cache dblocks, BFcache.find inum cache).
Definition cache_put inum dc fms :=
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    Ret (mk_memstate al ms alc ialc icache (BFcache.add inum dc cache) dblocks).
Definition attr := INODE.iattr.
Definition attr0 := INODE.iattr0.
Definition datatype := valuset.
Record bfile := mk_bfile {
    BFData : list datatype;
    BFAttr : attr;
    BFCache : option (Dcache_type * addr)
  }.
Definition bfile0 := mk_bfile nil attr0 None.
Definition freepred f := f = bfile0.
Definition smrep_single (dirty : SS.t) (i : INODE.inode) : @pred _ addr_eq_dec bool :=
    ( [[ SS.For_all (fun bn => In bn (map (@wordToNat _) (INODE.IBlocks i))) dirty ]] *
    listpred (fun bn => exists b, (# bn) |-> b  * [[ ~SS.In (# bn) dirty -> b = true ]]) (INODE.IBlocks i))%pred.
Definition smrep_single_helper dblocks i ino :=
    let dirty := match Map.find i dblocks with Some d => d | None => SS.empty end in
    smrep_single dirty ino.
Definition smrep frees (dirty : Map.t (SS.t)) (ilist : list INODE.inode) :=
    (BALLOCC.smrep (fst frees) * BALLOCC.smrep (snd frees) * arrayN (smrep_single_helper dirty) 0 ilist)%pred.
Definition file_match f i : @pred _ addr_eq_dec datatype :=
    (listmatch (fun v a => a |-> v ) (BFData f) (map (@wordToNat _) (INODE.IBlocks i)) *
     [[ BFAttr f = INODE.IAttr i ]])%pred.
Definition cache_ptsto inum (oc : option (Dcache_type * addr)) : @pred _ addr_eq_dec _ :=
    ( match oc with
      | None => emp
      | Some c => inum |-> c
      end )%pred.
Definition filter_cache (f : bfile ) :=
    match BFCache f with
    | Some v => Some (fst v)
    | None => None
    end.
Definition cache_rep mscache (flist : list bfile) (ilist : list INODE.inode) :=
     arrayN cache_ptsto 0 (map BFCache flist) (BFM.mm _ mscache).
Definition rep (bxps : balloc_xparams * balloc_xparams) sm ixp (flist : list bfile) ilist frees cms mscache icache dblocks :=
    (exists lms IFs,
     BALLOCC.rep (fst bxps) (fst frees) (BALLOCC.mk_memstate lms (fst cms)) *
     BALLOCC.rep (snd bxps) (snd frees) (BALLOCC.mk_memstate lms (snd cms)) *
     INODE.rep (fst bxps) IFs ixp ilist icache *
     listmatch file_match flist ilist *
     [[ locked (cache_rep mscache flist ilist) ]] *
     [[ BmapNBlocks (fst bxps) = BmapNBlocks (snd bxps) ]] *
     exists Fs, [[ (Fs * IFs * smrep frees dblocks ilist)%pred sm ]]
    )%pred.
Definition rep_length_pimpl : forall bxps sm ixp flist ilist frees allocc icache mscache dblocks,
    rep bxps sm ixp flist ilist frees allocc icache mscache dblocks =p=>
    (rep bxps sm ixp flist ilist frees allocc icache mscache dblocks *
     [[ length flist = ((INODE.IRecSig.RALen ixp) * INODE.IRecSig.items_per_val)%nat ]] *
     [[ length ilist = ((INODE.IRecSig.RALen ixp) * INODE.IRecSig.items_per_val)%nat ]])%pred.
Proof.
(* original proof tokens: 48 *)
intros.
repeat match goal with
| [ H : rep _ _ _ _ _ _ _ _ _ |- _ ] => 
    rewrite rep_length_pimpl in H
end.
(* No more tactics to try *)
Admitted.

Definition rep_alt (bxps : BALLOCC.Alloc.Alloc.BmpSig.xparams * BALLOCC.Alloc.Alloc.BmpSig.xparams)
                     sm ixp (flist : list bfile) ilist frees cms icache mscache msalloc dblocks :=
    (exists lms IFs,
      BALLOCC.rep (pick_balloc bxps msalloc) (pick_balloc frees msalloc) (BALLOCC.mk_memstate lms (pick_balloc cms msalloc)) *
     BALLOCC.rep (pick_balloc bxps (negb msalloc)) (pick_balloc frees (negb msalloc)) (BALLOCC.mk_memstate lms (pick_balloc cms (negb msalloc))) *
     INODE.rep (pick_balloc bxps msalloc) IFs ixp ilist icache *
     listmatch file_match flist ilist *
     [[ locked (cache_rep mscache flist ilist) ]] *
     [[ BmapNBlocks (pick_balloc bxps msalloc) = BmapNBlocks (pick_balloc bxps (negb msalloc)) ]] *
     exists Fs, [[ (Fs * IFs * smrep (pick_balloc frees (msalloc), pick_balloc frees (negb msalloc)) dblocks ilist)%pred sm ]]
    )%pred.
Theorem rep_alt_equiv : forall bxps sm ixp flist ilist frees mscache allocc icache msalloc dblocks,
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks <=p=> rep_alt bxps sm ixp flist ilist frees allocc icache mscache msalloc dblocks.
(* hint proof tokens: 100 *)
Proof.
    unfold rep, rep_alt; split; destruct msalloc; simpl.
    - cancel.
    - norml; unfold stars; simpl.
      rewrite INODE.rep_bxp_switch at 1 by eauto.
      cancel.
      unfold smrep. cancel.
    - cancel.
    - norml; unfold stars; simpl.
      rewrite INODE.rep_bxp_switch at 1 by eauto.
      cancel.
      unfold smrep. cancel.
  Qed.
Definition clear_cache bf := mk_bfile (BFData bf) (BFAttr bf) None.
Definition clear_caches bflist := map clear_cache bflist.
Theorem rep_clear_freelist : forall bxps sm ixp flist ilist frees allocc mscache icache dblocks,
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks =p=>
    rep bxps sm ixp flist ilist frees (BALLOCC.Alloc.freelist0, BALLOCC.Alloc.freelist0) mscache icache dblocks.
(* hint proof tokens: 45 *)
Proof.
    unfold rep; intros; cancel.
    rewrite <- BALLOCC.rep_clear_mscache_ok. cancel.
    rewrite <- BALLOCC.rep_clear_mscache_ok. cancel.
  Qed.
Theorem rep_clear_bfcache : forall bxps sm ixp flist ilist frees allocc mscache icache dblocks,
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks =p=>
    rep bxps sm ixp (clear_caches flist) ilist frees allocc (BFcache.empty _) icache dblocks.
(* hint proof tokens: 132 *)
Proof.
    unfold rep; intros; cancel.
    unfold clear_caches.
    rewrite listmatch_map_l.
    unfold file_match, clear_cache; simpl.
    reflexivity.

    rewrite locked_eq.
    unfold cache_rep, clear_caches, clear_cache.
    rewrite map_map; simpl.
    denote smrep as Hd. clear Hd.
    denote locked as Hl. clear Hl.
    generalize 0.
    induction flist; simpl; intros.
    apply BFM.mm_init.
    specialize (IHflist (S n)).
    pred_apply; cancel.
  Unshelve.
    exact unit.
  Qed.
Theorem rep_clear_icache: forall bxps sm ixp flist ilist frees allocc mscache icache dblocks,
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks =p=>
    rep bxps sm ixp flist ilist frees allocc mscache INODE.IRec.cache0 dblocks.
(* hint proof tokens: 26 *)
Proof.
    unfold BFILE.rep. cancel.
    apply INODE.rep_clear_cache.
    cancel.
  Qed.
Lemma smrep_init: forall n,
    emp <=p=> arrayN (smrep_single_helper (Map.empty _)) 0 (repeat INODE.inode0 n).
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Lemma smrep_single_helper_split_tail: forall inum ino ino' dblocks n,
    INODE.IBlocks ino' = firstn n (INODE.IBlocks ino) ->
    NoDup (map (@wordToNat addrlen) (INODE.IBlocks ino)) ->
    let removed := map (@wordToNat addrlen) (skipn n (INODE.IBlocks ino)) in
    smrep_single_helper dblocks inum ino =p=>
    smrep_single_helper (remove_dirty_vec inum removed dblocks) inum ino' *
    listpred (fun a => a |->?) removed.
Proof.
(* original proof tokens: 407 *)

(* No more tactics to try *)
Admitted.

Lemma smrep_single_helper_clear_dirty: forall inum ino dblocks,
    smrep_single_helper dblocks inum ino =p=>
    smrep_single_helper (clear_dirty inum dblocks) inum INODE.inode0 *
    listpred (fun a => a |->?) (map (@wordToNat addrlen) (INODE.IBlocks ino)).
Proof.
(* original proof tokens: 76 *)

(* No more tactics to try *)
Admitted.

Definition block_belong_to_file ilist bn inum off :=
    off < length (INODE.IBlocks (selN ilist inum INODE.inode0)) /\
    bn = # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0).
Definition block_is_unused freeblocks (bn : addr) := In bn freeblocks.
Definition block_is_unused_dec freeblocks (bn : addr) :
    { block_is_unused freeblocks bn } + { ~ block_is_unused freeblocks bn }
    := In_dec addr_eq_dec bn freeblocks.
Lemma block_is_unused_xor_belong_to_file : forall F Ftop fsxp sm files ilist free allocc mscache icache dblocks m flag bn inum off,
    (F * rep fsxp sm Ftop files ilist free allocc mscache icache dblocks)%pred m ->
    block_is_unused (pick_balloc free flag) bn ->
    block_belong_to_file ilist bn inum off ->
    False.
Proof.
(* original proof tokens: 517 *)

(* No more tactics to try *)
Admitted.

Definition ilist_safe ilist1 free1 ilist2 free2 :=
    incl free2 free1 /\
    forall inum off bn,
        block_belong_to_file ilist2 bn inum off ->
        (block_belong_to_file ilist1 bn inum off \/
         block_is_unused free1 bn).
Theorem ilist_safe_refl : forall i f,
    ilist_safe i f i f.
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 20 *)

intros. split; auto. 
apply incl_refl. 
Qed.

Local Hint Resolve ilist_safe_refl.
Theorem ilist_safe_trans : forall i1 f1 i2 f2 i3 f3,
    ilist_safe i1 f1 i2 f2 ->
    ilist_safe i2 f2 i3 f3 ->
    ilist_safe i1 f1 i3 f3.
(* hint proof tokens: 76 *)
Proof.
    unfold ilist_safe; intros.
    destruct H.
    destruct H0.
    split.
    - eapply incl_tran; eauto.
    - intros.
      specialize (H2 _ _ _ H3).
      destruct H2; eauto.
      right.
      unfold block_is_unused in *.
      eauto.
  Qed.
Theorem ilist_safe_upd_nil : forall ilist frees i off,
    INODE.IBlocks i = nil ->
    ilist_safe ilist frees (updN ilist off i) frees.
Proof.
(* original proof tokens: 111 *)

(* No more tactics to try *)
Admitted.

Lemma block_belong_to_file_inum_ok : forall ilist bn inum off,
    block_belong_to_file ilist bn inum off ->
    inum < length ilist.
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Lemma rep_used_block_eq_Some_helper : forall T (x y: T),
    Some x = Some y -> x = y.
(* hint proof tokens: 17 *)
Proof.
    intros.
    inversion H.
    auto.
  Qed.
Theorem rep_used_block_eq : forall F bxps sm ixp flist ilist m bn inum off frees allocc mscache icache dblocks,
    (F * rep bxps sm ixp flist ilist frees allocc mscache icache dblocks)%pred (list2nmem m) ->
    block_belong_to_file ilist bn inum off ->
    selN (BFData (selN flist inum bfile0)) off ($0, nil) = selN m bn ($0, nil).
(* hint proof tokens: 321 *)
Proof.
    unfold rep; intros.
    destruct_lift H.
    rewrite listmatch_length_pimpl in H; destruct_lift H.
    rewrite listmatch_extract with (i := inum) in H.
    2: substl (length flist); eapply block_belong_to_file_inum_ok; eauto.

    assert (inum < length ilist) by ( eapply block_belong_to_file_inum_ok; eauto ).
    assert (inum < length flist) by ( substl (length flist); eauto ).

    denote block_belong_to_file as Hx; assert (Hy := Hx).
    unfold block_belong_to_file in Hy; intuition.
    unfold file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFData _) in H; destruct_lift H.
    denote! (length _ = _) as Heq.
    rewrite listmatch_extract with (i := off) (a := BFData _) in H.
    2: rewrite Heq; rewrite map_length; eauto.

    erewrite selN_map in H; eauto.
    eapply rep_used_block_eq_Some_helper.
    apply eq_sym.
    rewrite <- list2nmem_sel_inb.

    eapply ptsto_valid.
    pred_apply.
    eassign (natToWord addrlen O).
    cancel.

    eapply list2nmem_inbound.
    pred_apply.
    cancel.

  Unshelve.
    all: eauto.
  Qed.
Lemma smrep_single_helper_add_oob: forall inum dirty dblocks st ino,
    inum <> st ->
    smrep_single_helper (Map.add inum dirty dblocks) st ino <=p=>
    smrep_single_helper dblocks st ino.
(* hint proof tokens: 36 *)
Proof.
    unfold smrep_single_helper.
    unfold put_dirty.
    intros.
    rewrite MapFacts.add_neq_o by auto.
    auto.
  Qed.
Lemma smrep_single_helper_remove_oob: forall inum dblocks st ino,
    inum <> st ->
    smrep_single_helper (Map.remove inum dblocks) st ino <=p=>
    smrep_single_helper dblocks st ino.
(* hint proof tokens: 36 *)
Proof.
    unfold smrep_single_helper.
    unfold put_dirty.
    intros.
    rewrite MapFacts.remove_neq_o by auto.
    auto.
  Qed.
Lemma arrayN_smrep_single_helper_add_oob: forall ilist st inum dirty dblocks,
    inum < st \/ inum >= st + length ilist ->
    arrayN (smrep_single_helper (Map.add inum dirty dblocks)) st ilist <=p=>
    arrayN (smrep_single_helper dblocks) st ilist.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_smrep_single_helper_remove_oob: forall ilist st inum dblocks,
    inum < st \/ inum >= st + length ilist ->
    arrayN (smrep_single_helper (Map.remove inum dblocks)) st ilist <=p=>
    arrayN (smrep_single_helper dblocks) st ilist.
(* hint proof tokens: 45 *)
Proof.
    induction ilist; cbn.
    split; cancel.
    intros.
    rewrite smrep_single_helper_remove_oob by lia.
    rewrite IHilist by lia.
    auto.
  Qed.
Lemma arrayN_ex_smrep_single_helper_add: forall ilist inum dirty dblocks,
    arrayN_ex (smrep_single_helper (Map.add inum dirty dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
(* hint proof tokens: 123 *)
Proof.
    unfold arrayN_ex.
    intros.
    destruct (lt_dec inum (length ilist)).
    - rewrite arrayN_smrep_single_helper_add_oob.
      rewrite arrayN_smrep_single_helper_add_oob.
      auto.
      autorewrite with core. lia.
      rewrite firstn_length_l; lia.
    - rewrite skipn_oob by lia.
      rewrite firstn_oob by lia.
      rewrite arrayN_smrep_single_helper_add_oob by lia.
      rewrite arrayN_smrep_single_helper_add_oob by lia.
      auto.
  Qed.
Lemma arrayN_ex_smrep_single_helper_remove: forall ilist inum dblocks,
    arrayN_ex (smrep_single_helper (Map.remove inum dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
Proof.
(* original proof tokens: 123 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_ex_smrep_single_helper_put_dirty: forall ilist inum bn dblocks,
    arrayN_ex (smrep_single_helper (put_dirty inum bn dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
(* hint proof tokens: 24 *)
Proof.
    unfold put_dirty.
    auto using arrayN_ex_smrep_single_helper_add.
  Qed.
Lemma arrayN_ex_smrep_single_helper_remove_dirty_vec: forall ilist inum bn dblocks,
    arrayN_ex (smrep_single_helper (remove_dirty_vec inum bn dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_ex_smrep_single_helper_clear_dirty: forall ilist inum dblocks,
    arrayN_ex (smrep_single_helper (clear_dirty inum dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma selN_NoDup_notin_firstn: forall T (l : list T) i x d,
    i < length l ->
    NoDup l ->
    selN l i d = x ->
    ~In x (firstn i l).
(* hint proof tokens: 69 *)
Proof.
    induction l; cbn; intros.
    lia.
    subst.
    destruct i; cbn.
    auto.
    inversion H0; subst.
    intuition subst.
    eapply H3.
    eapply in_selN; lia.
    eapply IHl; eauto; lia.
  Qed.
Lemma selN_NoDup_notin_skipn: forall T (l : list T) i x d,
    i < length l ->
    NoDup l ->
    selN l i d = x ->
    ~In x (skipn (S i) l).
(* hint proof tokens: 54 *)
Proof.
    induction l; cbn; intros.
    lia.
    subst.
    inversion H0; subst.
    destruct i; cbn.
    auto.
    intuition subst.
    eapply IHl; eauto; lia.
  Qed.
Lemma selN_NoDup_notin_removeN: forall T (l : list T) i x d,
    i < length l ->
    selN l i d = x ->
    NoDup l ->
    ~In x (removeN l i).
(* hint proof tokens: 55 *)
Proof.
    intros.
    unfold removeN.
    rewrite in_app_iff.
    intuition.
    eapply selN_NoDup_notin_firstn; eauto.
    eapply selN_NoDup_notin_skipn; eauto.
  Qed.
Lemma smrep_single_add: forall dirty ino bn,
    In bn (INODE.IBlocks ino) ->
    smrep_single dirty ino =p=> smrep_single (SS.add #bn dirty) ino.
Proof.
(* original proof tokens: 140 *)

(* No more tactics to try *)
Admitted.

Lemma smrep_single_helper_put_dirty: forall inum bn dblocks ino,
    In bn (INODE.IBlocks ino) ->
    smrep_single_helper dblocks inum ino =p=>
    smrep_single_helper (put_dirty inum #bn dblocks) inum ino.
(* hint proof tokens: 46 *)
Proof.
    unfold smrep_single_helper.
    unfold put_dirty.
    intros.
    rewrite MapFacts.add_eq_o by auto.
    unfold get_dirty.
    apply smrep_single_add. auto.
  Qed.
Lemma smrep_upd: forall frees dblocks ilist inum bn,
    goodSize addrlen bn ->
    In $bn (INODE.IBlocks (selN ilist inum INODE.inode0)) ->
    inum < length ilist ->
    smrep frees dblocks ilist =p=> smrep frees (put_dirty inum bn dblocks) ilist.
Proof.
(* original proof tokens: 94 *)

(* No more tactics to try *)
Admitted.

Lemma smrep_single_add_new: forall dirty ino ino' bn b,
    INODE.IBlocks ino' = INODE.IBlocks ino ++ [bn] ->
    #bn |->b * smrep_single dirty ino =p=> smrep_single (SS.add #bn dirty) ino'.
(* hint proof tokens: 123 *)
Proof.
    unfold smrep_single.
    cancel.
    rewrite H.
    rewrite listpred_app; cbn.
    cancel.
    apply listpred_pimpl_replace.
    intros.
    eapply in_selN_exists in H1; deex.
    cancel.
    rewrite H.
    unfold SS.For_all in *.
    intros x; intros.
    rewrite map_app.
    apply in_or_app.
    rewrite SS.add_spec in *.
    intuition. subst.
    right.
    cbn; auto.
  Unshelve.
    all: apply wzero.
  Qed.
Lemma smrep_single_helper_add_dirty: forall inum bn dblocks ino ino' b,
    INODE.IBlocks ino' = INODE.IBlocks ino ++ [bn] ->
    #bn |-> b * smrep_single_helper dblocks inum ino =p=>
    smrep_single_helper (put_dirty inum #bn dblocks) inum ino'.
Proof.
(* original proof tokens: 48 *)
(* generated proof tokens: 42 *)

unfold smrep_single_helper, put_dirty.
intros.
rewrite MapFacts.add_eq_o; auto.
unfold get_dirty.
apply smrep_single_add_new; auto.
Qed.

Lemma smrep_upd_add: forall frees dblocks ilist ilist' ino' inum bn b,
    goodSize addrlen bn ->
    inum < length ilist ->
    let ino := (selN ilist inum INODE.inode0) in
    ilist' = updN ilist inum ino' ->
    INODE.IBlocks ino' = INODE.IBlocks ino ++ [$bn] ->
    bn |-> b * smrep frees dblocks ilist =p=> smrep frees (put_dirty inum bn dblocks) ilist'.
Proof.
(* original proof tokens: 114 *)

(* No more tactics to try *)
Admitted.

Lemma smrep_upd_keep_blocks :
    forall frees dblocks ilist inum i' def,
    INODE.IBlocks (selN ilist inum def) = INODE.IBlocks i' ->
    smrep frees dblocks ilist =p=> smrep frees dblocks (updN ilist inum i').
(* hint proof tokens: 92 *)
Proof.
    unfold smrep.
    intros.
    cancel.
    destruct (lt_dec inum (length ilist)).
    2: rewrite updN_oob by lia; cancel.

    rewrite arrayN_except_upd by auto.
    rewrite arrayN_except with (i := inum) by auto.
    cancel.

    unfold smrep_single_helper, smrep_single.
    rewrite <- H.
    reflexivity.
  Qed.
Lemma smrep_single_helper_split_dirty: forall dblocks inum ino ino' off,
    INODE.IBlocks ino' = removeN (INODE.IBlocks ino) off ->
    off < length (INODE.IBlocks ino) ->
    NoDup (map (@wordToNat addrlen) (INODE.IBlocks ino)) ->
    let bn := #(selN (INODE.IBlocks ino) off $0) in
    smrep_single_helper dblocks inum ino =p=> smrep_single_helper (remove_dirty inum bn dblocks) inum ino' * bn |->?.
(* hint proof tokens: 337 *)
Proof.
    cbn; intros.
    unfold smrep_single_helper, remove_dirty.
    destruct Map.find eqn:Hfind.
    rewrite M.find_add_eq.
    unfold smrep_single.
    rewrite H.
    rewrite listpred_isolate with (i := off) by auto. cancel.
    rewrite listpred_pimpl_replace.
    solve [apply sep_star_comm | apply pimpl_refl].
    unfold SS.For_all in *.
    cancel.
    denote In as Hi.
    denote SS.remove as Hr.
    rewrite SS.remove_spec in Hr.
    denote (_ = true) as Hs. apply Hs.
    intros Ha.
    apply Hr. intuition auto.
    denote selN as Hb.
    denote NoDup as Hd.
    eapply selN_NoDup_notin_removeN in Hd; try reflexivity.
    rewrite removeN_map_comm in *.
    erewrite selN_map in Hd by eauto.
    eapply in_map in Hi.
    rewrite <- Hb in *.
    eauto.
    autorewrite with lists; auto.
    unfold SS.For_all in *.
    intros.
    rewrite SS.remove_spec in *.
    intuition.
    rewrite <- removeN_map_comm.
    eapply in_removeN_neq; eauto.
    erewrite selN_map; eauto.
    rewrite Hfind.
    unfold smrep_single, SS.For_all.
    rewrite H.
    rewrite listpred_isolate with (i := off) by auto.
    cancel.
    rewrite SetFacts.empty_iff in *.
    intuition.
  Unshelve.
    all: easy.
  Qed.
Lemma smrep_single_helper_return_dirty: forall dblocks inum ino ino' off b,
    INODE.IBlocks ino' = removeN (INODE.IBlocks ino) off ->
    off < length (INODE.IBlocks ino) ->
    let bn := #(selN (INODE.IBlocks ino) off $0) in
    bn |-> b * smrep_single_helper dblocks inum ino' =p=> smrep_single_helper (put_dirty inum bn dblocks) inum ino.
Proof.
(* original proof tokens: 258 *)

(* No more tactics to try *)
Admitted.

Lemma smrep_single_helper_put_remove_dirty: forall dblocks inum bn ino,
    smrep_single_helper (put_dirty inum bn (remove_dirty inum bn dblocks)) inum ino =p=>
    smrep_single_helper (put_dirty inum bn dblocks) inum ino.
(* hint proof tokens: 132 *)
Proof.
    intros.
    unfold put_dirty, remove_dirty, get_dirty, smrep_single_helper, smrep_single, SS.For_all.
    repeat rewrite M.find_add_eq.
    destruct (Map.find inum dblocks) eqn:?.
    repeat rewrite M.find_add_eq.
    cancel.
    apply listpred_pimpl_replace. cancel.
    rewrite SS.add_spec in *.
    rewrite SS.remove_spec in *.
    intuition.
    apply H0.
    rewrite SS.add_spec, SS.remove_spec in *.
    destruct (addr_eq_dec x bn); intuition.
    rewrite Heqo.
    cancel.
  Qed.
Lemma smrep_single_helper_to_listmatch: forall dblocks inum ino,
    smrep_single_helper dblocks inum ino =p=> exists l,
      listmatch (fun b a => a |-> b) l (map (@wordToNat addrlen) (INODE.IBlocks ino)) *
      [[ forall i, i < length (INODE.IBlocks ino) -> SS.In #(selN (INODE.IBlocks ino) i $0) (get_dirty inum dblocks) \/
        selN l i false = true ]] * [[ incl (SS.elements (get_dirty inum dblocks)) (map (wordToNat (sz:=addrlen)) (INODE.IBlocks ino)) ]].
(* hint proof tokens: 277 *)
Proof.
    intros.
    unfold smrep_single_helper, smrep_single.
    norml.
    cbv [stars fold_left pred_fold_left].
    rewrite listpred_exis_listmatch.
    norml.
    cbv [stars fold_left pred_fold_left].
    erewrite listmatch_lift with (P := fun x y => (~SS.In #x (get_dirty inum dblocks)) -> y = true).
    rewrite listmatch_length_pimpl.
    cancel.
    rewrite listmatch_map_r.
    rewrite listmatch_sym. apply pimpl_refl.
    denote Forall2 as Hf.
    eapply forall2_forall in Hf.
    rewrite Forall_forall in Hf.
    rewrite <- SS.mem_spec.
    destruct SS.mem eqn:Hm; auto.
    rewrite <- SetFacts.not_mem_iff in *.
    right.
    specialize (Hf (selN (INODE.IBlocks ino) i $0, selN b i false)).
    eapply Hf; auto.
    rewrite <- selN_combine by auto.
    apply in_selN.
    rewrite combine_length_eq; lia.
    unfold incl.
    denote SS.For_all as Hs.
    intros a.
    rewrite AddrSetFacts.elements_spec1.
    auto.
    split; cancel.
  Qed.
Theorem rep_safe_used: forall F bxps sm ixp flist ilist m bn inum off frees allocc mscache icache dblocks v,
    (F * rep bxps sm ixp flist ilist frees allocc mscache icache dblocks)%pred (list2nmem m) ->
    block_belong_to_file ilist bn inum off ->
    let f := selN flist inum bfile0 in
    let f' := mk_bfile (updN (BFData f) off v) (BFAttr f) (BFCache f) in
    let flist' := updN flist inum f' in
    (F * rep bxps sm ixp flist' ilist frees allocc mscache icache dblocks)%pred (list2nmem (updN m bn v)).
Proof.
(* original proof tokens: 607 *)

(* No more tactics to try *)
Admitted.

Theorem rep_safe_unused: forall F bxps sm ixp flist ilist m frees allocc mscache icache dblocks bn v flag,
    (F * rep bxps sm ixp flist ilist frees allocc mscache icache dblocks)%pred (list2nmem m) ->
    block_is_unused (pick_balloc frees flag) bn ->
    (F * rep bxps sm ixp flist ilist frees allocc mscache icache dblocks)%pred (list2nmem (updN m bn v)).
Proof.
(* original proof tokens: 660 *)

(* No more tactics to try *)
Admitted.

Theorem block_belong_to_file_bfdata_length : forall bxp sm ixp flist ilist frees allocc mscache icache dblocks m F inum off bn,
    (F * rep bxp sm ixp flist ilist frees allocc mscache icache dblocks)%pred m ->
    block_belong_to_file ilist bn inum off ->
    off < length (BFData (selN flist inum BFILE.bfile0)).
Proof.
(* original proof tokens: 140 *)
intros.
unfold rep in H.
destruct_lift H.
rewrite listmatch_length_pimpl in H.
destruct_lift H.
rewrite listmatch_extract with (i := inum) in H.
2: substl (length flist); eauto.
assert (inum < length ilist) by (eapply block_belong_to_file_inum_ok; eauto).
assert (inum < length flist) by (substl (length flist); eauto).
eapply block_belong_to_file_inum_ok in H0; eauto.
(* No more tactics to try *)
Admitted.

Definition synced_file f := mk_bfile (synced_list (map fst (BFData f))) (BFAttr f) (BFCache f).
Lemma add_nonzero_exfalso_helper2 : forall a b,
    a * valulen + b = 0 -> a <> 0 -> False.
(* hint proof tokens: 75 *)
Proof.
    intros.
    destruct a; auto.
    rewrite Nat.mul_succ_l in H.
    assert (0 < a * valulen + valulen + b).
    apply Nat.add_pos_l.
    apply Nat.add_pos_r.
    rewrite valulen_is; apply Nat.ltb_lt; compute; reflexivity.
    lia.
  Qed.
Lemma file_match_init_ok : forall n,
    emp =p=> listmatch file_match (repeat bfile0 n) (repeat INODE.inode0 n).
(* hint proof tokens: 44 *)
Proof.
    induction n; simpl; intros.
    unfold listmatch; cancel.
    rewrite IHn.
    unfold listmatch; cancel.
    unfold file_match, listmatch; cancel.
  Qed.
Lemma file_match_no_dup: forall ilist flist F inum m,
    (F * listmatch file_match flist ilist)%pred m ->
    NoDup (map (@wordToNat addrlen) (INODE.IBlocks (selN ilist inum INODE.inode0))).
Proof.
(* original proof tokens: 139 *)

(* No more tactics to try *)
Admitted.

Lemma file_match_length: forall F flist ilist inum di df m,
    (F * listmatch file_match flist ilist)%pred m ->
    inum < length flist -> inum < length ilist ->
    length (INODE.IBlocks (selN ilist inum di)) = length (BFData (selN flist inum df)).
Proof.
(* original proof tokens: 74 *)

(* No more tactics to try *)
Admitted.

Lemma odd_nonzero : forall n,
    Nat.odd n = true -> n <> 0.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve odd_nonzero.
Definition mscs_same_except_log mscs1 mscs2 :=
    (MSAlloc mscs1 = MSAlloc mscs2) /\
    (MSAllocC mscs1 = MSAllocC mscs2) /\
    (MSIAllocC mscs1 = MSIAllocC mscs2) /\
    (MSICache mscs1 = MSICache mscs2) /\
    (MSCache mscs1 = MSCache mscs2) /\
    (MSDBlocks mscs1 = MSDBlocks mscs2).
Lemma mscs_same_except_log_comm : forall mscs1 mscs2,
    mscs_same_except_log mscs1 mscs2 ->
    mscs_same_except_log mscs2 mscs1.
(* hint proof tokens: 11 *)
Proof.
    firstorder.
  Qed.
Lemma mscs_same_except_log_refl : forall mscs,
    mscs_same_except_log mscs mscs.
(* hint proof tokens: 11 *)
Proof.
    firstorder.
  Qed.
Ltac destruct_ands :=
    repeat match goal with
    | [ H: _ /\ _ |- _ ] => destruct H
    end.
Ltac msalloc_eq :=
    repeat match goal with
    | [ H: mscs_same_except_log _ _ |- _ ] =>
      unfold BFILE.mscs_same_except_log in H; destruct_ands
    | [ H: MSAlloc _ = MSAlloc _ |- _ ] => rewrite H in *; clear H
    | [ H: MSAllocC _ = MSAllocC _ |- _ ] => rewrite H in *; clear H
    | [ H: MSIAllocC _ = MSIAllocC _ |- _ ] => rewrite H in *; clear H
    | [ H: MSCache _ = MSCache _ |- _ ] => rewrite H in *; clear H
    | [ H: MSICache _ = MSICache _ |- _ ] => rewrite H in *; clear H
    | [ H: MSDBlocks _ = MSDBlocks _ |- _ ] => rewrite H in *; clear H
    end.
Fact resolve_selN_bfile0 : forall l i d,
    d = bfile0 -> selN l i d = selN l i bfile0.
(* hint proof tokens: 14 *)
Proof.
    intros; subst; auto.
  Qed.
Fact resolve_selN_vs0 : forall l i (d : valuset),
    d = ($0, nil) -> selN l i d = selN l i ($0, nil).
(* hint proof tokens: 14 *)
Proof.
    intros; subst; auto.
  Qed.
Hint Rewrite resolve_selN_bfile0 using reflexivity : defaults.
Hint Rewrite resolve_selN_vs0 using reflexivity : defaults.
Lemma bfcache_emp: forall ilist flist,
    Forall (fun f => BFCache f = None) flist ->
    locked (cache_rep (BFcache.empty (Dcache_type * addr)) flist ilist).
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Lemma bfcache_init : forall len ilist,
    locked (cache_rep (BFcache.empty _) (repeat bfile0 len) ilist).
(* hint proof tokens: 22 *)
Proof.
    intros.
    auto using bfcache_emp, Forall_repeat.
  Qed.
Lemma bfcache_upd : forall mscache inum flist ilist F f d a,
    locked (cache_rep mscache flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep mscache (updN flist inum {| BFData := d; BFAttr := a; BFCache := BFCache f |}) ilist).
(* hint proof tokens: 89 *)
Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    rewrite map_updN; simpl.
    eapply list2nmem_sel in H0 as H0'; rewrite H0'.
    erewrite selN_eq_updN_eq; eauto.
    erewrite selN_map; eauto.
    simplen.
  Unshelve.
    exact None.
  Qed.
Lemma cache_ptsto_none'' : forall l start m idx,
    arrayN cache_ptsto start l m ->
    idx < start ->
    m idx = None.
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Lemma cache_ptsto_none' : forall l start m idx def,
    arrayN cache_ptsto start l m ->
    idx < length l ->
    selN l idx def = None ->
    m (start + idx) = None.
(* hint proof tokens: 122 *)
Proof.
    induction l; intros; eauto.
    simpl in H.
    eapply sep_star_none; eauto; intros.
    destruct a; simpl in *.
    eapply ptsto_none; [ | eauto ].
    destruct idx; try lia; try congruence.
    eauto.
    destruct idx.
    eapply cache_ptsto_none''; eauto; lia.
    replace (start + S idx) with (S start + idx) by lia.
    eapply IHl; eauto.
    simpl in *; lia.
  Qed.
Lemma cache_ptsto_none : forall l m idx def,
    arrayN cache_ptsto 0 l m ->
    idx < length l ->
    selN l idx def = None ->
    m idx = None.
(* hint proof tokens: 35 *)
Proof.
    intros.
    replace (idx) with (0 + idx) by lia.
    eapply cache_ptsto_none'; eauto.
  Qed.
Lemma cache_ptsto_none_find : forall l c idx def,
    arrayN cache_ptsto 0 l (BFM.mm _ c) ->
    idx < length l ->
    selN l idx def = None ->
    BFcache.find idx c = None.
(* hint proof tokens: 37 *)
Proof.
    intros.
    assert (BFM.mm _ c idx = None).
    eapply cache_ptsto_none; eauto.
    eauto.
  Qed.
Lemma bfcache_find : forall c flist ilist inum f F,
    locked (cache_rep c flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    BFcache.find inum c = BFCache f.
(* hint proof tokens: 175 *)
Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    eapply list2nmem_sel in H0 as H0'.
    case_eq (BFCache f); intros.
    - eapply arrayN_isolate with (i := inum) in H; [ | simplen ].
      unfold cache_ptsto at 2 in H. simpl in H.
      erewrite selN_map in H by simplen. rewrite <- H0' in H. rewrite H1 in H.
      eapply BFM.mm_find; pred_apply; cancel.
    - eapply cache_ptsto_none_find; eauto.
      simplen.
      erewrite selN_map by simplen.
      rewrite <- H0'.
      eauto.
  Unshelve.
    all: exact None.
  Qed.
Lemma bfcache_put : forall msc flist ilist inum c f F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep (BFcache.add inum c msc)
                      (updN flist inum {| BFData := BFData f; BFAttr := BFAttr f; BFCache := Some c |})
                      ilist).
Proof.
(* original proof tokens: 381 *)

(* No more tactics to try *)
Admitted.

Lemma bfcache_remove' : forall msc flist ilist inum f d a F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep (BFcache.remove inum msc)
                      (updN flist inum {| BFData := d; BFAttr := a; BFCache := None |})
                      ilist).
Proof.
(* original proof tokens: 385 *)

(* No more tactics to try *)
Admitted.

Lemma bfcache_remove : forall msc flist ilist inum f F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    BFData f = nil ->
    BFAttr f = attr0 ->
    locked (cache_rep (BFcache.remove inum msc) (updN flist inum bfile0) ilist).
(* hint proof tokens: 24 *)
Proof.
    intros.
    eapply bfcache_remove' in H; eauto.
  Qed.
Lemma rep_bfcache_remove : forall bxps sm ixp flist ilist frees allocc mscache icache dblocks inum f F,
    (F * inum |-> f)%pred (list2nmem flist) ->
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks =p=>
    rep bxps sm ixp (updN flist inum {| BFData := BFData f; BFAttr := BFAttr f; BFCache := None |}) ilist frees allocc
      (BFcache.remove inum mscache) icache dblocks.
Proof.
(* original proof tokens: 130 *)

(* No more tactics to try *)
Admitted.

Hint Resolve bfcache_init bfcache_upd.
Ltac assignms :=
    match goal with
    [ fms : memstate |- LOG.rep _ _ _ ?ms _ _ =p=> LOG.rep _ _ _ (MSLL ?e) _ _ ] =>
      is_evar e; eassign (mk_memstate (MSAlloc fms) ms (MSAllocC fms) (MSIAllocC fms) (MSICache fms) (MSCache fms) (MSDBlocks fms)); simpl; eauto
    end.
Local Hint Extern 1 (LOG.rep _ _ _ ?ms _ _ =p=> LOG.rep _ _ _ (MSLL ?e) _ _ ) => assignms.
Local Hint Extern 0 (okToUnify (smrep_single_helper _ _ _) (smrep_single_helper _ _ _)) => constructor : okToUnify.
Local Opaque Nat.div.
Theorem shuffle_allocs_ok : forall lxp bxps ms cms,
    {< F Fm Fs m0 sm m frees,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * BALLOCC.rep (fst bxps) (fst frees) (BALLOCC.mk_memstate ms (fst cms)) *
                           BALLOCC.rep (snd bxps) (snd frees) (BALLOCC.mk_memstate ms (snd cms))) ]]] *
           [[ (Fs * BALLOCC.smrep (fst frees) * BALLOCC.smrep (snd frees))%pred sm ]] *
           [[ forall bn, bn < (BmapNBlocks (fst bxps)) * valulen -> In bn (fst frees) ]] *
           [[ BmapNBlocks (fst bxps) = BmapNBlocks (snd bxps) ]]
    POST:hm' RET:^(ms',cms')  exists m' frees',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm hm' *
           [[[ m' ::: (Fm * BALLOCC.rep (fst bxps) (fst frees') (BALLOCC.mk_memstate ms' (fst cms')) *
                            BALLOCC.rep (snd bxps) (snd frees') (BALLOCC.mk_memstate ms' (snd cms'))) ]]] *
           [[ (Fs * BALLOCC.smrep (fst frees') * BALLOCC.smrep (snd frees'))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} shuffle_allocs lxp bxps ms cms.
(* hint proof tokens: 265 *)
Proof.
    unfold shuffle_allocs.
    intros.
    eapply pimpl_ok2.
    ProgMonad.monad_simpl.
    eapply forN_ok'.
    cancel.
    step.
    unfold BALLOCC.bn_valid; split; auto. lia.
    denote (lt m1) as Hm.
    rewrite Nat.sub_add in Hm by lia.
    apply Rounding.lt_div_mul_lt in Hm; lia.
    denote In as Hb.
    eapply Hb.
    unfold BALLOCC.bn_valid; split; auto.
    denote (lt m1) as Hm.
    rewrite Nat.sub_add in Hm by lia.
    apply Rounding.lt_div_mul_lt in Hm; lia.
    step.
    unfold BALLOCC.bn_valid; split; auto. lia.
    substl (BmapNBlocks bxps_2); auto.
    denote (lt m1) as Hm.
    rewrite Nat.sub_add in Hm by lia.
    apply Rounding.lt_div_mul_lt in Hm; lia.
    step.
    apply remove_other_In.
    lia.
    intuition.
    step.
    cancel.
    eapply LOG.intact_hashmap_subset.
    eauto.
    Unshelve. exact tt.
  Qed.
Hint Extern 1 ({{_}} Bind (shuffle_allocs _ _ _ _) _) => apply shuffle_allocs_ok : prog.
Local Hint Resolve INODE.IRec.Defs.items_per_val_gt_0 INODE.IRec.Defs.items_per_val_not_0 valulen_gt_0.
Theorem init_ok : forall lxp bxps ibxp ixp ms,
    {< F Fm Fs m0 sm m l sl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 l) ]]] *
           [[ (Fs * arrayN (@ptsto _ _ _) 0 sl)%pred sm ]] *
           [[ length sl = length l ]] *
           [[ let data_bitmaps := (BmapNBlocks (fst bxps)) in
              let inode_bitmaps := (IAlloc.Sig.BMPLen ibxp) in
              let data_blocks := (data_bitmaps * valulen)%nat in
              let inode_blocks := (inode_bitmaps * valulen / INODE.IRecSig.items_per_val)%nat in
              let inode_base := data_blocks in
              let balloc_base1 := inode_base + inode_blocks + inode_bitmaps in
              let balloc_base2 := balloc_base1 + data_bitmaps in
              length l = balloc_base2 + data_bitmaps /\
              BmapNBlocks (fst bxps) = BmapNBlocks (snd bxps) /\
              BmapStart (fst bxps) = balloc_base1 /\
              BmapStart (snd bxps) = balloc_base2 /\
              IAlloc.Sig.BMPStart ibxp = inode_base + inode_blocks /\
              IXStart ixp = inode_base /\ IXLen ixp = inode_blocks /\
              data_bitmaps <> 0 /\ inode_bitmaps <> 0 /\
              data_bitmaps <= valulen * valulen /\
             inode_bitmaps <= valulen * valulen
           ]]
    POST:hm' RET:ms'  exists m' n frees freeinodes freeinode_pred,
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxps sm ixp (repeat bfile0 n) (repeat INODE.inode0 n) frees (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms') *
                            @IAlloc.rep bfile freepred ibxp freeinodes freeinode_pred (MSIAlloc ms')) ]]] *
           [[ n = ((IXLen ixp) * INODE.IRecSig.items_per_val)%nat /\ n > 1 ]] *
           [[ forall dl, length dl = n ->
                         Forall freepred dl ->
                         arrayN (@ptsto _ _ _) 0 dl =p=> freeinode_pred ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} init lxp bxps ibxp ixp ms.
Proof.
(* original proof tokens: 872 *)

(* No more tactics to try *)
Admitted.

Theorem getlen_ok : forall lxp bxps ixp inum ms,
    {< F Fm Fi m0 sm m f flist ilist allocc frees,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxps sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           [[[ m ::: (Fm * rep bxps sm ixp flist ilist frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[ r = length (BFData f) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} getlen lxp ixp inum ms.
Proof.
(* original proof tokens: 97 *)
intros lxp bxps ixp inum ms T rx.
hoare.
constructor.
(* No more tactics to try *)
Admitted.

Theorem getattrs_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 sm m flist ilist allocc frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[ r = BFAttr f ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} getattrs lxp ixp inum ms.
(* hint proof tokens: 46 *)
Proof.
    unfold getattrs, rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite.
    subst; eauto.

    cancel.
    eauto.
  Qed.
Definition treeseq_ilist_safe inum ilist1 ilist2 :=
    (forall off bn,
        block_belong_to_file ilist1 bn inum off ->
        block_belong_to_file ilist2 bn inum off) /\
    (forall i def,
        inum <> i -> selN ilist1 i def = selN ilist2 i def).
Lemma treeseq_ilist_safe_refl : forall inum ilist,
    treeseq_ilist_safe inum ilist ilist.
Proof.
(* original proof tokens: 18 *)

(* No more tactics to try *)
Admitted.

Lemma treeseq_ilist_safe_trans : forall inum ilist0 ilist1 ilist2,
    treeseq_ilist_safe inum ilist0 ilist1 ->
    treeseq_ilist_safe inum ilist1 ilist2 ->
    treeseq_ilist_safe inum ilist0 ilist2.
Proof.
(* original proof tokens: 40 *)
unfold treeseq_ilist_safe; intuition.
(* No more tactics to try *)
Admitted.

Theorem setattrs_ok : forall lxp bxps ixp inum a ms,
    {< F Fm Ff m0 sm m flist ilist allocc frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxps sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Ff * inum |-> f) ]]] 
    POST:hm' RET:ms'  exists m' flist' f' ilist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxps sm ixp flist' ilist' frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Ff * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) a (BFCache f) ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]] *
           [[ MSAlloc ms = MSAlloc ms' /\
              let free := pick_balloc frees (MSAlloc ms') in
              ilist_safe ilist free ilist' free ]] *
           [[ treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} setattrs lxp ixp inum a ms.
Proof.
(* original proof tokens: 373 *)

(* No more tactics to try *)
Admitted.

Theorem updattr_ok : forall lxp bxps ixp inum kv ms,
    {< F Fm Fi m0 sm m flist ilist frees allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxps sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' ilist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxps sm ixp flist' ilist' frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) (INODE.iattr_upd (BFAttr f) kv) (BFCache f) ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAlloc ms = MSAlloc ms' /\
              let free := pick_balloc frees (MSAlloc ms') in
              ilist_safe ilist free ilist' free ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} updattr lxp ixp inum kv ms.
(* hint proof tokens: 287 *)
Proof.
    unfold updattr, rep.
    step.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    5: reflexivity.
    4: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try lia.
    unfold file_match; cancel.
    seprewrite.
    rewrite <- smrep_upd_keep_blocks.
    cancel.
    reflexivity.

    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
  Unshelve.
    all: eauto.
  Qed.
Theorem read_ok : forall lxp bxp ixp inum off ms,
    {< F Fm Fi Fd m0 sm m flist ilist frees allocc f vs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ r = fst vs /\ MSAlloc ms = MSAlloc ms' /\ MSCache ms = MSCache ms' /\ MSDBlocks ms = MSDBlocks ms' /\
              MSAllocC ms = MSAllocC ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} read lxp ixp inum off ms.
Proof.
(* original proof tokens: 260 *)

(* No more tactics to try *)
Admitted.

Theorem write_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd m0 sm m flist ilist frees allocc f vs0,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs0) ]]]
    POST:hm' RET:ms'  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxp sm ixp flist' ilist frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, nil)) (BFAttr f) (BFCache f) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} write lxp ixp inum off v ms.
(* hint proof tokens: 460 *)
Proof.
    unfold write, rep.
    prestep; norml.
    extract; seprewrite; subst.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx; safecancel.
    match goal with H: _ = length _ |- _ => rewrite <-H end.
    now eauto.
    sepauto.

    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_extract with (i := off) in Hx at 2; try lia.
    destruct_lift Hx; filldef.
    step.

    setoid_rewrite INODE.inode_rep_bn_nonzero_pimpl in H.
    destruct_lift H; denote (_ <> 0) as Hx; subst.
    eapply Hx; try eassumption; lia.
    rewrite listmatch_extract with (b := map _ _) (i := off) by lia.
    erewrite selN_map by lia; filldef.
    rewrite <- surjective_pairing.
    cancel.
    prestep. norm. cancel.
    intuition cbn.
    2: sepauto.
    2: cbn; sepauto.
    pred_apply. cancel.
    rewrite listmatch_isolate with (a := updN _ _ _).
    rewrite removeN_updN, selN_updN_eq by simplen.
    unfold file_match.
    cancel; eauto.
    rewrite listmatch_isolate with (a := updN _ _ _).
    rewrite removeN_updN, selN_updN_eq by simplen.
    erewrite selN_map by simplen.
    cancel.

    simplen.
    simplen.
    simplen.
    simplen.

    eauto.
    eauto.

    pimpl_crash; cancel; auto.
  Unshelve.
    all: try exact unit.
    all: intros; eauto.
    all: try solve [exact bfile0 | exact INODE.inode0].
    all: try split; auto using nil, tt.
  Qed.
Lemma grow_treeseq_ilist_safe: forall (ilist: list INODE.inode) ilist' inum a,
    inum < Datatypes.length ilist ->
    (arrayN_ex (ptsto (V:=INODE.inode)) ilist inum
     ✶ inum
       |-> {|
           INODE.IBlocks := INODE.IBlocks (selN ilist inum INODE.inode0) ++ [$ (a)];
           INODE.IAttr := INODE.IAttr (selN ilist inum INODE.inode0) |})%pred (list2nmem ilist') ->
    treeseq_ilist_safe inum ilist ilist'.
Proof.
(* original proof tokens: 136 *)

(* No more tactics to try *)
Admitted.

Theorem grow_ok : forall lxp bxp ixp inum v ms,
    {< F Fm Fi Fd m0 sm m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST:hm' RET:^(ms', r) [[ MSAlloc ms = MSAlloc ms' /\ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] * exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' \/
           [[ r = OK tt  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxp sm ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * (length (BFData f)) |-> (v, nil)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ [(v, nil)]) (BFAttr f) (BFCache f) ]] *
           [[ ilist_safe ilist  (pick_balloc frees  (MSAlloc ms'))
                         ilist' (pick_balloc frees' (MSAlloc ms')) ]] *
           [[ treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} grow lxp bxp ixp inum v ms.
(* hint proof tokens: 906 *)
Proof.
    unfold grow.
    prestep; norml; unfold stars; simpl.
    denote rep as Hr.
    rewrite rep_alt_equiv with (msalloc := MSAlloc ms) in Hr.
    unfold rep_alt, smrep in Hr; destruct_lift Hr.
    extract. seprewrite; subst.
    denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx. safecancel.
    sepauto.

    step.

    
    {
      step.
      safestep.
      sepauto.
      step.

      eapply BALLOCC.bn_valid_facts; eauto.
      step.

      or_r; safecancel.

      rewrite rep_alt_equiv with (msalloc := MSAlloc ms); unfold rep_alt.
      erewrite pick_upd_balloc_lift with (new := freelist') (flag := MSAlloc ms) (p := (frees_1, frees_2)) at 1.
      rewrite pick_negb_upd_balloc with (new := freelist') (flag := MSAlloc ms) at 1.
      unfold upd_balloc.

      match goal with a : BALLOCC.Alloc.memstate |- _ =>
        progress replace a with (BALLOCC.mk_memstate (BALLOCC.MSLog a) (BALLOCC.MSCache a)) at 1 by (destruct a; reflexivity);
        setoid_rewrite pick_upd_balloc_lift with (new := (BALLOCC.MSCache a) ) (flag := MSAlloc ms) at 1;
        rewrite pick_negb_upd_balloc with (new := (BALLOCC.MSCache a)) (flag := MSAlloc ms) at 1
      end.
      unfold upd_balloc.

      cancel.

      4: sepauto.
      5: eauto.
      seprewrite.
      rewrite listmatch_updN_removeN by simplen.
      unfold file_match; cancel.
      rewrite map_app; simpl.
      rewrite <- listmatch_app_tail.
      cancel.

      rewrite map_length; lia.
      rewrite wordToNat_natToWord_idempotent'; auto.
      eapply BALLOCC.bn_valid_goodSize; eauto.
      seprewrite.
      eapply bfcache_upd; eauto.
      rewrite <- smrep_upd_add; eauto.
      cancel.
      unfold smrep. destruct MSAlloc; cancel.
      eapply BALLOCC.bn_valid_goodSize; eauto. lia.
      sepauto.
      cbn; auto.
      apply list2nmem_app; eauto.

      2: { eapply grow_treeseq_ilist_safe. lia. eauto. }
      2: cancel.
      2: or_l; cancel.

      denote (list2nmem ilist') as Hilist'.
      assert (inum < length ilist) by simplen'.
      apply arrayN_except_upd in Hilist'; eauto.
      apply list2nmem_array_eq in Hilist'; subst.
      unfold ilist_safe; intuition.

      destruct (MSAlloc ms); simpl in *; eapply incl_tran; eauto; eapply incl_remove.

      destruct (addr_eq_dec inum inum0); subst.
      + unfold block_belong_to_file in *; intuition.
        all: erewrite selN_updN_eq in * by eauto; simpl in *; eauto.
        destruct (addr_eq_dec off (length (INODE.IBlocks (selN ilist inum0 INODE.inode0)))).
        * right.
          rewrite selN_last in * by auto.
          subst. rewrite wordToNat_natToWord_idempotent'. eauto.
          eapply BALLOCC.bn_valid_goodSize; eauto.
        * left.
          rewrite app_length in *; simpl in *.
          split. lia.
          subst. rewrite selN_app1 by lia. auto.
      + unfold block_belong_to_file in *; intuition.
        all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
    }

    step.
    cancel; eauto.

    Unshelve. all: easy.
  Qed.
Local Hint Extern 0 (okToUnify (listmatch _ _ ?a) (listmatch _ _ ?a)) => constructor : okToUnify.
Local Hint Extern 0 (okToUnify (listmatch _ ?a _) (listmatch _ ?a _)) => constructor : okToUnify.
Local Hint Extern 0 (okToUnify (listmatch _ _ (?f _ _)) (listmatch _ _ (?f _ _))) => constructor : okToUnify.
Local Hint Extern 0 (okToUnify (listmatch _ (?f _ _) _) (listmatch _ (?f _ _) _)) => constructor : okToUnify.
Theorem shrink_ok : forall lxp bxp ixp inum nr ms,
    {< F Fm Fi m0 sm m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' f' ilist' frees',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxp sm ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (firstn ((length (BFData f)) - nr) (BFData f)) (BFAttr f) (BFCache f) ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAlloc ms = MSAlloc ms' /\
              ilist_safe ilist  (pick_balloc frees  (MSAlloc ms'))
                         ilist' (pick_balloc frees' (MSAlloc ms')) ]] *
           [[ forall inum' def', inum' <> inum -> 
                selN ilist inum' def' = selN ilist' inum' def' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} shrink lxp bxp ixp inum nr ms.
Proof.
(* original proof tokens: 1089 *)

(* No more tactics to try *)
Admitted.

Theorem sync_ok : forall lxp ixp ms,
    {< F sm ds,
    PRE:hm
      LOG.rep lxp F (LOG.NoTxn ds) (MSLL ms) sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      LOG.rep lxp F (LOG.NoTxn (ds!!, nil)) (MSLL ms') sm hm' *
      [[ MSAlloc ms' = negb (MSAlloc ms) ]] *
      [[ MSCache ms' = MSCache ms ]] *
      [[ MSIAllocC ms = MSIAllocC ms' ]] *
      [[ MSICache ms = MSICache ms' ]] *
      [[ MSAllocC ms' = MSAllocC ms ]] *
      [[ MSDBlocks ms' = MSDBlocks ms ]]
    XCRASH:hm'
      LOG.recover_any lxp F ds hm'
    >} sync lxp ixp ms.
(* hint proof tokens: 19 *)
Proof.
    unfold sync, rep.
    step.
    step.
  Qed.
Theorem sync_noop_ok : forall lxp ixp ms,
    {< F sm ds,
    PRE:hm
      LOG.rep lxp F (LOG.NoTxn ds) (MSLL ms) sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      LOG.rep lxp F (LOG.NoTxn ds) (MSLL ms') sm hm' *
      [[ MSAlloc ms' = negb (MSAlloc ms) ]] *
      [[ MSCache ms' = MSCache ms ]] *
      [[ MSIAllocC ms = MSIAllocC ms' ]] *
      [[ MSICache ms = MSICache ms' ]] *
      [[ MSAllocC ms' = MSAllocC ms]]
    XCRASH:hm'
      LOG.recover_any lxp F ds hm'
    >} sync_noop lxp ixp ms.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 14 *)
unfold sync_noop.
step.
step.
Qed.

Lemma block_belong_to_file_off_ok : forall Fm Fi sm bxp ixp flist ilist frees cms mscache icache dblocks inum off f m,
    (Fm * rep bxp sm ixp flist ilist frees cms mscache icache dblocks)%pred m ->
    (Fi * inum |-> f)%pred (list2nmem flist) ->
    off < Datatypes.length (BFData f) -> 
    block_belong_to_file ilist # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0) inum off.
(* hint proof tokens: 184 *)
Proof.
    unfold block_belong_to_file; intros; split; auto.
    unfold rep, INODE.rep in H; destruct_lift H.
    rewrite listmatch_extract with (i := inum) in H.
    unfold file_match in H; destruct_lift H.
    setoid_rewrite listmatch_extract with (i := inum) (b := ilist) in H.
    destruct_lift H.
    erewrite listmatch_length_pimpl with (a := BFData _) in H.
    destruct_lift H.
    rewrite map_length in *.
    simplen.
    simplen.
    rewrite combine_length_eq by lia.
    erewrite listmatch_length_pimpl with (b := ilist) in *.
    destruct_lift H. simplen.
    Unshelve. split; eauto. exact INODE.inode0.
  Qed.
Lemma block_belong_to_file_ok : forall Fm Fi Fd bxp sm ixp flist ilist frees cms mscache icache dblocks inum off f vs m,
    (Fm * rep bxp sm ixp flist ilist frees cms mscache icache dblocks)%pred m ->
    (Fi * inum |-> f)%pred (list2nmem flist) ->
    (Fd * off |-> vs)%pred (list2nmem (BFData f)) ->
    block_belong_to_file ilist # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0) inum off.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Definition diskset_was (ds0 ds : diskset) := ds0 = ds \/ ds0 = (ds!!, nil).
Theorem d_in_diskset_was : forall d ds ds',
    d_in d ds ->
    diskset_was ds ds' ->
    d_in d ds'.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Theorem dwrite_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd sm ds flist ilist frees allocc f vs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (MSLL ms) sm hm *
           [[ off < length (BFData f) ]] *
           [[[ ds!! ::: (Fm  * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]] *
           [[ sync_invariant F ]]
    POST:hm' RET:ms'  exists flist' f' bn ds' sm',
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (MSLL ms') sm' hm' *
           [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
           [[ block_belong_to_file ilist bn inum off ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           
           [[[ ds'!! ::: (Fm  * rep bxp sm' ixp flist' ilist frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, vsmerge vs)) (BFAttr f) (BFCache f) ]]
    XCRASH:hm'
           LOG.recover_any lxp F ds hm' \/
           exists bn, [[ block_belong_to_file ilist bn inum off ]] *
           LOG.recover_any lxp F (dsupd ds bn (v, vsmerge vs)) hm'
    >} dwrite lxp ixp inum off v ms.
Proof.
(* original proof tokens: 722 *)

(* No more tactics to try *)
Admitted.

Theorem datasync_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi sm ds flist ilist free allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (MSLL ms) sm hm *
           [[[ ds!!  ::: (Fm  * rep bxp sm ixp flist ilist free allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ sync_invariant F ]]
    POST:hm' RET:ms'  exists ds' flist' al sm',
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (MSLL ms') sm' hm' *
           [[ ds' = dssync_vecs ds al ]] *
           [[[ ds'!! ::: (Fm * rep bxp sm' ixp flist' ilist free allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> synced_file f) ]]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ length al = length (BFILE.BFData f) /\ forall i, i < length al ->
              BFILE.block_belong_to_file ilist (selN al i 0) inum i ]]
    CRASH:hm' LOG.recover_any lxp F ds hm'
    >} datasync lxp ixp inum ms.
(* hint proof tokens: 643 *)
Proof.
    unfold datasync, synced_file, rep.
    
    intros.
    ProgMonad.monad_simpl.
    eapply pimpl_ok2.
    apply LOG.dsync_vecs_additional_ok.
    unfold smrep. intros. norml.
    rewrite arrayN_except with (i := inum) in *|- by sepauto.
    denote arrayN_ex as Ha.
    pose proof Ha as Ha'.
    rewrite <- locked_eq with (x := _ sm) in Ha'.
    rewrite smrep_single_helper_to_listmatch in *.
    destruct_lifts.
    extract.
    safecancel.
    cancel; solve [apply pimpl_refl].
    cancel.
    rewrite map_length in *.
    erewrite selN_map by auto.
    rewrite AddrSetFacts.elements_spec1.
    denote SS.In as Hs. eapply Hs; auto.
    auto.
    apply AddrSetFacts.nodup_elements.

    prestep. norm. cancel.
    intuition auto.
    2: sepauto.
    pred_apply. cancel.
    seprewrite.
    rewrite listmatch_isolate with (b := ilist) by sepauto.
    rewrite removeN_updN, selN_updN_eq by sepauto.
    rewrite synced_list_map_fst_map.
    unfold file_match. cancel.
    rewrite listmatch_map_l.
    cancel.
    auto.
    eauto using bfcache_upd.
    rewrite arrayN_except with (vs := ilist) by sepauto.
    rewrite arrayN_ex_smrep_single_helper_clear_dirty.
    cancel.
    unfold smrep_single_helper, clear_dirty, smrep_single.
    rewrite M.find_remove_eq.
    cancel.
    rewrite listpred_map.
    rewrite listpred_pimpl_replace.
    cancel; solve [apply pimpl_refl | apply sep_star_comm].
    cancel.
    unfold SS.For_all.
    setoid_rewrite SetFacts.empty_iff.
    intuition.
    seprewrite.
    symmetry.
    eapply listmatch_length_r with (m := list2nmem ds !!).
    pred_apply; cancel.

    erewrite selN_map by simplen.
    eapply block_belong_to_file_ok with (m := list2nmem ds!!); eauto.
    eassign (bxp_1, bxp_2); pred_apply; unfold rep. cancel; eauto.
    repeat erewrite fst_pair by eauto.
    cancel.
    rewrite listmatch_isolate with (a := flist) by sepauto.
    unfold file_match.
    cancel.
    rewrite locked_eq in Ha'.
    pred_apply' Ha'.
    unfold smrep.
    rewrite arrayN_except by sepauto.
    solve [do 2 cancel].
    seprewrite.
    apply list2nmem_ptsto_cancel.
    erewrite listmatch_length_l with (m := list2nmem ds !!); eauto.
    pred_apply; cancel.
  Unshelve.
    all: solve [eauto | exact BFILE.bfile0 | exact ($0, nil)].
  Qed.
Hint Extern 1 ({{_}} Bind (init _ _ _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (getlen _ _ _ _) _) => apply getlen_ok : prog.
Hint Extern 1 ({{_}} Bind (getattrs _ _ _ _) _) => apply getattrs_ok : prog.
Hint Extern 1 ({{_}} Bind (setattrs _ _ _ _ _) _) => apply setattrs_ok : prog.
Hint Extern 1 ({{_}} Bind (updattr _ _ _ _ _) _) => apply updattr_ok : prog.
Hint Extern 1 ({{_}} Bind (read _ _ _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (write _ _ _ _ _ _) _) => apply write_ok : prog.
Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _ _) _) => apply dwrite_ok : prog.
Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _ _) _) => apply grow_ok : prog.
Hint Extern 1 ({{_}} Bind (shrink _ _ _ _ _ _) _) => apply shrink_ok : prog.
Hint Extern 1 ({{_}} Bind (datasync _ _ _ _) _) => apply datasync_ok : prog.
Hint Extern 1 ({{_}} Bind (sync _ _ _) _) => apply sync_ok : prog.
Hint Extern 1 ({{_}} Bind (sync_noop _ _ _) _) => apply sync_noop_ok : prog.
Hint Extern 0 (okToUnify (rep _ _ _ _ _ _ _ _ _ _) (rep _ _ _ _ _ _ _ _ _ _)) => constructor : okToUnify.
Definition read_array lxp ixp inum a i ms :=
    let^ (ms, r) <- read lxp ixp inum (a + i) ms;
    Ret ^(ms, r).
Definition write_array lxp ixp inum a i v ms :=
    ms <- write lxp ixp inum (a + i) v ms;
    Ret ms.
Theorem read_array_ok : forall lxp bxp ixp inum a i ms,
    {< F Fm Fi Fd m0 sm m flist ilist free allocc f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist free allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a vsl ]]] *
           [[ i < length vsl]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist free allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[ r = fst (selN vsl i ($0, nil)) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} read_array lxp ixp inum a i ms.
Proof.
(* original proof tokens: 87 *)

(* No more tactics to try *)
Admitted.

Theorem write_array_ok : forall lxp bxp ixp inum a i v ms,
    {< F Fm Fi Fd m0 sm m flist ilist free allocc f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist free allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a vsl ]]] *
           [[ i < length vsl]]
    POST:hm' RET:ms' exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxp sm ixp flist' ilist free allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a (updN vsl i (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) (a + i) (v, nil)) (BFAttr f) (BFCache f) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} write_array lxp ixp inum a i v ms.
Proof.
(* original proof tokens: 109 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (read_array _ _ _ _ _ _) _) => apply read_array_ok : prog.
Hint Extern 1 ({{_}} Bind (write_array _ _ _ _ _ _ _) _) => apply write_array_ok : prog.
Definition read_range A lxp ixp inum a nr (vfold : A -> valu -> A) v0 ms0 :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi Fd crash m0 sm m flist ilist frees allocc f vsl ]
    Loopvar [ ms pf ]
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
      [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[[ (BFData f) ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a vsl ]]] *
      [[ pf = fold_left vfold (firstn i (map fst vsl)) v0 ]] *
      [[ MSAlloc ms = MSAlloc ms0 ]] *
      [[ MSCache ms = MSCache ms0 ]] *
      [[ MSIAllocC ms = MSIAllocC ms0 ]] *
      [[ MSAllocC ms = MSAllocC ms0 ]] *
      [[ MSDBlocks ms = MSDBlocks ms0 ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array lxp ixp inum a i ms;
      Ret ^(ms, vfold pf v)
    Rof ^(ms0, v0);
    Ret ^(ms, r).
Theorem read_range_ok : forall A lxp bxp ixp inum a nr (vfold : A -> valu -> A) v0 ms,
    {< F Fm Fi Fd m0 sm m flist ilist frees allocc f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a vsl ]]] *
           [[ nr <= length vsl]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[ r = fold_left vfold (firstn nr (map fst vsl)) v0 ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} read_range lxp ixp inum a nr vfold v0 ms.
(* hint proof tokens: 164 *)
Proof.
    unfold read_range.
    safestep. eauto. eauto.
    safestep.

    assert (m1 < length vsl).
    denote (arrayN _ a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; lia.
    safestep.

    rewrite firstn_S_selN_expand with (def := $0) by (rewrite map_length; auto).
    rewrite fold_left_app; simpl.
    erewrite selN_map; subst; auto.
    cancel.

    safestep.
    cancel.
    erewrite <- LOG.rep_hashmap_subset; eauto.
  Unshelve.
    all: eauto; try exact tt; intros; try exact emp.
  Qed.
Definition read_cond A lxp ixp inum (vfold : A -> valu -> A)
                       v0 (cond : A -> bool) ms0 :=
    let^ (ms, nr) <- getlen lxp ixp inum ms0;
    let^ (ms, r, ret) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi m0 sm m flist f ilist frees allocc ]
    Loopvar [ ms pf ret ]
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
      [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[ MSAlloc ms = MSAlloc ms0 ]] *
      [[ MSCache ms = MSCache ms0 ]] *
      [[ MSIAllocC ms = MSIAllocC ms0 ]] *
      [[ MSAllocC ms = MSAllocC ms0 ]] *
      [[ MSDBlocks ms = MSDBlocks ms0 ]] *
      [[ ret = None ->
        pf = fold_left vfold (firstn i (map fst (BFData f))) v0 ]] *
      [[ ret = None ->
        cond pf = false ]] *
      [[ forall v, ret = Some v ->
        cond v = true ]]
    OnCrash
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm
    Begin
      If (is_some ret) {
        Ret ^(ms, pf, ret)
      } else {
        let^ (ms, v) <- read lxp ixp inum i ms;
        let pf' := vfold pf v in
        If (bool_dec (cond pf') true) {
          Ret ^(ms, pf', Some pf')
        } else {
          Ret ^(ms, pf', None)
        }
      }
    Rof ^(ms, v0, None);
    Ret ^(ms, ret).
Theorem read_cond_ok : forall A lxp bxp ixp inum (vfold : A -> valu -> A)
                                v0 (cond : A -> bool) ms,
    {< F Fm Fi m0 sm m flist ilist frees allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ cond v0 = false ]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]] *
           ( exists v, 
             [[ r = Some v /\ cond v = true ]] \/
             [[ r = None /\ cond (fold_left vfold (map fst (BFData f)) v0) = false ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} read_cond lxp ixp inum vfold v0 cond ms.
(* hint proof tokens: 179 *)
Proof.
    unfold read_cond.
    prestep. cancel.
    safestep. eauto. eauto.

    msalloc_eq.
    step.
    step.
    step.

    eapply list2nmem_array_pick; eauto.
    step.
    step.
    step.

    rewrite firstn_S_selN_expand with (def := $0) by (rewrite map_length; auto).
    rewrite fold_left_app; simpl.
    erewrite selN_map; subst; auto.
    apply not_true_is_false; auto.

    destruct a2.
    step.
    step.
    or_r; cancel.
    denote cond as Hx; rewrite firstn_oob in Hx; auto.
    rewrite map_length; auto.
    cancel.

  Unshelve.
    all: try easy.
    try exact ($0, nil).
  Qed.
Hint Extern 1 ({{_}} Bind (read_range _ _ _ _ _ _ _ _) _) => apply read_range_ok : prog.
Hint Extern 1 ({{_}} Bind (read_cond _ _ _ _ _ _ _) _) => apply read_cond_ok : prog.
Definition grown lxp bxp ixp inum l ms0 :=
    let^ (ms, ret) <- ForN i < length l
      Hashmap hm
      Ghost [ F Fm Fi m0 sm f ilist frees ]
      Loopvar [ ms ret ]
      Invariant
        exists m',
        LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms) sm hm *
        [[ MSAlloc ms = MSAlloc ms0 ]] *
        [[ MSCache ms = MSCache ms0 ]] *
        [[ MSIAllocC ms = MSIAllocC ms0 ]] *
        ([[ isError ret ]] \/
         exists flist' ilist' frees' f',
         [[ ret = OK tt ]] *
         [[[ m' ::: (Fm * rep bxp sm ixp flist' ilist' frees' (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
         [[[ flist' ::: (Fi * inum |-> f') ]]] *
         [[  f' = mk_bfile ((BFData f) ++ synced_list (firstn i l)) (BFAttr f) (BFCache f) ]] *
         [[ ilist_safe ilist  (pick_balloc frees  (MSAlloc ms)) 
                       ilist' (pick_balloc frees' (MSAlloc ms)) ]] *
         [[ treeseq_ilist_safe inum ilist ilist' ]])
      OnCrash
        LOG.intact lxp F m0 sm hm
      Begin
        match ret with
        | Err e => Ret ^(ms, ret)
        | OK _ =>
          let^ (ms, ok) <- grow lxp bxp ixp inum (selN l i $0) ms;
          Ret ^(ms, ok)
        end
      Rof ^(ms0, OK tt);
    Ret ^(ms, ret).
Definition truncate lxp bxp xp inum newsz ms :=
    let^ (ms, sz) <- getlen lxp xp inum ms;
    If (lt_dec newsz sz) {
      ms <- shrink lxp bxp xp inum (sz - newsz) ms;
      Ret ^(ms, OK tt)
    } else {
      let^ (ms, ok) <- grown lxp bxp xp inum (repeat $0 (newsz - sz)) ms;
      Ret ^(ms, ok)
    }.
Definition reset lxp bxp xp inum ms :=
    let^ (fms, sz) <- getlen lxp xp inum ms;
    let '(al, ms, alc, ialc, icache, cache, dblocks) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSIAllocC fms, MSICache fms, MSCache fms, MSDBlocks fms) in
    let^ (icache, ms, bns) <- INODE.getallbnum lxp xp inum icache ms;
    let l := map (@wordToNat _) bns in
    cms <- BALLOCC.freevec lxp (pick_balloc bxp (negb al)) l (BALLOCC.mk_memstate ms (pick_balloc alc (negb al)));
    let^ (icache, cms) <- INODE.reset lxp (pick_balloc bxp (negb al)) xp inum sz attr0 icache cms;
    let dblocks := clear_dirty inum dblocks in
    Ret (mk_memstate al (BALLOCC.MSLog cms) (upd_balloc alc (BALLOCC.MSCache cms) (negb al)) ialc icache (BFcache.remove inum cache) dblocks).
Definition reset' lxp bxp xp inum ms :=
    let^ (ms, sz) <- getlen lxp xp inum ms;
    ms <- shrink lxp bxp xp inum sz ms;
    ms <- setattrs lxp xp inum attr0 ms;
    Ret (mk_memstate (MSAlloc ms) (MSLL ms) (MSAllocC ms) (MSIAllocC ms) (MSICache ms) (BFcache.remove inum (MSCache ms)) (MSDBlocks ms)).
Theorem grown_ok : forall lxp bxp ixp inum l ms,
    {< F Fm Fi Fd m0 sm m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST:hm' RET:^(ms', r)
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSCache ms' = MSCache ms ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' \/
           [[ r = OK tt  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxp sm ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * arrayN (@ptsto _ addr_eq_dec _) (length (BFData f)) (synced_list l)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ (synced_list l)) (BFAttr f) (BFCache f) ]] *
           [[ ilist_safe ilist (pick_balloc frees (MSAlloc ms')) 
                      ilist' (pick_balloc frees' (MSAlloc ms'))  ]] *
           [[ treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} grown lxp bxp ixp inum l ms.
(* hint proof tokens: 223 *)
Proof.
    unfold grown; intros.
    safestep.
    unfold synced_list; simpl; rewrite app_nil_r.
    eassign f; destruct f.
    eassign F_; cancel. or_r; cancel. eapply treeseq_ilist_safe_refl.
    eauto. eauto.

    safestep.
    apply list2nmem_arrayN_app; eauto.
    safestep.
    cancel.
    or_r; cancel.
    erewrite firstn_S_selN_expand by lia.
    rewrite synced_list_app, <- app_assoc.
    unfold synced_list at 3; simpl; eauto.
    msalloc_eq.
    eapply ilist_safe_trans; eauto.
    eapply treeseq_ilist_safe_trans; eauto.

    cancel.
    cancel.

    safestep.
    cancel.
    or_r; cancel.
    rewrite firstn_oob; auto.
    apply list2nmem_arrayN_app; auto.
    rewrite firstn_oob; auto.

    cancel.
    Unshelve. all: easy.
  Qed.
Hint Extern 1 ({{_}} Bind (grown _ _ _ _ _ _) _) => apply grown_ok : prog.
Theorem truncate_ok : forall lxp bxp ixp inum sz ms,
    {< F Fm Fi m0 sm m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms', r)
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' \/
           [[ r = OK tt  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxp sm ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (setlen (BFData f) sz ($0, nil)) (BFAttr f) (BFCache f) ]] *
           [[ ilist_safe ilist (pick_balloc frees (MSAlloc ms')) 
                         ilist' (pick_balloc frees' (MSAlloc ms'))  ]] *
           [[ sz >= Datatypes.length (BFData f) -> treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} truncate lxp bxp ixp inum sz ms.
Proof.
(* original proof tokens: 135 *)

(* No more tactics to try *)
Admitted.

Theorem reset_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 sm m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees (MSAllocC ms) (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms' exists m' flist' ilist' frees',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
           [[[ m' ::: (Fm * rep bxp sm ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> bfile0) ]]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ ilist_safe ilist  (pick_balloc frees  (MSAlloc ms'))
                         ilist' (pick_balloc frees' (MSAlloc ms')) ]] *
           [[ forall inum' def', inum' <> inum -> 
                selN ilist inum' def' = selN ilist' inum' def' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} reset lxp bxp ixp inum ms.
(* hint proof tokens: 585 *)
Proof.
    unfold reset; intros.
    step.
    prestep. norml.
    rewrite rep_alt_equiv with (msalloc := MSAlloc ms) in *.
    match goal with H: context [rep_alt] |- _ =>
      unfold rep_alt, smrep in H; destruct_lift H end.
    cancel; msalloc_eq.
    sepauto.

    rewrite INODE.rep_bxp_switch in *|- by eassumption.
    step.
    rewrite Forall_map.
    match goal with H: context [INODE.rep] |- context [pick_balloc ?a ?b] =>
      rewrite INODE.inode_rep_bn_valid_piff with (bxp := pick_balloc a b) in H; destruct_lift H
    end.
    intuition sepauto.
    rewrite listmatch_isolate by sepauto.
    unfold file_match at 2.
    erewrite <- listmatch_ptsto_listpred.
    cancel.
    rewrite arrayN_except by sepauto.
    rewrite smrep_single_helper_clear_dirty.
    cancel.

    prestep; norm. cancel.
    intuition auto.
    pred_apply.
    erewrite INODE.rep_bxp_switch by eassumption.
    cancel.
    apply list2nmem_array_pick. sepauto.
    pred_apply. cancel.

    seprewrite.
    safestep.
    2: sepauto.
    rewrite rep_alt_equiv with (msalloc := MSAlloc a).
    cbv [rep_alt].
    erewrite <- INODE.rep_bxp_switch by eassumption.
    unfold cuttail.
    match goal with H: context [listmatch file_match flist ilist] |- _ =>
      erewrite file_match_length by solve [pred_apply' H; cancel | sepauto]
    end.
    rewrite Nat.sub_diag.
    cancel.
    rewrite listmatch_updN_removeN by sepauto.
    unfold file_match, listmatch. cancel.
    4: erewrite <- surjective_pairing, <- pick_upd_balloc_lift;
      auto using ilist_safe_upd_nil.
    
    repeat rewrite <- surjective_pairing.
    repeat rewrite <- pick_upd_balloc_negb.
    rewrite <- pick_negb_upd_balloc.
    repeat rewrite <- pick_upd_balloc_lift.
    cancel.
    eapply bfcache_remove'; sepauto.
    unfold smrep. cancel.
    rewrite arrayN_except_upd by sepauto.
    rewrite arrayN_ex_smrep_single_helper_clear_dirty.
    cancel.
    destruct MSAlloc; cancel.
    rewrite selN_updN_ne; auto.
    cancel.
    cancel.
    eauto.
  Unshelve.
    all : try easy.
    all : solve [ exact bfile0 | intros; exact emp | exact nil].
  Qed.
Hint Extern 1 ({{_}} Bind (truncate _ _ _ _ _ _) _) => apply truncate_ok : prog.
Hint Extern 1 ({{_}} Bind (reset _ _ _ _ _) _) => apply reset_ok : prog.
Theorem recover_ok : forall ms,
    {< F ds sm lxp,
    PRE:hm  LOG.rep lxp F (LOG.NoTxn ds) ms sm hm
    POST:hm' RET:ms'
      LOG.rep lxp F (LOG.NoTxn ds) (MSLL ms') sm hm' *
      [[ ms = (MSLL ms') ]] *
      [[ BFILE.MSinitial ms' ]]
    CRASH:hm' LOG.rep lxp F (LOG.NoTxn ds) ms sm hm'
    >} recover ms.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (recover _ ) _) => apply recover_ok : prog.
Theorem cache_get_ok : forall inum ms,
    {< F Fm Fi m0 sm m lxp bxp ixp flist ilist frees allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms', r)
           [[ ms' = ms ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           [[ r = BFCache f ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} cache_get inum ms.
(* hint proof tokens: 40 *)
Proof.
    unfold cache_get, rep; intros.
    step.
    step.
    destruct ms; reflexivity.
    eapply bfcache_find; eauto.
  Qed.
Theorem cache_put_ok : forall inum ms c,
    {< F Fm Fi m0 sm m lxp bxp ixp flist ilist frees allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           [[[ m ::: (Fm * rep bxp sm ixp flist ilist frees allocc (MSCache ms) (MSICache ms) (MSDBlocks ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'
           exists f' flist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           [[[ m ::: (Fm * rep bxp sm ixp flist' ilist frees allocc (MSCache ms') (MSICache ms') (MSDBlocks ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) (BFAttr f) (Some c) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSIAllocC ms = MSIAllocC ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSDBlocks ms = MSDBlocks ms' ]] *
           [[ MSLL ms = MSLL ms' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} cache_put inum c ms.
(* hint proof tokens: 130 *)
Proof.
    unfold cache_put, rep; intros.
    step.
    seprewrite.
    prestep. norm. cancel.
    intuition idtac.
    2: sepauto.
    pred_apply; cancel.
    erewrite <- updN_selN_eq with (l := ilist) at 2.
    rewrite listmatch_updN_removeN by sepauto.
    rewrite listmatch_isolate by sepauto.
    unfold file_match.
    cancel.
    eauto using bfcache_put.
    eauto.
  Unshelve.
    all: exact INODE.inode0.
  Qed.
Hint Extern 1 ({{_}} Bind (cache_get _ _) _) => apply cache_get_ok : prog.
Hint Extern 1 ({{_}} Bind (cache_put _ _ _) _) => apply cache_put_ok : prog.
Definition FSynced f : Prop :=
     forall n, snd (selN (BFData f) n ($0, nil)) = nil.
Definition file_crash f f' : Prop :=
    exists vs, possible_crash_list (BFData f) vs /\
    f' = mk_bfile (synced_list vs) (BFAttr f) None.
Definition flist_crash fl fl' : Prop :=
    Forall2 file_crash fl fl'.
Lemma flist_crash_length : forall a b,
    flist_crash a b -> length a = length b.
(* hint proof tokens: 26 *)
Proof.
    unfold flist_crash; intros.
    eapply forall2_length; eauto.
  Qed.
Lemma fsynced_synced_file : forall f,
    FSynced (synced_file f).
Proof.
(* original proof tokens: 98 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_synced_list_fsynced : forall f l,
    arrayN (@ptsto _ addr_eq_dec _) 0 (synced_list l) (list2nmem (BFData f)) ->
    FSynced f.
(* hint proof tokens: 49 *)
Proof.
    unfold FSynced; intros.
    erewrite list2nmem_array_eq with (l' := (BFData f)) by eauto.
    rewrite synced_list_selN; simpl; auto.
  Qed.
Lemma file_crash_attr : forall f f',
    file_crash f f' -> BFAttr f' = BFAttr f.
(* hint proof tokens: 25 *)
Proof.
    unfold file_crash; intros.
    destruct H; intuition; subst; auto.
  Qed.
Lemma file_crash_possible_crash_list : forall f f',
    file_crash f f' ->
    possible_crash_list (BFData f) (map fst (BFData f')).
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma file_crash_data_length : forall f f',
    file_crash f f' -> length (BFData f) = length (BFData f').
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma file_crash_synced : forall f f',
    file_crash f f' ->
    FSynced f ->
    BFData f = BFData f' /\
    BFAttr f = BFAttr f'.
(* hint proof tokens: 126 *)
Proof.
    unfold FSynced, file_crash; intros.
    destruct H; intuition subst; simpl; eauto.
    destruct f; simpl in *.
    f_equal.
    eapply list_selN_ext.
    rewrite synced_list_length.
    apply possible_crash_list_length; auto.
    intros.
    setoid_rewrite synced_list_selN.
    rewrite surjective_pairing at 1.
    rewrite H0.
    f_equal.
    erewrite possible_crash_list_unique with (b := x); eauto.
    erewrite selN_map; eauto.
  Qed.
Lemma file_crash_fsynced : forall f f',
    file_crash f f' ->
    FSynced f'.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma file_crash_ptsto : forall f f' vs F a,
    file_crash f f' ->
    (F * a |-> vs)%pred (list2nmem (BFData f)) ->
    (exists v, [[ In v (vsmerge vs) ]]  *
       crash_xform F * a |=> v)%pred (list2nmem (BFData f')).
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Lemma xform_file_match : forall f ino,
    crash_xform (file_match f ino) =p=> 
      exists f', [[ file_crash f f' ]] * file_match f' ino.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma xform_file_list : forall fs inos,
    crash_xform (listmatch file_match fs inos) =p=>
      exists fs', [[ flist_crash fs fs' ]] * listmatch file_match fs' inos.
Proof.
(* original proof tokens: 154 *)

(* No more tactics to try *)
Admitted.

Lemma flist_crash_caches_cleared: forall flist flist',
    flist_crash flist flist' ->
    Forall (fun f => BFCache f = None) flist'.
(* hint proof tokens: 47 *)
Proof.
    unfold flist_crash.
    induction flist; cbn; intros; inversion H; constructor.
    unfold file_crash in *.
    deex.
    auto.
    auto.
  Qed.
Lemma smrep_single_helper_sm_sync_all: forall dblocks inum ino sm,
    smrep_single_helper dblocks inum ino sm ->
    smrep_single_helper (Map.empty _ ) inum ino (sm_sync_all sm).
Proof.
(* original proof tokens: 179 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_smrep_single_helper_sm_sync_all: forall dblocks ilist i sm,
    arrayN (smrep_single_helper dblocks) i ilist sm ->
    arrayN (smrep_single_helper (Map.empty _)) i ilist (sm_sync_all sm).
(* hint proof tokens: 47 *)
Proof.
  induction ilist; cbn; intros; auto.
  eapply sm_sync_all_sep_star_swap; eauto.
  intros.
  eauto using smrep_single_helper_sm_sync_all.
  Qed.
Lemma smrep_sm_sync_all: forall frees dblocks ilist sm,
    smrep frees dblocks ilist sm ->
    smrep frees (Map.empty _) ilist (SyncedMem.sm_sync_all sm).
Proof.
(* original proof tokens: 82 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_smrep_sm_synced: forall IFs ilist frees dblocks sm Fs,
    sm_sync_invariant IFs ->
    ((Fs * IFs) * smrep frees dblocks ilist)%pred sm ->
    ((any * IFs) * smrep frees (Map.empty _) ilist)%pred sm_synced.
(* hint proof tokens: 85 *)
Proof.
    intros.
    apply sep_star_assoc_2.
    eapply sm_synced_sep_star_l with (p := any).
    apply sep_star_assoc_1.
    eapply sm_sync_all_sep_star_swap; eauto.
    intros.
    eapply sm_sync_all_sep_star_swap_l; eauto.
    firstorder.
    eauto using smrep_sm_sync_all.
  Qed.
Lemma xform_rep : forall bxp ixp flist ilist sm frees allocc mscache icache dblocks,
    crash_xform (rep bxp sm ixp flist ilist frees allocc mscache icache dblocks) =p=>
      exists flist', [[ flist_crash flist flist' ]] *
      rep bxp sm_synced ixp flist' ilist frees allocc (BFcache.empty _) icache (Map.empty _).
Proof.
(* original proof tokens: 99 *)

(* No more tactics to try *)
Admitted.

Lemma xform_file_match_ptsto : forall F a vs f ino,
    (F * a |-> vs)%pred (list2nmem (BFData f)) ->
    crash_xform (file_match f ino) =p=>
      exists f' v, file_match f' ino *
      [[ In v (vsmerge vs) ]] *
      [[ (crash_xform F * a |=> v)%pred (list2nmem (BFData f')) ]].
(* hint proof tokens: 128 *)
Proof.
    unfold file_crash, file_match; intros.
    xform_norm.
    rewrite xform_listmatch_ptsto.
    xform_norm.
    pose proof (list2nmem_crash_xform _ H1 H) as Hx.
    apply crash_xform_sep_star_dist in Hx.
    rewrite crash_xform_ptsto in Hx; destruct_lift Hx.

    norm.
    eassign (mk_bfile (synced_list l) (BFAttr f) (BFCache f)); cancel.
    eassign (dummy).
    intuition subst; eauto.
  Qed.
Lemma xform_rep_file : forall F bxp ixp fs f i ilist sm frees allocc mscache icache dblocks,
    (F * i |-> f)%pred (list2nmem fs) ->
    crash_xform (rep bxp sm ixp fs ilist frees allocc mscache icache dblocks) =p=>
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp sm_synced ixp fs' ilist frees allocc (BFcache.empty _) icache (Map.empty _) *
      [[ (arrayN_ex (@ptsto _ addr_eq_dec _) fs' i * i |-> f')%pred (list2nmem fs') ]].
Proof.
(* original proof tokens: 283 *)
intros.
unfold rep in H; simpl in H.
destruct_lift H.
xform_norm.
cancel.
(* No more tactics to try *)
Admitted.

Lemma xform_rep_file_pred : forall (F Fd : pred) bxp ixp fs f i ilist sm frees allocc mscache icache dblocks,
    (F * i |-> f)%pred (list2nmem fs) ->
    (Fd (list2nmem (BFData f))) ->
    crash_xform (rep bxp sm ixp fs ilist frees allocc mscache icache dblocks) =p=>
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp sm_synced ixp fs' ilist frees allocc (BFcache.empty _) icache (Map.empty _) *
      [[ (arrayN_ex (@ptsto _ addr_eq_dec _) fs' i * i |-> f')%pred (list2nmem fs') ]] *
      [[ (crash_xform Fd)%pred (list2nmem (BFData f')) ]].
Proof.
(* original proof tokens: 56 *)

(* No more tactics to try *)
Admitted.

Lemma xform_rep_off : forall Fm Fd bxp ixp ino off f fs vs ilist sm frees allocc mscache icache dblocks,
    (Fm * ino |-> f)%pred (list2nmem fs) ->
    (Fd * off |-> vs)%pred (list2nmem (BFData f)) ->
    crash_xform (rep bxp sm ixp fs ilist frees allocc mscache icache dblocks) =p=>
      exists fs' f' v, [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp sm_synced ixp fs' ilist frees allocc (BFcache.empty _) icache (Map.empty _) * [[ In v (vsmerge vs) ]] *
      [[ (arrayN_ex (@ptsto _ addr_eq_dec _) fs' ino * ino |-> f')%pred (list2nmem fs') ]] *
      [[ (crash_xform Fd * off |=> v)%pred (list2nmem (BFData f')) ]].
Proof.
(* original proof tokens: 64 *)

(* No more tactics to try *)
Admitted.

Lemma flist_crash_clear_caches : forall f f',
    flist_crash f f' ->
    clear_caches f' = f'.
Proof.
(* original proof tokens: 76 *)

(* No more tactics to try *)
Admitted.

Lemma freepred_file_crash : forall f f',
    file_crash f f' -> freepred f -> freepred f'.
(* hint proof tokens: 61 *)
Proof.
    unfold file_crash, freepred, bfile0; intros.
    deex.
    f_equal.
    simpl in *.
    eapply possible_crash_list_length in H1.
    destruct vs; simpl in *; eauto.
    lia.
  Qed.
Lemma freepred_bfile0 : freepred bfile0.
(* hint proof tokens: 15 *)
Proof.
    unfold freepred; eauto.
  Qed.
Hint Resolve freepred_bfile0.
End BFILE.
Ltac msalloc_eq := BFILE.msalloc_eq.
