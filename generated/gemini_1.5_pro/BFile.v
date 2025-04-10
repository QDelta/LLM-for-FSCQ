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
(* skipped proof tokens: 18 *)
Admitted.
Theorem pick_negb_upd_balloc : forall A flag p (new : A),
    pick_balloc p (negb flag) = pick_balloc (upd_balloc p new flag) (negb flag).
Proof.
(* original proof tokens: 18 *)
(* generated proof tokens: 28 *)

intros.
unfold pick_balloc, upd_balloc.
destruct flag; destruct p; auto.
Qed.

Theorem pick_upd_balloc_lift : forall A flag p (new : A),
    new = pick_balloc (upd_balloc p new flag) flag.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
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
(* skipped proof tokens: 48 *)
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
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Definition clear_cache bf := mk_bfile (BFData bf) (BFAttr bf) None.
Definition clear_caches bflist := map clear_cache bflist.
Theorem rep_clear_freelist : forall bxps sm ixp flist ilist frees allocc mscache icache dblocks,
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks =p=>
    rep bxps sm ixp flist ilist frees (BALLOCC.Alloc.freelist0, BALLOCC.Alloc.freelist0) mscache icache dblocks.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Theorem rep_clear_bfcache : forall bxps sm ixp flist ilist frees allocc mscache icache dblocks,
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks =p=>
    rep bxps sm ixp (clear_caches flist) ilist frees allocc (BFcache.empty _) icache dblocks.
Proof.
(* skipped proof tokens: 132 *)
Admitted.
Theorem rep_clear_icache: forall bxps sm ixp flist ilist frees allocc mscache icache dblocks,
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks =p=>
    rep bxps sm ixp flist ilist frees allocc mscache INODE.IRec.cache0 dblocks.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma smrep_init: forall n,
    emp <=p=> arrayN (smrep_single_helper (Map.empty _)) 0 (repeat INODE.inode0 n).
Proof.
(* skipped proof tokens: 85 *)
Admitted.
Lemma smrep_single_helper_split_tail: forall inum ino ino' dblocks n,
    INODE.IBlocks ino' = firstn n (INODE.IBlocks ino) ->
    NoDup (map (@wordToNat addrlen) (INODE.IBlocks ino)) ->
    let removed := map (@wordToNat addrlen) (skipn n (INODE.IBlocks ino)) in
    smrep_single_helper dblocks inum ino =p=>
    smrep_single_helper (remove_dirty_vec inum removed dblocks) inum ino' *
    listpred (fun a => a |->?) removed.
Proof.
(* skipped proof tokens: 407 *)
Admitted.
Lemma smrep_single_helper_clear_dirty: forall inum ino dblocks,
    smrep_single_helper dblocks inum ino =p=>
    smrep_single_helper (clear_dirty inum dblocks) inum INODE.inode0 *
    listpred (fun a => a |->?) (map (@wordToNat addrlen) (INODE.IBlocks ino)).
Proof.
(* skipped proof tokens: 76 *)
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
(* skipped proof tokens: 517 *)
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
(* skipped proof tokens: 15 *)
Admitted.
Local Hint Resolve ilist_safe_refl.
Theorem ilist_safe_trans : forall i1 f1 i2 f2 i3 f3,
    ilist_safe i1 f1 i2 f2 ->
    ilist_safe i2 f2 i3 f3 ->
    ilist_safe i1 f1 i3 f3.
Proof.
(* skipped proof tokens: 76 *)
Admitted.
Theorem ilist_safe_upd_nil : forall ilist frees i off,
    INODE.IBlocks i = nil ->
    ilist_safe ilist frees (updN ilist off i) frees.
Proof.
(* skipped proof tokens: 111 *)
Admitted.
Lemma block_belong_to_file_inum_ok : forall ilist bn inum off,
    block_belong_to_file ilist bn inum off ->
    inum < length ilist.
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Lemma rep_used_block_eq_Some_helper : forall T (x y: T),
    Some x = Some y -> x = y.
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Theorem rep_used_block_eq : forall F bxps sm ixp flist ilist m bn inum off frees allocc mscache icache dblocks,
    (F * rep bxps sm ixp flist ilist frees allocc mscache icache dblocks)%pred (list2nmem m) ->
    block_belong_to_file ilist bn inum off ->
    selN (BFData (selN flist inum bfile0)) off ($0, nil) = selN m bn ($0, nil).
Proof.
(* skipped proof tokens: 321 *)
Admitted.
Lemma smrep_single_helper_add_oob: forall inum dirty dblocks st ino,
    inum <> st ->
    smrep_single_helper (Map.add inum dirty dblocks) st ino <=p=>
    smrep_single_helper dblocks st ino.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma smrep_single_helper_remove_oob: forall inum dblocks st ino,
    inum <> st ->
    smrep_single_helper (Map.remove inum dblocks) st ino <=p=>
    smrep_single_helper dblocks st ino.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_smrep_single_helper_add_oob: forall ilist st inum dirty dblocks,
    inum < st \/ inum >= st + length ilist ->
    arrayN (smrep_single_helper (Map.add inum dirty dblocks)) st ilist <=p=>
    arrayN (smrep_single_helper dblocks) st ilist.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma arrayN_smrep_single_helper_remove_oob: forall ilist st inum dblocks,
    inum < st \/ inum >= st + length ilist ->
    arrayN (smrep_single_helper (Map.remove inum dblocks)) st ilist <=p=>
    arrayN (smrep_single_helper dblocks) st ilist.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma arrayN_ex_smrep_single_helper_add: forall ilist inum dirty dblocks,
    arrayN_ex (smrep_single_helper (Map.add inum dirty dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
Proof.
(* skipped proof tokens: 123 *)
Admitted.
Lemma arrayN_ex_smrep_single_helper_remove: forall ilist inum dblocks,
    arrayN_ex (smrep_single_helper (Map.remove inum dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
Proof.
(* skipped proof tokens: 123 *)
Admitted.
Lemma arrayN_ex_smrep_single_helper_put_dirty: forall ilist inum bn dblocks,
    arrayN_ex (smrep_single_helper (put_dirty inum bn dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma arrayN_ex_smrep_single_helper_remove_dirty_vec: forall ilist inum bn dblocks,
    arrayN_ex (smrep_single_helper (remove_dirty_vec inum bn dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
Proof.
(* original proof tokens: 35 *)
split; intros; cancel.
(* No more tactics to try *)
Admitted.

Lemma arrayN_ex_smrep_single_helper_clear_dirty: forall ilist inum dblocks,
    arrayN_ex (smrep_single_helper (clear_dirty inum dblocks)) ilist inum <=p=>
    arrayN_ex (smrep_single_helper dblocks) ilist inum.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma selN_NoDup_notin_firstn: forall T (l : list T) i x d,
    i < length l ->
    NoDup l ->
    selN l i d = x ->
    ~In x (firstn i l).
Proof.
(* skipped proof tokens: 69 *)
Admitted.
Lemma selN_NoDup_notin_skipn: forall T (l : list T) i x d,
    i < length l ->
    NoDup l ->
    selN l i d = x ->
    ~In x (skipn (S i) l).
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Lemma selN_NoDup_notin_removeN: forall T (l : list T) i x d,
    i < length l ->
    selN l i d = x ->
    NoDup l ->
    ~In x (removeN l i).
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma smrep_single_add: forall dirty ino bn,
    In bn (INODE.IBlocks ino) ->
    smrep_single dirty ino =p=> smrep_single (SS.add #bn dirty) ino.
Proof.
(* skipped proof tokens: 140 *)
Admitted.
Lemma smrep_single_helper_put_dirty: forall inum bn dblocks ino,
    In bn (INODE.IBlocks ino) ->
    smrep_single_helper dblocks inum ino =p=>
    smrep_single_helper (put_dirty inum #bn dblocks) inum ino.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma smrep_upd: forall frees dblocks ilist inum bn,
    goodSize addrlen bn ->
    In $bn (INODE.IBlocks (selN ilist inum INODE.inode0)) ->
    inum < length ilist ->
    smrep frees dblocks ilist =p=> smrep frees (put_dirty inum bn dblocks) ilist.
Proof.
(* skipped proof tokens: 94 *)
Admitted.
Lemma smrep_single_add_new: forall dirty ino ino' bn b,
    INODE.IBlocks ino' = INODE.IBlocks ino ++ [bn] ->
    #bn |->b * smrep_single dirty ino =p=> smrep_single (SS.add #bn dirty) ino'.
Proof.
(* skipped proof tokens: 123 *)
Admitted.
Lemma smrep_single_helper_add_dirty: forall inum bn dblocks ino ino' b,
    INODE.IBlocks ino' = INODE.IBlocks ino ++ [bn] ->
    #bn |-> b * smrep_single_helper dblocks inum ino =p=>
    smrep_single_helper (put_dirty inum #bn dblocks) inum ino'.
Proof.
(* skipped proof tokens: 48 *)
Admitted.
Lemma smrep_upd_add: forall frees dblocks ilist ilist' ino' inum bn b,
    goodSize addrlen bn ->
    inum < length ilist ->
    let ino := (selN ilist inum INODE.inode0) in
    ilist' = updN ilist inum ino' ->
    INODE.IBlocks ino' = INODE.IBlocks ino ++ [$bn] ->
    bn |-> b * smrep frees dblocks ilist =p=> smrep frees (put_dirty inum bn dblocks) ilist'.
Proof.
(* skipped proof tokens: 114 *)
Admitted.
Lemma smrep_upd_keep_blocks :
    forall frees dblocks ilist inum i' def,
    INODE.IBlocks (selN ilist inum def) = INODE.IBlocks i' ->
    smrep frees dblocks ilist =p=> smrep frees dblocks (updN ilist inum i').
Proof.
(* skipped proof tokens: 92 *)
Admitted.
Lemma smrep_single_helper_split_dirty: forall dblocks inum ino ino' off,
    INODE.IBlocks ino' = removeN (INODE.IBlocks ino) off ->
    off < length (INODE.IBlocks ino) ->
    NoDup (map (@wordToNat addrlen) (INODE.IBlocks ino)) ->
    let bn := #(selN (INODE.IBlocks ino) off $0) in
    smrep_single_helper dblocks inum ino =p=> smrep_single_helper (remove_dirty inum bn dblocks) inum ino' * bn |->?.
Proof.
(* skipped proof tokens: 337 *)
Admitted.
Lemma smrep_single_helper_return_dirty: forall dblocks inum ino ino' off b,
    INODE.IBlocks ino' = removeN (INODE.IBlocks ino) off ->
    off < length (INODE.IBlocks ino) ->
    let bn := #(selN (INODE.IBlocks ino) off $0) in
    bn |-> b * smrep_single_helper dblocks inum ino' =p=> smrep_single_helper (put_dirty inum bn dblocks) inum ino.
Proof.
(* skipped proof tokens: 258 *)
Admitted.
Lemma smrep_single_helper_put_remove_dirty: forall dblocks inum bn ino,
    smrep_single_helper (put_dirty inum bn (remove_dirty inum bn dblocks)) inum ino =p=>
    smrep_single_helper (put_dirty inum bn dblocks) inum ino.
Proof.
(* skipped proof tokens: 132 *)
Admitted.
Lemma smrep_single_helper_to_listmatch: forall dblocks inum ino,
    smrep_single_helper dblocks inum ino =p=> exists l,
      listmatch (fun b a => a |-> b) l (map (@wordToNat addrlen) (INODE.IBlocks ino)) *
      [[ forall i, i < length (INODE.IBlocks ino) -> SS.In #(selN (INODE.IBlocks ino) i $0) (get_dirty inum dblocks) \/
        selN l i false = true ]] * [[ incl (SS.elements (get_dirty inum dblocks)) (map (wordToNat (sz:=addrlen)) (INODE.IBlocks ino)) ]].
Proof.
(* skipped proof tokens: 277 *)
Admitted.
Theorem rep_safe_used: forall F bxps sm ixp flist ilist m bn inum off frees allocc mscache icache dblocks v,
    (F * rep bxps sm ixp flist ilist frees allocc mscache icache dblocks)%pred (list2nmem m) ->
    block_belong_to_file ilist bn inum off ->
    let f := selN flist inum bfile0 in
    let f' := mk_bfile (updN (BFData f) off v) (BFAttr f) (BFCache f) in
    let flist' := updN flist inum f' in
    (F * rep bxps sm ixp flist' ilist frees allocc mscache icache dblocks)%pred (list2nmem (updN m bn v)).
Proof.
(* skipped proof tokens: 607 *)
Admitted.
Theorem rep_safe_unused: forall F bxps sm ixp flist ilist m frees allocc mscache icache dblocks bn v flag,
    (F * rep bxps sm ixp flist ilist frees allocc mscache icache dblocks)%pred (list2nmem m) ->
    block_is_unused (pick_balloc frees flag) bn ->
    (F * rep bxps sm ixp flist ilist frees allocc mscache icache dblocks)%pred (list2nmem (updN m bn v)).
Proof.
(* skipped proof tokens: 660 *)
Admitted.
Theorem block_belong_to_file_bfdata_length : forall bxp sm ixp flist ilist frees allocc mscache icache dblocks m F inum off bn,
    (F * rep bxp sm ixp flist ilist frees allocc mscache icache dblocks)%pred m ->
    block_belong_to_file ilist bn inum off ->
    off < length (BFData (selN flist inum BFILE.bfile0)).
Proof.
(* skipped proof tokens: 140 *)
Admitted.
Definition synced_file f := mk_bfile (synced_list (map fst (BFData f))) (BFAttr f) (BFCache f).
Lemma add_nonzero_exfalso_helper2 : forall a b,
    a * valulen + b = 0 -> a <> 0 -> False.
Proof.
(* skipped proof tokens: 75 *)
Admitted.
Lemma file_match_init_ok : forall n,
    emp =p=> listmatch file_match (repeat bfile0 n) (repeat INODE.inode0 n).
Proof.
(* skipped proof tokens: 44 *)
Admitted.
Lemma file_match_no_dup: forall ilist flist F inum m,
    (F * listmatch file_match flist ilist)%pred m ->
    NoDup (map (@wordToNat addrlen) (INODE.IBlocks (selN ilist inum INODE.inode0))).
Proof.
(* skipped proof tokens: 139 *)
Admitted.
Lemma file_match_length: forall F flist ilist inum di df m,
    (F * listmatch file_match flist ilist)%pred m ->
    inum < length flist -> inum < length ilist ->
    length (INODE.IBlocks (selN ilist inum di)) = length (BFData (selN flist inum df)).
Proof.
(* skipped proof tokens: 74 *)
Admitted.
Lemma odd_nonzero : forall n,
    Nat.odd n = true -> n <> 0.
Proof.
(* skipped proof tokens: 25 *)
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
Proof.
(* skipped proof tokens: 11 *)
Admitted.
Lemma mscs_same_except_log_refl : forall mscs,
    mscs_same_except_log mscs mscs.
Proof.
(* skipped proof tokens: 11 *)
Admitted.
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
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Fact resolve_selN_vs0 : forall l i (d : valuset),
    d = ($0, nil) -> selN l i d = selN l i ($0, nil).
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Hint Rewrite resolve_selN_bfile0 using reflexivity : defaults.
Hint Rewrite resolve_selN_vs0 using reflexivity : defaults.
Lemma bfcache_emp: forall ilist flist,
    Forall (fun f => BFCache f = None) flist ->
    locked (cache_rep (BFcache.empty (Dcache_type * addr)) flist ilist).
Proof.
(* skipped proof tokens: 85 *)
Admitted.
Lemma bfcache_init : forall len ilist,
    locked (cache_rep (BFcache.empty _) (repeat bfile0 len) ilist).
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma bfcache_upd : forall mscache inum flist ilist F f d a,
    locked (cache_rep mscache flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep mscache (updN flist inum {| BFData := d; BFAttr := a; BFCache := BFCache f |}) ilist).
Proof.
(* skipped proof tokens: 89 *)
Admitted.
Lemma cache_ptsto_none'' : forall l start m idx,
    arrayN cache_ptsto start l m ->
    idx < start ->
    m idx = None.
Proof.
(* skipped proof tokens: 72 *)
Admitted.
Lemma cache_ptsto_none' : forall l start m idx def,
    arrayN cache_ptsto start l m ->
    idx < length l ->
    selN l idx def = None ->
    m (start + idx) = None.
Proof.
(* skipped proof tokens: 122 *)
Admitted.
Lemma cache_ptsto_none : forall l m idx def,
    arrayN cache_ptsto 0 l m ->
    idx < length l ->
    selN l idx def = None ->
    m idx = None.
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma cache_ptsto_none_find : forall l c idx def,
    arrayN cache_ptsto 0 l (BFM.mm _ c) ->
    idx < length l ->
    selN l idx def = None ->
    BFcache.find idx c = None.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma bfcache_find : forall c flist ilist inum f F,
    locked (cache_rep c flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    BFcache.find inum c = BFCache f.
Proof.
(* skipped proof tokens: 175 *)
Admitted.
Lemma bfcache_put : forall msc flist ilist inum c f F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep (BFcache.add inum c msc)
                      (updN flist inum {| BFData := BFData f; BFAttr := BFAttr f; BFCache := Some c |})
                      ilist).
Proof.
(* skipped proof tokens: 381 *)
Admitted.
Lemma bfcache_remove' : forall msc flist ilist inum f d a F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep (BFcache.remove inum msc)
                      (updN flist inum {| BFData := d; BFAttr := a; BFCache := None |})
                      ilist).
Proof.
(* skipped proof tokens: 385 *)
Admitted.
Lemma bfcache_remove : forall msc flist ilist inum f F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    BFData f = nil ->
    BFAttr f = attr0 ->
    locked (cache_rep (BFcache.remove inum msc) (updN flist inum bfile0) ilist).
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma rep_bfcache_remove : forall bxps sm ixp flist ilist frees allocc mscache icache dblocks inum f F,
    (F * inum |-> f)%pred (list2nmem flist) ->
    rep bxps sm ixp flist ilist frees allocc mscache icache dblocks =p=>
    rep bxps sm ixp (updN flist inum {| BFData := BFData f; BFAttr := BFAttr f; BFCache := None |}) ilist frees allocc
      (BFcache.remove inum mscache) icache dblocks.
Proof.
(* skipped proof tokens: 130 *)
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
Proof.
(* original proof tokens: 265 *)

(* No more tactics to try *)
Admitted.

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
(* skipped proof tokens: 872 *)
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
(* skipped proof tokens: 97 *)
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
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Definition treeseq_ilist_safe inum ilist1 ilist2 :=
    (forall off bn,
        block_belong_to_file ilist1 bn inum off ->
        block_belong_to_file ilist2 bn inum off) /\
    (forall i def,
        inum <> i -> selN ilist1 i def = selN ilist2 i def).
Lemma treeseq_ilist_safe_refl : forall inum ilist,
    treeseq_ilist_safe inum ilist ilist.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Lemma treeseq_ilist_safe_trans : forall inum ilist0 ilist1 ilist2,
    treeseq_ilist_safe inum ilist0 ilist1 ->
    treeseq_ilist_safe inum ilist1 ilist2 ->
    treeseq_ilist_safe inum ilist0 ilist2.
Proof.
(* skipped proof tokens: 40 *)
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
Proof.
(* skipped proof tokens: 287 *)
Admitted.
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
(* skipped proof tokens: 260 *)
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
Proof.
(* skipped proof tokens: 460 *)
Admitted.
Lemma grow_treeseq_ilist_safe: forall (ilist: list INODE.inode) ilist' inum a,
    inum < Datatypes.length ilist ->
    (arrayN_ex (ptsto (V:=INODE.inode)) ilist inum
     ✶ inum
       |-> {|
           INODE.IBlocks := INODE.IBlocks (selN ilist inum INODE.inode0) ++ [$ (a)];
           INODE.IAttr := INODE.IAttr (selN ilist inum INODE.inode0) |})%pred (list2nmem ilist') ->
    treeseq_ilist_safe inum ilist ilist'.
Proof.
(* skipped proof tokens: 136 *)
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
Proof.
(* skipped proof tokens: 906 *)
Admitted.
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
(* skipped proof tokens: 1089 *)
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
Proof.
(* skipped proof tokens: 19 *)
Admitted.
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
(* skipped proof tokens: 21 *)
Admitted.
Lemma block_belong_to_file_off_ok : forall Fm Fi sm bxp ixp flist ilist frees cms mscache icache dblocks inum off f m,
    (Fm * rep bxp sm ixp flist ilist frees cms mscache icache dblocks)%pred m ->
    (Fi * inum |-> f)%pred (list2nmem flist) ->
    off < Datatypes.length (BFData f) -> 
    block_belong_to_file ilist # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0) inum off.
Proof.
(* skipped proof tokens: 184 *)
Admitted.
Lemma block_belong_to_file_ok : forall Fm Fi Fd bxp sm ixp flist ilist frees cms mscache icache dblocks inum off f vs m,
    (Fm * rep bxp sm ixp flist ilist frees cms mscache icache dblocks)%pred m ->
    (Fi * inum |-> f)%pred (list2nmem flist) ->
    (Fd * off |-> vs)%pred (list2nmem (BFData f)) ->
    block_belong_to_file ilist # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0) inum off.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Definition diskset_was (ds0 ds : diskset) := ds0 = ds \/ ds0 = (ds!!, nil).
Theorem d_in_diskset_was : forall d ds ds',
    d_in d ds ->
    diskset_was ds ds' ->
    d_in d ds'.
Proof.
(* skipped proof tokens: 38 *)
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
(* skipped proof tokens: 722 *)
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
Proof.
(* skipped proof tokens: 643 *)
Admitted.
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
(* skipped proof tokens: 87 *)
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
(* skipped proof tokens: 109 *)
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
Proof.
(* skipped proof tokens: 164 *)
Admitted.
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
Proof.
(* skipped proof tokens: 179 *)
Admitted.
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
Proof.
(* skipped proof tokens: 223 *)
Admitted.
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
(* skipped proof tokens: 135 *)
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
Proof.
(* skipped proof tokens: 585 *)
Admitted.
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
Proof.
(* skipped proof tokens: 40 *)
Admitted.
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
Proof.
(* skipped proof tokens: 130 *)
Admitted.
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
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma fsynced_synced_file : forall f,
    FSynced (synced_file f).
Proof.
(* skipped proof tokens: 98 *)
Admitted.
Lemma arrayN_synced_list_fsynced : forall f l,
    arrayN (@ptsto _ addr_eq_dec _) 0 (synced_list l) (list2nmem (BFData f)) ->
    FSynced f.
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Lemma file_crash_attr : forall f f',
    file_crash f f' -> BFAttr f' = BFAttr f.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma file_crash_possible_crash_list : forall f f',
    file_crash f f' ->
    possible_crash_list (BFData f) (map fst (BFData f')).
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma file_crash_data_length : forall f f',
    file_crash f f' -> length (BFData f) = length (BFData f').
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma file_crash_synced : forall f f',
    file_crash f f' ->
    FSynced f ->
    BFData f = BFData f' /\
    BFAttr f = BFAttr f'.
Proof.
(* skipped proof tokens: 126 *)
Admitted.
Lemma file_crash_fsynced : forall f f',
    file_crash f f' ->
    FSynced f'.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma file_crash_ptsto : forall f f' vs F a,
    file_crash f f' ->
    (F * a |-> vs)%pred (list2nmem (BFData f)) ->
    (exists v, [[ In v (vsmerge vs) ]]  *
       crash_xform F * a |=> v)%pred (list2nmem (BFData f')).
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma xform_file_match : forall f ino,
    crash_xform (file_match f ino) =p=> 
      exists f', [[ file_crash f f' ]] * file_match f' ino.
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Lemma xform_file_list : forall fs inos,
    crash_xform (listmatch file_match fs inos) =p=>
      exists fs', [[ flist_crash fs fs' ]] * listmatch file_match fs' inos.
Proof.
(* skipped proof tokens: 154 *)
Admitted.
Lemma flist_crash_caches_cleared: forall flist flist',
    flist_crash flist flist' ->
    Forall (fun f => BFCache f = None) flist'.
Proof.
(* skipped proof tokens: 47 *)
Admitted.
Lemma smrep_single_helper_sm_sync_all: forall dblocks inum ino sm,
    smrep_single_helper dblocks inum ino sm ->
    smrep_single_helper (Map.empty _ ) inum ino (sm_sync_all sm).
Proof.
(* skipped proof tokens: 179 *)
Admitted.
Lemma arrayN_smrep_single_helper_sm_sync_all: forall dblocks ilist i sm,
    arrayN (smrep_single_helper dblocks) i ilist sm ->
    arrayN (smrep_single_helper (Map.empty _)) i ilist (sm_sync_all sm).
Proof.
(* skipped proof tokens: 47 *)
Admitted.
Lemma smrep_sm_sync_all: forall frees dblocks ilist sm,
    smrep frees dblocks ilist sm ->
    smrep frees (Map.empty _) ilist (SyncedMem.sm_sync_all sm).
Proof.
(* skipped proof tokens: 82 *)
Admitted.
Lemma sep_star_smrep_sm_synced: forall IFs ilist frees dblocks sm Fs,
    sm_sync_invariant IFs ->
    ((Fs * IFs) * smrep frees dblocks ilist)%pred sm ->
    ((any * IFs) * smrep frees (Map.empty _) ilist)%pred sm_synced.
Proof.
(* skipped proof tokens: 85 *)
Admitted.
Lemma xform_rep : forall bxp ixp flist ilist sm frees allocc mscache icache dblocks,
    crash_xform (rep bxp sm ixp flist ilist frees allocc mscache icache dblocks) =p=>
      exists flist', [[ flist_crash flist flist' ]] *
      rep bxp sm_synced ixp flist' ilist frees allocc (BFcache.empty _) icache (Map.empty _).
Proof.
(* skipped proof tokens: 99 *)
Admitted.
Lemma xform_file_match_ptsto : forall F a vs f ino,
    (F * a |-> vs)%pred (list2nmem (BFData f)) ->
    crash_xform (file_match f ino) =p=>
      exists f' v, file_match f' ino *
      [[ In v (vsmerge vs) ]] *
      [[ (crash_xform F * a |=> v)%pred (list2nmem (BFData f')) ]].
Proof.
(* skipped proof tokens: 128 *)
Admitted.
Lemma xform_rep_file : forall F bxp ixp fs f i ilist sm frees allocc mscache icache dblocks,
    (F * i |-> f)%pred (list2nmem fs) ->
    crash_xform (rep bxp sm ixp fs ilist frees allocc mscache icache dblocks) =p=>
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp sm_synced ixp fs' ilist frees allocc (BFcache.empty _) icache (Map.empty _) *
      [[ (arrayN_ex (@ptsto _ addr_eq_dec _) fs' i * i |-> f')%pred (list2nmem fs') ]].
Proof.
(* skipped proof tokens: 283 *)
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
(* skipped proof tokens: 56 *)
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
(* skipped proof tokens: 64 *)
Admitted.
Lemma flist_crash_clear_caches : forall f f',
    flist_crash f f' ->
    clear_caches f' = f'.
Proof.
(* skipped proof tokens: 76 *)
Admitted.
Lemma freepred_file_crash : forall f f',
    file_crash f f' -> freepred f -> freepred f'.
Proof.
(* skipped proof tokens: 61 *)
Admitted.
Lemma freepred_bfile0 : freepred bfile0.
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Hint Resolve freepred_bfile0.
End BFILE.
Ltac msalloc_eq := BFILE.msalloc_eq.
