Require Import Hashmap.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Classes.SetoidTactics.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import Lia.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import Eqdep_dec.
Require Import WordAuto.
Require Import Cache.
Require Import Idempotent.
Require Import ListUtils.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import MemLog.
Require Import MapUtils.
Require Import ListPred.
Require Import LogReplay.
Require Import GroupLog.
Require Import DiskSet.
Require Import SyncedMem.
Require Import RelationClasses.
Require Import Morphisms.
Import ListNotations.
Set Implicit Arguments.
Parameter should_flushall : bool.
Module LOG.
Import AddrMap LogReplay.
Record mstate := mk_mstate {
    MSTxn   : valumap;         
    MSGLog  : GLog.mstate    
  }.
Definition memstate := (mstate * cachestate)%type.
Definition mk_memstate mm (ll : GLog.memstate) : memstate :=
    (mk_mstate mm (fst ll), (snd ll)).
Definition mk_memstate0 (cs: cachestate) := (mk_mstate vmap0 GLog.mk_memstate0, cs).
Definition MSCache (ms : memstate) := snd ms.
Definition MSLL (ms : memstate) : GLog.memstate := (MSGLog (fst ms), (snd ms)).
Definition readOnly (ms ms' : memstate) :=
    (GLog.readOnly (MSLL ms) (MSLL ms') /\
     Map.Empty (MSTxn (fst ms)) /\
     Map.Empty (MSTxn (fst ms'))).
Inductive state :=
  | NoTxn (cur : diskset)
  

  | ActiveTxn (old : diskset) (cur : diskstate)
  

  | FlushingTxn (new : diskset)
  

  | RollbackTxn (old : diskstate)
  | RecoveringTxn (old : diskstate)
  .
Definition rep_inner xp st ms sm hm :=
  let '(cm, mm) := (MSTxn ms, MSGLog ms) in
  (match st with
    | NoTxn ds =>
      [[ Map.Empty cm ]] *
      [[ sm_ds_valid sm ds ]] *
      GLog.rep xp (GLog.Cached ds) mm hm
    | ActiveTxn ds cur =>
      [[ map_valid cm ds!! ]] *
      [[ map_replay cm ds!! cur ]] *
      [[ sm_ds_valid sm (pushd cur ds) ]] *
      GLog.rep xp (GLog.Cached ds) mm hm
    | FlushingTxn ds =>
      [[ sm_ds_valid sm ds ]] *
      GLog.would_recover_any xp ds hm
    | RollbackTxn d =>
      [[ Map.Empty cm ]] *
      [[ sm_ds_valid sm (d, nil) ]] *
      GLog.rep xp (GLog.Rollback d) mm hm
    | RecoveringTxn d =>
      [[ Map.Empty cm ]] *
      [[ sm_ds_valid sm (d, nil) ]] *
      GLog.rep xp (GLog.Recovering d) mm hm
  end)%pred.
Definition rep xp F st ms sm hm :=
    (exists raw, BUFCACHE.rep (snd ms) raw *
      [[ (F * rep_inner xp st (fst ms) sm hm)%pred raw ]])%pred.
Definition intact xp F ds sm hm :=
    (exists ms,
      rep xp F (NoTxn ds) ms sm hm \/
      exists new, rep xp F (ActiveTxn ds new) ms sm hm)%pred.
Definition recover_any xp F ds hm :=
    (exists ms sm, rep xp F (FlushingTxn ds) ms sm hm)%pred.
Theorem sync_invariant_rep : forall xp F st ms sm hm,
    sync_invariant F ->
    sync_invariant (rep xp F st ms sm hm).
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Hint Resolve sync_invariant_rep.
Theorem sync_invariant_intact : forall xp F ds sm hm,
    sync_invariant F ->
    sync_invariant (intact xp F ds sm hm).
Proof.
(* skipped proof tokens: 13 *)
Admitted.
Theorem sync_invariant_recover_any : forall xp F ds hm,
    sync_invariant F ->
    sync_invariant (recover_any xp F ds hm).
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Hint Resolve sync_invariant_intact sync_invariant_recover_any.
Lemma active_intact : forall xp F old new ms sm hm,
    rep xp F (ActiveTxn old new) ms sm hm =p=> intact xp F old sm hm.
Proof.
(* skipped proof tokens: 13 *)
Admitted.
Lemma notxn_intact : forall xp F old ms sm hm,
    rep xp F (NoTxn old) ms sm hm =p=> intact xp F old sm hm.
Proof.
(* skipped proof tokens: 13 *)
Admitted.
Lemma flushing_any : forall xp F ds ms sm hm,
    rep xp F (FlushingTxn ds) ms sm hm =p=> recover_any xp F ds hm.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Lemma intact_any : forall xp F ds sm hm,
    intact xp F ds sm hm =p=> recover_any xp F ds hm.
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Lemma notxn_any : forall xp F ds ms sm hm,
    rep xp F (NoTxn ds) ms sm hm =p=> recover_any xp F ds hm.
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma active_notxn : forall xp F old new ms sm hm,
    rep xp F (ActiveTxn old new) ms sm hm =p=>
    rep xp F (NoTxn old) (mk_mstate vmap0 (MSGLog (fst ms)), (snd ms)) sm hm.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma active_dset_match_pimpl : forall xp F ds d hm sm ms,
    rep xp F (ActiveTxn ds d) ms sm hm <=p=>
    rep xp F (ActiveTxn ds d) ms sm hm *
      [[ exists gms, GLog.dset_match xp (GLog.effective ds (length gms)) gms ]].
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Lemma notxn_dset_match_pimpl : forall xp F ds hm sm ms,
    rep xp F (NoTxn ds) ms sm hm <=p=>
    rep xp F (NoTxn ds) ms sm hm *
      [[ exists gms, GLog.dset_match xp (GLog.effective ds (length gms)) gms ]].
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Lemma rep_inner_hashmap_subset : forall xp ms hm sm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep_inner xp st ms sm hm
        =p=> rep_inner xp st ms sm hm'.
Proof.
(* skipped proof tokens: 61 *)
Admitted.
Lemma rep_hashmap_subset : forall xp F ms hm sm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp F st ms sm hm
        =p=> rep xp F st ms sm hm'.
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Lemma intact_hashmap_subset : forall xp F ds hm sm hm',
    (exists l, hashmap_subset l hm hm')
    -> intact xp F ds sm hm
        =p=> intact xp F ds sm hm'.
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Lemma rep_inner_notxn_pimpl : forall xp d ms sm hm,
    rep_inner xp (NoTxn (d, nil)) ms sm hm
    =p=> exists ms', rep_inner xp (RecoveringTxn d) ms' sm hm.
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma rep_inner_rollbacktxn_pimpl : forall xp d ms sm hm,
    rep_inner xp (RollbackTxn d) ms sm hm
    =p=> rep_inner xp (RecoveringTxn d) ms sm hm.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma readOnlyMapEmpty : forall ms,
    (exists ms0, readOnly ms0 ms) -> Map.Empty (MSTxn (fst ms)).
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Hint Resolve readOnlyMapEmpty.
Theorem readOnlyLL : forall ms ms',
    GLog.readOnly (MSLL ms) (MSLL ms') ->
    Map.Empty (MSTxn (fst ms)) ->
    Map.Empty (MSTxn (fst ms')) ->
    readOnly ms ms'.
Proof.
(* skipped proof tokens: 11 *)
Admitted.
Hint Resolve readOnlyLL.
Theorem readOnlyLL' : forall ms mstxn' msll',
    GLog.readOnly (MSLL ms) msll' ->
    Map.Empty (MSTxn (fst ms)) ->
    MSTxn (fst ms) = mstxn' ->
    readOnly ms (mk_memstate mstxn' msll').
Proof.
(* skipped proof tokens: 16 *)
Admitted.
Hint Resolve readOnlyLL'.
Theorem readOnly_refl : forall ms,
    Map.Empty (MSTxn (fst ms)) ->
    readOnly ms ms.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Hint Resolve readOnly_refl.
Theorem readOnly_trans : forall ms ms' ms'',
    readOnly ms ms' -> readOnly ms' ms'' -> readOnly ms ms''.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Hint Resolve readOnly_trans.
Definition init xp cs :=
    mm <- GLog.init xp cs;
    Ret (mk_memstate vmap0 mm).
Definition begin (xp : log_xparams) (ms : memstate) :=
    Ret ms.
Definition abort (xp : log_xparams) ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate vmap0 mm).
Definition write (xp : log_xparams) a v ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate (Map.add a v cm) mm).
Definition read xp a ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    match Map.find a cm with
    | Some v =>  Ret ^(ms, v)
    | None =>
        let^ (mm', v) <- GLog.read xp a mm;
        Ret ^(mk_memstate cm mm', v)
    end.
Definition commit xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    let^ (mm', r) <- GLog.submit xp (Map.elements cm) mm;
    If (bool_dec should_flushall true) {
      mm' <- GLog.flushall_noop xp mm';
      Ret ^(mk_memstate vmap0 mm', r)
    } else {
      Ret ^(mk_memstate vmap0 mm', r)
    }.
Definition commit_ro (xp : log_xparams) ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate vmap0 mm).
Definition dwrite (xp : log_xparams) a v ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    let cm' := Map.remove a cm in
    mm' <- GLog.dwrite xp a v mm;
    Ret (mk_memstate cm' mm').
Definition dsync xp a ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dsync xp a mm;
    Ret (mk_memstate cm mm').
Definition flushsync xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushsync xp mm;
    Ret (mk_memstate cm mm').
Definition flushall xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushall xp mm;
    Ret (mk_memstate cm mm').
Definition flushsync_noop xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushsync_noop xp mm;
    Ret (mk_memstate cm mm').
Definition flushall_noop xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushall_noop xp mm;
    Ret (mk_memstate cm mm').
Definition sync_cache xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.sync_cache xp mm;
    Ret (mk_memstate cm mm').
Definition recover xp cs :=
    mm <- GLog.recover xp cs;
    Ret (mk_memstate vmap0 mm).
Local Hint Unfold rep rep_inner map_replay: hoare_unfold.
Arguments GLog.rep: simpl never.
Hint Extern 0 (okToUnify (GLog.rep _ _ _ _) (GLog.rep _ _ _ _)) => constructor : okToUnify.
Ltac dems := eauto; repeat match goal with
  | [ H : eq _ (mk_memstate _ _) |- _ ] =>
     inversion H; subst; simpl; clear H
  | [ |- Map.Empty vmap0 ] => apply Map.empty_1
  | [ |- map_valid vmap0 _ ] => apply map_valid_map0
  | [ H : Map.Empty ?m |- map_valid ?m _ ] => apply map_valid_empty
  end; eauto.
Local Hint Resolve KNoDup_map_elements.
Local Hint Resolve MapProperties.eqke_equiv.
Lemma possible_crash_list2nmem_synced: forall d' d,
    possible_crash d (list2nmem d') ->
    Forall (fun v => snd v = nil) d'.
Proof.
(* skipped proof tokens: 157 *)
Admitted.
Lemma sm_vs_valid_crash_xform: forall ds sm d n,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    sm_ds_valid sm ds ->
    sm_vs_valid sm d.
Proof.
(* skipped proof tokens: 75 *)
Admitted.
Lemma sm_vs_valid_sm_synced: forall d d',
    crash_xform (diskIs (list2nmem d')) (list2nmem d) ->
    sm_vs_valid sm_synced d.
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Lemma listpred_ptsto_combine_ex : forall AT AEQ V a b,
    length a = length b ->
    listpred (pprd (fun y x => @ptsto AT AEQ V x y)) (List.combine b a) =p=> listpred (fun x => x |->?) a.
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma listpred_ptsto_combine_same : forall AT AEQ V f k a b,
    length a = length b ->
    (forall (x : AT) (y : V), In (y, x) (filter (fun x => f (snd x)) (List.combine b a)) -> y = k) ->
    listpred (pprd (fun y x => @ptsto AT AEQ V x y)) (filter (fun x => f (snd x)) (List.combine b a)) =p=> listpred (fun x => x |-> k) (filter f a).
Proof.
(* skipped proof tokens: 135 *)
Admitted.
Lemma listpred_ptsto_combine_same' : forall AT AEQ V (F : (V * AT) -> @pred AT AEQ V) k a b,
    length a = length b ->
    (forall x y, In (y, x) (List.combine b a) -> F (y, x) =p=> x |-> k) ->
    listpred F (List.combine b a) =p=> listpred (fun x => x |-> k) a.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Local Hint Resolve sm_vs_valid_upd_synced vs_synced_updN_synced
     sm_ds_valid_synced sm_ds_valid_pushd_l sm_ds_valid_pushd_r
     sm_ds_valid_pushd sm_ds_valid_dsupd sm_ds_valid_pushd_latest
     sm_ds_valid_dssync list2nmem_inbound ptsto_upd'
     sm_ds_valid_dsupd_vecs sm_ds_valid_dssync_vecs.
Definition init_ok : forall xp cs,
    {< F l d m,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * arrayS (DataStart xp) m * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * DiskLogHash.PaddedLog.DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: ms exists d sm l,
          rep xp F (NoTxn (d, nil)) ms sm hm' *
          [[[ d ::: arrayN (@ptsto _ _ _) 0 d ]]] *
          [[ arrayN (@ptsto _ _ _) 0 l sm ]] * [[ length l = length d ]] *
          [[ length d = (LogHeader xp) - (DataStart xp) ]]
    XCRASH:hm_crash any
    >} init xp cs.
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Theorem begin_ok: forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm
    POST:hm' RET:r
      rep xp F (ActiveTxn ds ds!!) r sm hm' *
      [[ readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' sm hm'
    >} begin xp ms.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Theorem abort_ok : forall xp ms,
    {< F ds sm m,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm
    POST:hm' RET:r
      rep xp F (NoTxn ds) r sm hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' sm hm'
    >} abort xp ms.
Proof.
(* skipped proof tokens: 111 *)
Admitted.
Theorem read_ok: forall xp ms a,
    {< F Fm ds sm m v,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[[ m ::: Fm * a |-> v ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' sm hm' * [[ r = fst v ]] *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' sm hm'
    >} read xp a ms.
Proof.
(* original proof tokens: 129 *)

(* No more tactics to try *)
Admitted.

Theorem write_ok : forall xp ms a v,
    {< F Fm ds m sm vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm * [[ a <> 0 ]] *
      [[[ m ::: (Fm * a |-> vs) ]]]
    POST:hm' RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' sm hm' *
      [[[ m' ::: (Fm * a |-> (v, nil)) ]]]
    CRASH:hm'
      exists m' ms', rep xp F (ActiveTxn ds m') ms' sm hm'
    >} write xp a v ms.
Proof.
(* skipped proof tokens: 131 *)
Admitted.
Set Regular Subst Tactic.
Theorem dwrite_ok : forall xp ms a v,
    {< F Fm Fs ds sm vs,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[[ ds!! ::: (Fm * a |-> vs) ]]] *
      [[ (Fs * a |->?)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: (Fm * a |-> (v, vsmerge vs)) ]]] *
      [[ (Fs * a |-> false)%pred sm' ]] *
      [[ ds' = dsupd ds a (v, vsmerge vs) ]]
    XCRASH:hm'
      recover_any xp F ds hm' \/
      recover_any xp F (dsupd ds a (v, vsmerge vs)) hm'
    >} dwrite xp a v ms.
Proof.
(* skipped proof tokens: 137 *)
Admitted.
Theorem dsync_ok : forall xp ms a,
    {< F Fm Fs ds sm vs,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[[ ds!! ::: (Fm * a |-> vs) ]]] *
      [[ (Fs * a |->?)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[ ds' = dssync ds a ]] *
      [[ (Fs * a |-> true)%pred sm' ]]
    CRASH:hm'
      recover_any xp F ds hm'
    >} dsync xp a ms.
Proof.
(* skipped proof tokens: 77 *)
Admitted.
Theorem flushall_ok : forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' sm hm'
    XCRASH:hm'
      recover_any xp F ds hm'
    >} flushall xp ms.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Theorem flushsync_ok : forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' sm hm'
    XCRASH:hm'
      recover_any xp F ds hm'
    >} flushsync xp ms.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Theorem flushall_noop_ok : forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn ds) ms' sm hm'
    XCRASH:hm'
      recover_any xp F ds hm'
    >} flushall_noop xp ms.
Proof.
(* skipped proof tokens: 38 *)
Admitted.
Theorem flushsync_noop_ok : forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn ds) ms' sm hm'
    XCRASH:hm'
      recover_any xp F ds hm'
    >} flushsync_noop xp ms.
Proof.
(* skipped proof tokens: 38 *)
Admitted.
Hint Extern 1 ({{_}} Bind (flushall_noop _ _) _) => apply flushall_noop_ok : prog.
Hint Extern 1 ({{_}} Bind (flushsync_noop _ _) _) => apply flushsync_noop_ok : prog.
Local Hint Resolve map_valid_log_valid length_elements_cardinal_gt map_empty_vmap0.
Theorem commit_ok : forall xp ms,
    {< F sm ds m,
     PRE:hm  rep xp F (ActiveTxn ds m) ms sm hm *
            [[ sync_invariant F ]]
     POST:hm' RET:^(ms',r)
          ([[ r = true ]] *
            rep xp F (NoTxn (pushd m ds)) ms' sm hm') \/
          ([[ r = false ]] *
            [[ Map.cardinal (MSTxn (fst ms)) > (LogLen xp) ]] *
            rep xp F (NoTxn ds) ms' sm hm')
     XCRASH:hm' recover_any xp F (pushd m ds) hm'
    >} commit xp ms.
Proof.
(* skipped proof tokens: 120 *)
Admitted.
Theorem commit_ro_ok : forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm
    POST:hm' RET:r
      rep xp F (NoTxn ds) r sm hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' sm hm'
    >} commit_ro xp ms.
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Definition after_crash xp F ds cs hm :=
    (exists raw, BUFCACHE.rep cs raw *
     [[ ( exists d n ms, [[ n <= length (snd ds) ]] *
       F * (rep_inner xp (NoTxn (d, nil)) ms sm_synced hm \/
            rep_inner xp (RollbackTxn d) ms sm_synced hm) *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     )%pred raw ]])%pred.
Definition before_crash xp F ds hm :=
    (exists cs raw, BUFCACHE.rep cs raw *
     [[ ( exists d n ms, [[ n <= length (snd ds) ]] *
       F * (rep_inner xp (RecoveringTxn d) ms sm_synced hm) *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     )%pred raw ]])%pred.
Theorem sync_invariant_after_crash : forall xp F ds cs hm,
    sync_invariant F ->
    sync_invariant (after_crash xp F ds cs hm).
Proof.
(* skipped proof tokens: 16 *)
Admitted.
Theorem sync_invariant_before_crash : forall xp F ds hm,
    sync_invariant F ->
    sync_invariant (before_crash xp F ds hm).
Proof.
(* skipped proof tokens: 16 *)
Admitted.
Hint Resolve sync_invariant_after_crash sync_invariant_before_crash.
Theorem recover_ok: forall xp cs,
    {< F ds,
    PRE:hm
      after_crash xp F ds cs hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      exists d n, [[ n <= length (snd ds) ]] *
      rep xp F (NoTxn (d, nil)) ms' sm_synced hm' *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
    XCRASH:hm'
      before_crash xp F ds hm'
    >} recover xp cs.
Proof.
(* skipped proof tokens: 226 *)
Admitted.
Lemma crash_xform_before_crash : forall xp F ds hm,
    crash_xform (before_crash xp F ds hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs hm.
Proof.
(* skipped proof tokens: 234 *)
Admitted.
Lemma crash_xform_any : forall xp F ds hm,
    crash_xform (recover_any xp F ds hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs hm.
Proof.
(* skipped proof tokens: 192 *)
Admitted.
Lemma after_crash_notxn : forall xp cs F ds hm,
    after_crash xp F ds cs hm =p=>
      exists d n ms, [[ n <= length (snd ds) ]] *
      (rep xp F (NoTxn (d, nil)) ms sm_synced hm \/
        rep xp F (RollbackTxn d) ms sm_synced hm) *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]].
Proof.
(* skipped proof tokens: 76 *)
Admitted.
Lemma after_crash_notxn_singular : forall xp cs F d hm,
    after_crash xp F (d, nil) cs hm =p=>
      exists d' ms, (rep xp F (NoTxn (d', nil)) ms sm_synced hm \/
                      rep xp F (RollbackTxn d') ms sm_synced hm) *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma after_crash_idem : forall xp F ds cs hm,
    crash_xform (after_crash xp F ds cs hm) =p=>
     exists cs', after_crash xp (crash_xform F) ds cs' hm.
Proof.
(* skipped proof tokens: 286 *)
Admitted.
Lemma after_crash_idem' : forall xp d ms sm hm (F : rawpred),
    F (list2nmem d) ->
    crash_xform (rep_inner xp (NoTxn (d, nil)) ms sm hm
              \/ rep_inner xp (RollbackTxn d) ms sm hm) =p=>
    exists d' ms',(rep_inner xp (NoTxn (d', nil)) ms' sm_synced hm \/
                   rep_inner xp (RollbackTxn d') ms' sm_synced hm) *
                   [[ (crash_xform F) (list2nmem d') ]].
Proof.
(* skipped proof tokens: 141 *)
Admitted.
Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _ _ _) (LOG.rep_inner _ _ _ _ _)) => constructor : okToUnify.
Instance rep_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> eq ==> pimpl) rep.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Instance intact_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> pimpl) intact.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Instance after_crash_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> pimpl) after_crash.
Proof.
(* skipped proof tokens: 101 *)
Admitted.
Lemma notxn_after_crash_diskIs : forall xp F n ds d ms sm hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    rep xp F (NoTxn (d, nil)) ms sm hm =p=> after_crash xp F ds (snd ms) hm.
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma rollbacktxn_after_crash_diskIs : forall xp F n d ds ms sm hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    rep xp F (RollbackTxn d) ms sm hm =p=> after_crash xp F ds (snd ms) hm.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Definition idempred xp F ds hm :=
    (recover_any xp F ds hm \/
      before_crash xp F ds hm \/
      exists cs, after_crash xp F ds cs hm)%pred.
Theorem sync_invariant_idempred : forall xp F ds hm,
    sync_invariant F ->
    sync_invariant (idempred xp F ds hm).
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Hint Resolve sync_invariant_idempred.
Theorem idempred_idem : forall xp F ds hm,
    crash_xform (idempred xp F ds hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs hm.
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Theorem recover_any_idempred : forall xp F ds hm,
    recover_any xp F ds hm =p=> idempred xp F ds hm.
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Theorem intact_idempred : forall xp F ds sm hm,
    intact xp F ds sm hm =p=> idempred xp F ds hm.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Theorem notxn_idempred : forall xp F ds ms sm hm,
    rep xp F (NoTxn ds) ms sm hm =p=> idempred xp F ds hm.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Theorem active_idempred : forall xp F ds ms d sm hm,
    rep xp F (ActiveTxn ds d) ms sm hm =p=> idempred xp F ds hm.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Theorem after_crash_idempred : forall xp F ds cs hm,
    after_crash xp F ds cs hm =p=> idempred xp F ds hm.
Proof.
(* original proof tokens: 21 *)
eapply pimpl_refl.
(* No more tactics to try *)
Admitted.

Theorem before_crash_idempred : forall xp F ds hm,
    before_crash xp F ds hm =p=> idempred xp F ds hm.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Instance idempred_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> pimpl) idempred.
Proof.
(* original proof tokens: 181 *)

(* No more tactics to try *)
Admitted.

Theorem crash_xform_intact : forall xp F ds sm hm,
    crash_xform (intact xp F ds sm hm) =p=>
      exists ms d n, rep xp (crash_xform F) (NoTxn (d, nil)) ms sm_synced hm *
        [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] *
        [[ n <= length (snd ds) ]].
Proof.
(* skipped proof tokens: 183 *)
Admitted.
Theorem crash_xform_idempred : forall xp F ds hm,
    crash_xform (idempred xp F ds hm) =p=>
      exists ms d n,
        (rep xp (crash_xform F) (NoTxn (d, nil)) ms sm_synced hm \/
          rep xp (crash_xform F) (RollbackTxn d) ms sm_synced hm) *
        [[ n <= length (snd ds) ]] *
        [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]].
Proof.
(* skipped proof tokens: 702 *)
Admitted.
Hint Resolve active_intact flushing_any.
Hint Extern 0 (okToUnify (intact _ _ _ _) (intact _ _ _ _)) => constructor : okToUnify.
Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (begin _ _) _) => apply begin_ok : prog.
Hint Extern 1 ({{_}} Bind (abort _ _) _) => apply abort_ok : prog.
Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (write _ _ _ _) _) => apply write_ok : prog.
Hint Extern 1 ({{_}} Bind (commit _ _) _) => apply commit_ok : prog.
Hint Extern 1 ({{_}} Bind (commit_ro _ _) _) => apply commit_ro_ok : prog.
Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
Hint Extern 1 ({{_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
Hint Extern 1 ({{_}} Bind (flushall _ _) _) => apply flushall_ok : prog.
Hint Extern 1 ({{_}} Bind (flushsync _ _) _) => apply flushsync_ok : prog.
Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.
Definition read_array xp a i ms :=
    let^ (ms, r) <- read xp (a + i) ms;
    Ret ^(ms, r).
Definition write_array xp a i v ms :=
    ms <- write xp (a + i) v ms;
    Ret ms.
Notation arrayP := (arrayN (@ptsto _ addr_eq_dec _)).
Theorem read_array_ok : forall xp ms a i,
    {< F Fm ds m sm vs,
    PRE:hm   rep xp F (ActiveTxn ds m) ms sm hm *
          [[ i < length vs]] *
          [[[ m ::: Fm * arrayP a vs ]]]
    POST:hm' RET:^(ms', r)
          rep xp F (ActiveTxn ds m) ms' sm hm' *
          [[ r = fst (selN vs i ($0, nil)) ]] *
          [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm' exists ms',
          rep xp F (ActiveTxn ds m) ms' sm hm'
    >} read_array xp a i ms.
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Theorem write_array_ok : forall xp a i v ms,
    {< F Fm ds sm m vs,
    PRE:hm   rep xp F (ActiveTxn ds m) ms sm hm *
          [[[ m ::: Fm * arrayP a vs ]]] *
          [[ i < length vs /\ a <> 0 ]]
    POST:hm' RET:ms' exists m',
          rep xp F (ActiveTxn ds m') ms' sm hm' *
          [[[ m' ::: Fm * arrayP a (updN vs i (v, nil)) ]]]
    CRASH:hm' exists m' ms',
          rep xp F (ActiveTxn ds m') ms' sm hm'
    >} write_array xp a i v ms.
Proof.
(* skipped proof tokens: 98 *)
Admitted.
Hint Extern 1 ({{_}} Bind (read_array _ _ _ _) _) => apply read_array_ok : prog.
Hint Extern 1 ({{_}} Bind (write_array _ _ _ _ _) _) => apply write_array_ok : prog.
Hint Extern 0 (okToUnify (rep _ _ _ ?a _ _) (rep _ _ _ ?a _ _)) => constructor : okToUnify.
Definition read_range A xp a nr (vfold : A -> valu -> A) v0 ms :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ F Fm crash ds sm m vs ms0 ]
    Loopvar [ ms pf ]
    Invariant
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) v0 ]] *
      [[ (exists ms00, readOnly ms00 ms0) -> readOnly ms0 ms ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array xp a i ms;
      Ret ^(ms, vfold pf v)
    Rof ^(ms, v0);
    Ret ^(ms, r).
Definition write_range xp a l ms :=
    let^ (ms) <- ForN i < length l
    Hashmap hm
    Ghost [ F Fm crash ds sm vs ]
    Loopvar [ ms ]
    Invariant
      exists m, rep xp F (ActiveTxn ds m) ms sm hm *
      [[[ m ::: (Fm * arrayP a (vsupsyn_range vs (firstn i l))) ]]]
    OnCrash crash
    Begin
      ms <- write_array xp a i (selN l i $0) ms;
      Ret ^(ms)
    Rof ^(ms);
    Ret ms.
Theorem read_range_ok : forall A xp a nr vfold (v0 : A) ms,
    {< F Fm ds sm m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[ nr <= length vs ]] *
      [[[ m ::: (Fm * arrayP a vs) ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' sm hm' *
      [[ r = fold_left vfold (firstn nr (map fst vs)) v0 ]] *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' sm hm'
    >} read_range xp a nr vfold v0 ms.
Proof.
(* skipped proof tokens: 216 *)
Admitted.
Lemma firstn_vsupsyn_range_firstn_S : forall i vs l,
    i < length l ->
    firstn i (vsupsyn_range vs (firstn (S i) l)) =
    firstn i (vsupsyn_range vs (firstn i l)).
Proof.
(* skipped proof tokens: 94 *)
Admitted.
Lemma skip_vsupsyn_range_skip_S : forall i vs l,
    i < length l -> length l <= length vs ->
    skipn (S i) (vsupsyn_range vs (firstn (S i) l)) =
    skipn (S i) (vsupsyn_range vs (firstn i l)).
Proof.
(* skipped proof tokens: 87 *)
Admitted.
Lemma sep_star_reorder_helper1 : forall AT AEQ V (a b c d : @pred AT AEQ V),
    ((a * b * d) * c) =p=> (a * ((b * c) * d)).
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma vsupsyn_range_progress : forall l a m vs,
    m < length l -> length l <= length vs ->
    arrayP a (updN (vsupsyn_range vs (firstn m l)) m (selN l m $0, nil)) =p=>
    arrayP a (vsupsyn_range vs (firstn (S m) l)).
Proof.
(* skipped proof tokens: 132 *)
Admitted.
Lemma write_range_length_ok : forall F a i ms d vs,
    i < length vs ->
    (F ✶ arrayP a vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    a + i < length d.
Proof.
(* skipped proof tokens: 48 *)
Admitted.
Theorem write_range_ok : forall xp a l ms,
    {< F Fm ds m sm vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ a <> 0 /\ length l <= length vs ]]
    POST:hm' RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' sm hm' *
      [[[ m' ::: (Fm * arrayP a (vsupsyn_range vs l)) ]]]
    CRASH:hm' exists ms' m',
      rep xp F (ActiveTxn ds m') ms' sm hm'
    >} write_range xp a l ms.
Proof.
(* skipped proof tokens: 128 *)
Admitted.
Definition read_cond A xp a nr (vfold : A -> valu -> A) v0 (cond : A -> bool) ms :=
    let^ (ms, pf, ret) <- ForN i < nr
    Hashmap hm
    Ghost [ F Fm crash ds sm m vs ms0 ]
    Loopvar [ ms pf ret ]
    Invariant
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ ret = None ->
        cond pf = false ]] *
      [[ forall v, ret = Some v ->
        cond v = true ]] *
      [[ ret = None ->
        pf = fold_left vfold (firstn i (map fst vs)) v0 ]] *
      [[ (exists ms00, readOnly ms00 ms0) -> readOnly ms0 ms ]]
    OnCrash  crash
    Begin
      If (is_some ret) {
        Ret ^(ms, pf, ret)
      } else {
        let^ (ms, v) <- read_array xp a i ms;
            let pf' := vfold pf v in
            If (bool_dec (cond pf') true) {
                Ret ^(ms, pf', Some pf')
            } else {
                Ret ^(ms, pf', None)
            }
      }
    Rof ^(ms, v0, None);
    Ret ^(ms, ret).
Theorem read_cond_ok : forall A xp a nr vfold (v0 : A) cond ms,
    {< F Fm ds sm m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[ nr <= length vs /\ cond v0 = false ]] *
      [[[ m ::: (Fm * arrayP a vs) ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' sm hm' *
      ( exists v, [[ r = Some v /\ cond v = true ]] \/
      [[ r = None /\ cond (fold_left vfold (firstn nr (map fst vs)) v0) = false ]]) *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' sm hm'
    >} read_cond xp a nr vfold v0 cond ms.
Proof.
(* skipped proof tokens: 232 *)
Admitted.
Hint Extern 1 ({{_}} Bind (read_cond _ _ _ _ _ _ _) _) => apply read_cond_ok : prog.
Hint Extern 1 ({{_}} Bind (read_range _ _ _ _ _ _) _) => apply read_range_ok : prog.
Hint Extern 1 ({{_}} Bind (write_range _ _ _ _) _) => apply write_range_ok : prog.
Definition dwrite_vecs (xp : log_xparams) avl ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dwrite_vecs xp avl mm;
    Ret (mk_memstate vmap0 mm').
Definition dsync_vecs xp al ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dsync_vecs xp al mm;
    Ret (mk_memstate cm mm').
Lemma dwrite_ptsto_inbound : forall (F : @pred _ _ valuset) ovl avl m,
    (F * listmatch (fun v e => fst e |-> v) ovl avl)%pred (list2nmem m) ->
    Forall (fun e => (@fst _ valu) e < length m) avl.
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma sep_star_reorder_helper2: forall AT AEQ V (a b c d : @pred AT AEQ V),
    (a * (b * (c * d))) <=p=> (a * b * d) * c.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma sep_star_reorder_helper3: forall AT AEQ V (a b c d : @pred AT AEQ V),
    ((a * b) * (c * d)) <=p=> ((a * c * d) * b).
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma dwrite_vsupd_vecs_ok : forall avl ovl m F,
    (F * listmatch (fun v e => fst e |-> v) ovl avl)%pred (list2nmem m) ->
    NoDup (map fst avl) ->
    (F * listmatch (fun v e => fst e |-> (snd e, vsmerge v)) ovl avl)%pred (list2nmem (vsupd_vecs m avl)).
Proof.
(* skipped proof tokens: 160 *)
Admitted.
Lemma dsync_vssync_vecs_ok : forall al vsl m F,
    (F * listmatch (fun vs a => a |-> vs) vsl al)%pred (list2nmem m) ->
    (F * listmatch (fun vs a => a |-> (fst vs, nil)) vsl al)%pred (list2nmem (vssync_vecs m al)).
Proof.
(* skipped proof tokens: 116 *)
Admitted.
Lemma dsync_vssync_vecs_partial : forall al n vsl F m,
    (F * listmatch (fun vs a => a |-> vs) vsl al)%pred (list2nmem m) ->
    (F * listmatch (fun vs a => a |-> vs \/ a |=> fst vs) vsl al)%pred
        (list2nmem (vssync_vecs m (firstn n al))).
Proof.
(* original proof tokens: 243 *)

(* No more tactics to try *)
Admitted.

Lemma sm_upd_vecs_listpred_ptsto: forall a sm F,
    (F * listpred (fun a => (fst a) |->?) a)%pred sm ->
    (F * listpred (fun a => (fst a) |-> false) a)%pred (sm_upd_vecs sm a).
Proof.
(* skipped proof tokens: 90 *)
Admitted.
Lemma sm_sync_vecs_listpred_ptsto: forall a sm F,
    (F * listpred (fun a => a |->?) a)%pred sm ->
    (F * listpred (fun a => a |-> true) a)%pred (sm_sync_vecs sm a).
Proof.
(* skipped proof tokens: 89 *)
Admitted.
Theorem dwrite_vecs_ok : forall xp ms avl,
    {< F Fs Fm ds sm ovl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[[ ds!! ::: Fm * listmatch (fun v e => (fst e) |-> v) ovl avl ]]] *
      [[ (Fs * listpred (fun e => (fst e) |->?) avl)%pred sm ]] *
      [[ NoDup (map fst avl) /\ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun v e => (fst e) |-> (snd e, vsmerge v)) ovl avl ]]] *
      [[ (Fs * listpred (fun e => (fst e) |-> false) avl)%pred sm' ]] *
      [[ ds' = (dsupd_vecs ds avl) ]]
    XCRASH:hm'
      recover_any xp F ds hm' \/
      recover_any xp F (dsupd_vecs ds avl) hm'
    >} dwrite_vecs xp avl ms.
Proof.
(* skipped proof tokens: 212 *)
Admitted.
Theorem dsync_vecs_ok : forall xp ms al,
    {< F Fs Fm ds sm vsl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl al ]]] *
      [[ (Fs * listpred (fun a => a |->?) al)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl al ]]] *
      [[ (Fs * listpred (fun a => a |-> true) al)%pred sm' ]] *
      [[ ds' = dssync_vecs ds al ]]
    CRASH:hm'
      recover_any xp F ds hm'
    >} dsync_vecs xp al ms.
Proof.
(* skipped proof tokens: 125 *)
Admitted.
Lemma sm_vs_valid_listpred_Forall: forall l F sm vs,
    (F * listpred (fun a => a |-> true) l)%pred sm ->
    sm_vs_valid sm vs ->
    Forall (fun a => vs_synced a vs) l.
Proof.
(* skipped proof tokens: 78 *)
Admitted.
Lemma sm_ds_valid_listpred_Forall: forall l F sm ds,
    (F * listpred (fun a => a |-> true) l)%pred sm ->
    sm_ds_valid sm ds ->
    Forall (fun a => ds_synced a ds) l.
Proof.
(* skipped proof tokens: 78 *)
Admitted.
Theorem dsync_vecs_additional_ok' : forall xp ms al,
    {< F Fs Fm ds sm all synced vsl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[ all = al ++ synced ]] *
      [[ (Fs * listpred (fun a => a |->?) al * listpred (fun a => a |-> true) synced)%pred sm ]] *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl all ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl all ]]] *
      [[ (Fs * listpred (fun a => a |-> true) all)%pred sm' ]] *
      [[ ds' = dssync_vecs ds all ]]
    CRASH:hm'
      recover_any xp F ds hm'
    >} dsync_vecs xp al ms.
Proof.
(* skipped proof tokens: 341 *)
Admitted.
Hint Resolve Nat.eqb_eq.
Hint Rewrite sort_by_index_length split_length_l split_length_r : lists.
Theorem dsync_vecs_additional_ok : forall xp ms al,
    {< F Fs Fm ds sm all vsl sml,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[ (Fs * listmatch (fun b a => a |-> b) sml all)%pred sm ]] *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl all ]]] *
      [[ forall i, i < length all -> In (selN all i 0) al \/ selN sml i false = true ]] *
      [[ incl al all ]] * [[ NoDup al ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl all ]]] *
      [[ (Fs * listpred (fun a => a |-> true) all)%pred sm' ]] *
      [[ ds' = dssync_vecs ds all ]]
    CRASH:hm'
      recover_any xp F ds hm'
    >} dsync_vecs xp al ms.
Proof.
(* skipped proof tokens: 1026 *)
Admitted.
Hint Extern 1 ({{_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
Hint Extern 1 ({{_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.
Lemma idempred_hashmap_subset : forall xp F ds hm hm',
    (exists l, hashmap_subset l hm hm')
    -> idempred xp F ds hm
       =p=> idempred xp F ds hm'.
Proof.
(* skipped proof tokens: 178 *)
Admitted.
Lemma crash_xform_intact_dssync_vecs_idempred : forall xp F sm ds al hm,
    crash_xform (intact xp F (dssync_vecs ds al) sm hm) =p=>
    idempred xp (crash_xform F) ds hm.
Proof.
(* skipped proof tokens: 85 *)
Admitted.
Lemma crash_xform_cached_before: forall fsxp F d hm ms ds sm n,
    n <= length (snd ds) ->
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    crash_xform (rep (FSXPLog fsxp) F (LOG.NoTxn (d, [])) ms sm hm)
        =p=> crash_xform (before_crash (FSXPLog fsxp) F ds hm).
Proof.
(* skipped proof tokens: 127 *)
Admitted.
End LOG.
Global Opaque LOG.begin.
Global Opaque LOG.abort.
Global Opaque LOG.commit.
Global Opaque LOG.commit_ro.
Global Opaque LOG.write.
Global Opaque LOG.write_array.
Arguments LOG.rep : simpl never.
