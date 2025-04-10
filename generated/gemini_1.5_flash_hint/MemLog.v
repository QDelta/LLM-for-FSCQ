Require Import String.
Require Import Hashmap.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classes.SetoidTactics.
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
Require Import DiskLogHash.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import MapUtils.
Require Import FMapFacts.
Require Import Lock.
Require Import LogReplay.
Import ListNotations.
Set Implicit Arguments.
Module LogNotations.
Notation "'<<' F ',' func ':' a1 a2 ms hm '>>'" :=
    (exists raw, BUFCACHE.rep (snd ms%pred) raw *
     lift_empty ((F * (func a1 a2 (fst ms) hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, ms, hm at level 0, only parsing) : pred_scope.
Notation "'<<' F ',' func ':' a1 a2 a3 ms hm '>>'" :=
    (exists raw, BUFCACHE.rep (snd ms%pred) raw *
     lift_empty ((F * (func a1 a2 a3 (fst ms) hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, a3, ms, hm at level 0, only parsing) : pred_scope.
Notation "'<<' F ',' func ':' a1 a2 hm '--' '>>'" :=
    (exists raw cs, BUFCACHE.rep cs raw *
     lift_empty ((F * (func a1 a2 hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, hm at level 0, only parsing) : pred_scope.
Notation "'<<' F ',' func ':' a1 a2 a3 hm '--' '>>'" :=
    (exists raw cs, BUFCACHE.rep cs raw *
     lift_empty ((F * (func a1 a2 a3 hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, a3, hm at level 0, only parsing) : pred_scope.
End LogNotations.
Module MLog.
Import AddrMap LogReplay LogNotations.
Definition mstate := valumap.
Definition memstate := (mstate * cachestate)%type.
Definition mk_memstate ms cs : memstate := (ms, cs).
Definition MSCache (ms : memstate) := snd ms.
Definition MSInLog (ms : memstate) := fst ms.
Definition readOnly (ms ms' : memstate) := (fst ms = fst ms').
Inductive logstate :=
  | Synced  (na : nat) (d : diskstate)
  

  | Flushing (d : diskstate) (ents : DLog.contents)
  

  | Applying (d : diskstate)
  

  | Rollback (d : diskstate)
  

  | Recovering (d : diskstate)
  
  .
Definition equal_unless_in (keys: list addr) (l1 l2: list valuset) :=
    length l1 = length l2 /\
    forall a,  ~ In a keys -> selN l1 a ($0, nil) = selN l2 a ($0, nil).
Definition synced_rep xp (d : diskstate) : rawpred :=
    arrayS (DataStart xp) d.
Definition unsync_rep xp (ms : valumap) (old : diskstate) : rawpred :=
    (exists vs, [[ equal_unless_in (map_keys ms) old vs ]] *
     arrayS (DataStart xp) vs
    )%pred.
Definition rep xp st mm hm :=
    ( exists log d0,
      [[ Map.Equal mm (replay_mem log vmap0) ]] *
      [[ goodSize addrlen (length d0) /\ map_valid mm d0 ]] *
    match st with
    | Synced na d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        DLog.rep xp (DLog.Synced na log) hm
    | Flushing d ents => exists na,
        [[ log_valid ents d /\ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        (DLog.rep xp (DLog.Synced na log) hm
      \/ DLog.rep xp (DLog.Extended log ents) hm)
    | Applying d => exists na,
        [[ map_replay mm d0 d ]] *
        (((DLog.rep xp (DLog.Synced na log) hm) *
          (unsync_rep xp mm d0))
      \/ ((DLog.rep xp (DLog.Truncated log) hm) *
          (synced_rep xp d)))
    | Rollback d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        DLog.rep xp (DLog.Rollback log) hm
    | Recovering d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        DLog.rep xp (DLog.Recovering log) hm
    end)%pred.
Definition would_recover_before xp d hm :=
    (exists mm, rep xp (Applying d) mm hm \/
     exists mm na', rep xp (Synced na' d) mm hm)%pred.
Definition would_recover_either xp d ents hm :=
     (exists mm,
      (exists na', rep xp (Synced na' d) mm hm) \/
      (exists na', rep xp (Synced na' (replay_disk ents d)) mm hm) \/
      rep xp (Flushing d ents) mm hm \/
      rep xp (Applying d) mm hm \/
      rep xp (Recovering d) mm hm)%pred.
Theorem sync_invariant_rep : forall xp st mm hm,
    sync_invariant (rep xp st mm hm).
(* hint proof tokens: 28 *)
Proof.
    unfold rep, synced_rep, unsync_rep; destruct st; intros; eauto 20.
  Qed.
Hint Resolve sync_invariant_rep.
Theorem sync_invariant_would_recover_before : forall xp d hm,
    sync_invariant (would_recover_before xp d hm).
Proof.
(* original proof tokens: 17 *)
(* generated proof tokens: 18 *)

intros. unfold would_recover_before; eauto.
Qed.

Theorem sync_invariant_would_recover_either : forall xp d ents hm,
    sync_invariant (would_recover_either xp d ents hm).
Proof.
(* original proof tokens: 20 *)

(* No more tactics to try *)
Admitted.

Hint Resolve sync_invariant_would_recover_before sync_invariant_would_recover_either.
Definition read xp a ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    match Map.find a oms with
    | Some v => Ret ^(ms, v)
    | None =>
        let^ (cs, v) <- BUFCACHE.read_array (DataStart xp) a cs;
        Ret ^(mk_memstate oms cs, v)
    end.
Definition flush_noapply xp ents ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    let^ (cs, ok) <- DLog.extend xp ents cs;
    If (bool_dec ok true) {
      Ret ^(mk_memstate (replay_mem ents oms) cs, true)
    } else {
      Ret ^(mk_memstate oms cs, false)
    }.
Definition apply xp ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs <- BUFCACHE.write_vecs (DataStart xp) (Map.elements oms) cs;
    cs <- BUFCACHE.sync_vecs_now (DataStart xp) (map_keys oms) cs;
    cs <- DLog.trunc xp cs;
    Ret (mk_memstate vmap0 cs).
Definition flush xp ents ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    If (addr_eq_dec (length ents) 0) {
      Ret ^(ms, true)
    } else {
      let^ (cs, na) <- DLog.avail xp cs;
      let ms := (mk_memstate oms cs) in
      ms' <- If (lt_dec na (length ents)) {
        ms <- apply xp ms;
        Ret ms
      } else {
        Ret ms
      };
      r <- flush_noapply xp ents ms';
      Ret r
   }.
Definition sync_cache (xp : log_xparams) ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs <- BUFCACHE.sync_all cs;
    Ret (mk_memstate oms cs).
Definition dwrite xp a v ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    ms' <- If (MapFacts.In_dec oms a) {
      ms <- apply xp ms;
      Ret ms
    } else {
      Ret ms
    };
    cs' <- BUFCACHE.write_array (DataStart xp) a v (MSCache ms');
    Ret (mk_memstate (MSInLog ms') cs').
Definition dsync xp a ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs' <- BUFCACHE.begin_sync cs;
    cs' <- BUFCACHE.sync_array (DataStart xp) a cs';
    cs' <- BUFCACHE.end_sync cs';
    Ret (mk_memstate oms cs').
Definition recover xp cs :=
    cs <- DLog.recover xp cs;
    let^ (cs, log) <- DLog.read xp cs;
    Ret (mk_memstate (replay_mem log vmap0) cs).
Definition init (xp : log_xparams) cs :=
    cs <- DLog.init xp cs;
    Ret (mk_memstate vmap0 cs).
Arguments DLog.rep: simpl never.
Hint Extern 0 (okToUnify (DLog.rep _ _ _) (DLog.rep _ _ _)) => constructor : okToUnify.
Lemma rep_hashmap_subset : forall xp mm hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st mm hm
        =p=> rep xp st mm hm'.
(* hint proof tokens: 63 *)
Proof.
    unfold rep; intros.
    destruct st; cancel.
    all: eauto.
    all: erewrite DLog.rep_hashmap_subset; eauto; cancel.
    or_l; cancel.
    or_r; cancel.
    Unshelve. all: easy.
  Qed.
Lemma would_recover_either_hashmap_subset : forall xp d ents hm hm',
    (exists l, hashmap_subset l hm hm')
    -> would_recover_either xp d ents hm
        =p=> would_recover_either xp d ents hm'.
(* hint proof tokens: 34 *)
Proof.
    unfold would_recover_either; intros; cancel.
    all: erewrite rep_hashmap_subset; eauto; cancel.
  Qed.
Lemma synced_applying : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    exists ms', rep xp (Applying d) ms' hm.
(* hint proof tokens: 45 *)
Proof.
    unfold rep, map_replay, unsync_rep, synced_rep in *.
    cancel; eauto.
    or_l; cancel.
    unfold equal_unless_in; intuition.
  Qed.
Lemma synced_flushing : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    exists ms' ents, rep xp (Flushing d ents) ms' hm.
(* hint proof tokens: 78 *)
Proof.
    unfold rep, map_replay, unsync_rep, synced_rep in *.
    cancel; eauto.
    or_l.
    eassign na.
    unfold DLog.rep. cancel; eauto.
    cancel.
    unfold log_valid; intuition.
    unfold KNoDup; auto.
    inversion H1.
    inversion H1.
  Qed.
Lemma equal_unless_in_length_eq : forall a b l,
    equal_unless_in l a b -> length b = length a.
Proof.
(* original proof tokens: 17 *)
(* generated proof tokens: 15 *)

intros.
destruct H.
auto.
Qed.

Lemma apply_synced_data_ok' : forall l d,
    NoDup (map fst l) ->
    vssync_vecs (vsupd_vecs d l) (map fst l) = replay_disk l d.
(* hint proof tokens: 75 *)
Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl.
    inversion H; subst.
    rewrite <- IHl by auto.

    rewrite vsupd_vecs_vsupd_notin by auto.
    rewrite vssync_vsupd_eq.
    rewrite updN_vsupd_vecs_notin; auto.
  Qed.
Lemma apply_synced_data_ok : forall xp m d,
    arrayS (DataStart xp) (vssync_vecs (vsupd_vecs d (Map.elements m)) (map_keys m))
    =p=> synced_rep xp (replay_disk (Map.elements m) d).
(* hint proof tokens: 39 *)
Proof.
    unfold synced_rep; intros.
    apply arrayN_unify.
    apply apply_synced_data_ok'.
    apply KNoDup_NoDup; auto.
  Qed.
Lemma apply_unsync_applying_ok' : forall l d n,
    NoDup (map fst l) ->
    equal_unless_in (map fst l) d (vsupd_vecs d (firstn n l)).
(* hint proof tokens: 182 *)
Proof.
    unfold equal_unless_in; induction l; intros; simpl.
    rewrite firstn_nil; simpl; intuition.
    split; intuition;
    destruct n; simpl; auto;
    destruct a; inversion H; simpl in *; intuition; subst.

    rewrite vsupd_vecs_vsupd_notin.
    rewrite vsupd_length, vsupd_vecs_length; auto.
    rewrite <- firstn_map_comm.
    contradict H2.
    eapply in_firstn_in; eauto.

    pose proof (IHl d n H5) as [Hx Hy].
    rewrite Hy by auto.
    rewrite vsupd_vecs_vsupd_notin.
    unfold vsupd; rewrite selN_updN_ne; auto.
    rewrite <- firstn_map_comm.
    contradict H4.
    eapply in_firstn_in; eauto.
  Qed.
Lemma apply_unsync_applying_ok : forall xp m d n,
    arrayS (DataStart xp) (vsupd_vecs d (firstn n (Map.elements m)))
       =p=> unsync_rep xp m d.
(* hint proof tokens: 38 *)
Proof.
    unfold unsync_rep, map_replay; cancel.
    apply apply_unsync_applying_ok'.
    apply KNoDup_NoDup; auto.
  Qed.
Lemma apply_unsync_syncing_ok' : forall l a d n,
    NoDup (map fst l) ->
    ~ In a (map fst l) ->
    selN d a ($0, nil) = selN (vssync_vecs (vsupd_vecs d l) (firstn n (map fst l))) a ($0, nil).
(* hint proof tokens: 147 *)
Proof.
    induction l; intros; simpl.
    rewrite firstn_nil; simpl; auto.

    destruct a; inversion H; simpl in *; subst; intuition.
    destruct n; simpl; auto.
    rewrite vsupd_vecs_vsupd_notin by auto.
    unfold vsupd.
    rewrite selN_updN_ne by auto.
    rewrite vsupd_vecs_selN_not_in; auto.

    unfold vssync.
    rewrite -> updN_vsupd_vecs_notin by auto.
    rewrite <- IHl; auto.
    rewrite selN_updN_ne by auto.
    unfold vsupd.
    rewrite selN_updN_ne; auto.
  Qed.
Lemma apply_unsync_syncing_ok : forall xp m d n,
    arrayS (DataStart xp) (vssync_vecs (vsupd_vecs d (Map.elements m)) (firstn n (map_keys m)))
       =p=> unsync_rep xp m d.
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Lemma rep_rollback_pimpl : forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=>
      rep xp (Recovering d) ms hm.
Proof.
(* original proof tokens: 35 *)
eapply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma rep_synced_pimpl : forall xp nr d ms hm,
    rep xp (Synced nr d) ms hm =p=>
      rep xp (Recovering d) ms hm.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Theorem recover_before_either : forall xp d ents hm,
    would_recover_before xp d hm =p=>
    would_recover_either xp d ents hm.
(* hint proof tokens: 22 *)
Proof.
    unfold would_recover_before, would_recover_either; cancel.
  Qed.
Theorem synced_recover_before : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    would_recover_before xp d hm.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Theorem synced_recover_either : forall xp na d ms ents hm,
    rep xp (Synced na d) ms hm =p=>
    would_recover_either xp d ents hm.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Theorem rollback_recover_either : forall xp d ms ents hm,
    rep xp (Rollback d) ms hm =p=>
    would_recover_either xp d ents hm.
(* hint proof tokens: 37 *)
Proof.
    unfold would_recover_either; cancel.
    rewrite rep_rollback_pimpl.
    or_r; or_r; or_r; cancel.
  Qed.
Theorem applying_recover_before : forall xp d ms hm,
    rep xp (Applying d) ms hm =p=>
    would_recover_before xp d hm.
(* hint proof tokens: 16 *)
Proof.
    unfold would_recover_before; cancel.
  Qed.
Theorem synced_recover_after : forall xp na d ms ents hm,
    rep xp (Synced na (replay_disk ents d)) ms hm =p=>
    would_recover_either xp d ents hm.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Theorem applying_recover_after : forall xp d ms ents hm,
    rep xp (Applying d) ms hm =p=>
    would_recover_either xp d ents hm.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Theorem flushing_recover_after : forall xp d ms ents hm,
    rep xp (Flushing d ents) ms hm =p=>
    would_recover_either xp d ents hm.
(* hint proof tokens: 36 *)
Proof.
    unfold would_recover_either; intros.
    norm; unfold stars; simpl; auto.
    or_r; or_r; cancel.
  Qed.
Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.
Section UnfoldProof1.
Local Hint Unfold rep map_replay: hoare_unfold.
Definition init_ok : forall xp cs,
    {< F l m d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * arrayS (DataStart xp) m * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * PaddedLog.DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: ms  exists d' nr,
          BUFCACHE.rep (MSCache ms) d' *
          [[ (F * rep xp (Synced nr m) (MSInLog ms) hm')%pred d' ]]
    XCRASH:hm_crash any
    >} init xp cs.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem read_ok: forall xp ms a,
    {< F d na vs,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[[ d ::: exists F', (F' * a |-> vs) ]]]
    POST:hm' RET:^(ms', r)
      << F, rep: xp (Synced na d) ms' hm' >> * [[ r = fst vs ]] * [[ readOnly ms ms' ]]
    CRASH:hm'
      exists ms', << F, rep: xp (Synced na d) ms' hm' >>
    >} read xp a ms.
Proof.
(* original proof tokens: 244 *)

(* No more tactics to try *)
Admitted.

End UnfoldProof1.
Local Hint Resolve log_valid_nodup.
Section UnfoldProof2.
Local Hint Unfold rep map_replay synced_rep: hoare_unfold.
Theorem flush_noapply_ok: forall xp ents ms,
    {< F d na,
     PRE:hm  << F, rep: xp (Synced na d) ms hm >> *
          [[ log_valid ents d /\ sync_invariant F ]]
     POST:hm' RET:^(ms',r)
          ([[ r = true ]]  * exists na',
            << F, rep: xp (Synced na' (replay_disk ents d)) ms' hm' >>) \/
          ([[ r = false /\ length ents > na ]] *
            << F, rep: xp (Synced na d) ms' hm' >>)
     XCRASH:hm'  exists ms',
            << F, rep: xp (Flushing d ents) ms' hm' >>
    >} flush_noapply xp ents ms.
Proof.
(* original proof tokens: 149 *)

(* No more tactics to try *)
Admitted.

End UnfoldProof2.
Section UnfoldProof3.
Local Hint Unfold rep map_replay would_recover_before: hoare_unfold.
Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.
Lemma goodSize_vssync_vsupd_vecs : forall l ents ks,
    goodSize addrlen (length l) ->
    goodSize addrlen (length (vssync_vecs (vsupd_vecs l ents) ks)).
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma map_valid_vssync_vsupd_vecs : forall l mm ents ks,
    map_valid mm l ->
    map_valid mm (vssync_vecs (vsupd_vecs l ents) ks).
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma replay_disk_vssync_vsupd_vecs : forall d mm,
    replay_disk (Map.elements mm) d =
    vssync_vecs (vsupd_vecs d (Map.elements mm)) (map_keys mm).
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma replay_disk_vssync_vsupd_vecs_twice : forall d mm,
    replay_disk (Map.elements mm) d =
    replay_disk (Map.elements mm) (vssync_vecs (vsupd_vecs d (Map.elements mm)) (map_keys mm)).
(* hint proof tokens: 38 *)
Proof.
    intros; rewrite apply_synced_data_ok'; auto.
    rewrite replay_disk_twice; auto.
    apply KNoDup_NoDup; auto.
  Qed.
Lemma replay_disk_vsupd_vecs' : forall l d,
    KNoDup l ->
    replay_disk l (vsupd_vecs d l) =
    replay_disk l d.
(* hint proof tokens: 104 *)
Proof.
    induction l; simpl; intros; auto.
    destruct a; inversion H; subst; simpl in *.
    assert (~ In k (map fst l)).
    contradict H2.
    apply In_KIn; auto.

    rewrite replay_disk_updN_comm; auto.
    rewrite IHl; unfold vsupd; auto.
    rewrite replay_disk_updN_comm; auto.
    rewrite updN_twice.
    rewrite replay_disk_updN_comm; auto.
  Qed.
Lemma replay_disk_vsupd_vecs : forall mm d,
    replay_disk (Map.elements mm) (vsupd_vecs d (Map.elements mm)) =
    replay_disk (Map.elements mm) d.
(* hint proof tokens: 23 *)
Proof.
    intros.
    apply replay_disk_vsupd_vecs'.
    auto.
  Qed.
Local Hint Resolve goodSize_vssync_vsupd_vecs map_valid_map0
                     map_valid_vssync_vsupd_vecs KNoDup_NoDup
                     replay_disk_vssync_vsupd_vecs replay_disk_vssync_vsupd_vecs_twice
                     replay_disk_vsupd_vecs.
Theorem apply_ok: forall xp ms,
    {< F d na,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Synced (LogLen xp) d) ms' hm' >> *
      [[ Map.Empty (MSInLog ms') ]]
    XCRASH:hm'
      << F, would_recover_before: xp d hm' -- >>
    >} apply xp ms.
(* hint proof tokens: 353 *)
Proof.
    unfold apply; intros.
    step.
    unfold synced_rep; cancel.
    step.
    rewrite vsupd_vecs_length.
    apply map_valid_Forall_synced_map_fst; auto.
    safestep.
    erewrite DLog.rep_hashmap_subset.
    cancel.
    auto. auto.
    safestep.
    unfold synced_rep; eauto.
    rewrite vssync_vecs_length, vsupd_vecs_length; eauto.
    rewrite replay_disk_vssync_vsupd_vecs; auto.

    
    xcrash.
    or_r; safecancel; eauto.

    xcrash.
    or_l; safecancel; eauto.
    rewrite replay_disk_vssync_vsupd_vecs.
    or_r; unfold synced_rep; cancel.

    xcrash.
    or_r; safecancel.
    unfold synced_rep; cancel.
    rewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; eauto.
    eapply length_eq_map_valid; eauto.
    rewrite vsupd_vecs_length; auto.
    erewrite <- LogReplay.replay_disk_vsupd_vecs; eauto.

    xcrash.
    or_r; safecancel.
    unfold synced_rep; cancel.
    rewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; eauto.
    eapply length_eq_map_valid; eauto.
    rewrite vsupd_vecs_length; auto.
    erewrite <- LogReplay.replay_disk_vsupd_vecs; eauto.

    Unshelve. all: eauto.
  Qed.
End UnfoldProof3.
Local Hint Unfold map_replay : hoare_unfold.
Hint Extern 1 ({{_}} Bind (apply _ _) _) => apply apply_ok : prog.
Hint Extern 1 ({{_}} Bind (flush_noapply _ _ _) _) => apply flush_noapply_ok : prog.
Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.
Theorem flush_ok: forall xp ents ms,
    {< F d na,
     PRE:hm  << F, rep: xp (Synced na d) ms hm >> *
          [[ log_valid ents d /\ sync_invariant F ]]
     POST:hm' RET:^(ms',r) exists na',
          ([[ r = true ]] *
           << F, rep: xp (Synced na' (replay_disk ents d)) ms' hm' >>)
      \/  ([[ r = false /\ length ents > (LogLen xp) ]] *
           << F, rep: xp (Synced na' d) ms' hm' >>)
     XCRASH:hm'
          << F, would_recover_either: xp d ents hm' -- >>
    >} flush xp ents ms.
Proof.
(* original proof tokens: 196 *)

(* No more tactics to try *)
Admitted.

Theorem dwrite_ok: forall xp a v ms,
    {< F Fd d na vs,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[[ d ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists d' na',
      << F, rep: xp (Synced na' d') ms' hm' >> *
      [[ d' = updN d a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]]
    XCRASH:hm'
      << F, would_recover_before: xp d hm' -- >> \/
      exists ms' na' d',
      << F, rep: xp (Synced na' d') ms' hm' >> *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]] *
      [[ d' = updN d a (v, vsmerge vs) ]]
    >} dwrite xp a v ms.
Proof.
(* original proof tokens: 977 *)

(* No more tactics to try *)
Admitted.

Section UnfoldProof4.
Local Hint Unfold rep map_replay synced_rep: hoare_unfold.
Theorem dsync_ok: forall xp a ms,
    {< F Fd d na vs,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[[ d ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists d' na',
      << F, rep: xp (Synced na' d') ms' hm' >> *
      [[[ d' ::: (Fd * a |-> (fst vs, nil)) ]]] *
      [[  d' = vssync d a ]]
    CRASH:hm'
      exists ms' na',
      << F, rep: xp (Synced na' d) ms' hm' >>
    >} dsync xp a ms.
(* hint proof tokens: 160 *)
Proof.
    unfold dsync.
    step.
    step.
    subst; erewrite <- replay_disk_length.
    eapply list2nmem_inbound; eauto.
    step.

    step.
    rewrite DLog.rep_hashmap_subset; eauto.
    unfold vssync; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    setoid_rewrite <- replay_disk_vssync_comm.
    unfold vssync.
    erewrite <- list2nmem_sel; eauto; simpl.
    eapply list2nmem_updN; eauto.
    setoid_rewrite replay_disk_vssync_comm.
    auto.

    
    all: rewrite DLog.rep_hashmap_subset; eauto.
  Qed.
End UnfoldProof4.
Definition dwrite_vecs xp avl ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    ms' <- If (bool_dec (overlap (map fst avl) oms) true) {
      ms <- apply xp ms;
      Ret ms
    } else {
      Ret ms
    };
    cs' <- BUFCACHE.write_vecs (DataStart xp) avl (MSCache ms');
    Ret (mk_memstate (MSInLog ms') cs').
Definition dsync_vecs xp al ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs' <- BUFCACHE.sync_vecs_now (DataStart xp) al cs;
    Ret (mk_memstate oms cs').
Lemma map_valid_replay_mem_synced_list : forall x0 x3 x4 l',
    map_valid x0 x4 ->
    possible_crash_list x4 l' ->
    Map.Equal x0 (replay_mem x3 vmap0) ->
    map_valid (replay_mem x3 vmap0) (synced_list l').
(* hint proof tokens: 50 *)
Proof.
    intros.
    eapply map_valid_equal; eauto.
    eapply length_eq_map_valid; eauto.
    rewrite synced_list_length.
    erewrite <- possible_crash_list_length; eauto.
  Qed.
Hint Rewrite selN_combine repeat_selN' Nat.min_id synced_list_length : lists.
Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints lists)) in H); subst_evars;
      [ try simplen_rewrite H | try autorewrite with lists .. ]).
Ltac simplen' := repeat match goal with
    | [H : context[length ?x] |- _] => progress ( first [ is_var x | simplen_rewrite H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : context[Nat.min ?a ?a] |- _ ] => rewrite Nat.min_id in H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : equal_unless_in _ _ _ |- _ ] => apply equal_unless_in_length_eq in H
    | [H : possible_crash_list _ _ |- _ ] => apply possible_crash_list_length in H
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try lia ]
    end.
Ltac simplen :=  auto; repeat (try subst; simpl;
    auto; simplen'; autorewrite with lists); simpl; eauto; try lia.
Ltac map_rewrites :=
    match goal with
    | [ H : Map.Equal (replay_mem ?x ?y) _ |- map_valid (replay_mem ?x ?y) ?l ] =>
        eapply (map_valid_equal (MapFacts.Equal_sym H))
    | [ H : Map.Equal _ (replay_mem ?x ?y) |- map_valid (replay_mem ?x ?y) ?l ] =>
        eapply (map_valid_equal H)
    | [ H : Map.Equal _  (replay_mem ?x ?y)
        |-  context [ replay_disk (Map.elements (replay_mem ?x ?y)) _ ] ] =>
        rewrite (mapeq_elements (MapFacts.Equal_sym H))
    | [ H : Map.Equal (replay_mem ?x ?y) _
        |-  context [ replay_disk (Map.elements (replay_mem ?x ?y)) _ ] ] =>
        rewrite (mapeq_elements H)
    end.
Ltac t :=
    repeat map_rewrites;
    try match goal with
      | [ H : goodSize _ ?a |- goodSize _ ?b ] => simplen
      | [ H : map_valid ?a _ |- map_valid ?a _ ] =>
          solve [ eapply (length_eq_map_valid _ H); simplen ]
      | [ |- map_valid (replay_mem _ _) (synced_list _) ] =>
          try solve [ eapply map_valid_replay_mem_synced_list; eauto ]
    end.
Lemma equal_unless_in_possible_crash : forall l a b c,
    equal_unless_in l (synced_list a) b ->
    possible_crash_list b c ->
    forall i, ~ In i l -> selN a i $0 = selN c i $0.
Proof.
(* original proof tokens: 127 *)

(* No more tactics to try *)
Admitted.

Lemma equal_unless_in_updN : forall B l a (b : B) v d d',
    ~ KIn (a, b) l ->
    equal_unless_in (a :: map fst l) d d' ->
    equal_unless_in (map fst l) (updN d a (v, nil)) (updN d' a (v, nil)).
(* hint proof tokens: 86 *)
Proof.
    unfold equal_unless_in, synced_list; intuition; simpl in *.
    simplen.
    destruct (lt_dec a0 (length d)).
    destruct (Nat.eq_dec a a0); simplen.
    repeat rewrite selN_updN_ne by auto.
    rewrite <- H2; simplen; tauto.
    repeat rewrite selN_oob; simplen.
  Qed.
Lemma equal_unless_in_sym : forall l a b,
    equal_unless_in l a b <-> equal_unless_in l b a.
Proof.
(* original proof tokens: 17 *)
split; intros; simpl in *; intuition; simplen; eauto.
split; simpl in *; intuition; simplen; eauto.
(* No more tactics to try *)
Admitted.

Lemma equal_unless_in_refl : forall l a,
    equal_unless_in l a a.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Lemma equal_unless_in_replay_disk' : forall l a b,
    KNoDup l ->
    equal_unless_in (map fst l) a b ->
    replay_disk l a = replay_disk l b.
Proof.
(* original proof tokens: 68 *)

(* No more tactics to try *)
Admitted.

Lemma equal_unless_in_replay_disk : forall a b m,
    equal_unless_in (map_keys m) b a ->
    replay_disk (Map.elements m) a = replay_disk (Map.elements m) b.
(* hint proof tokens: 34 *)
Proof.
    intros.
    eapply equal_unless_in_replay_disk'; eauto.
    apply equal_unless_in_sym; auto.
  Qed.
Lemma list2nmem_replay_disk_crash_xform : forall ents vsl vl (F : rawpred),
    KNoDup ents ->
    possible_crash_list vsl vl ->
    F (list2nmem (replay_disk ents vsl)) ->
    crash_xform F (list2nmem (replay_disk ents (synced_list vl))).
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_list2nmem_replay_disk : forall F ents vsl vl,
    crash_xform F (list2nmem (replay_disk ents vsl)) ->
    possible_crash_list vsl vl ->
    crash_xform F (list2nmem (replay_disk ents (synced_list vl))).
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma map_valid_replay_mem_app : forall a ents l' x0 x1,
     Map.Equal x0 (replay_mem a vmap0) ->
     map_valid x0 x1 ->
     possible_crash_list x1 l' ->
     log_valid ents (replay_disk (Map.elements (elt:=valu) x0) x1) ->
     map_valid (replay_mem (a ++ ents) vmap0) (synced_list l').
(* hint proof tokens: 107 *)
Proof.
      intros.
      eapply map_valid_equal.
      apply MapFacts.Equal_sym.
      apply replay_mem_app; auto.
      apply MapFacts.Equal_refl.
      apply map_valid_replay_mem'.
      destruct H2; split; intros; auto.
      specialize (H3 _ _ H4); destruct H3.
      simplen.
      eapply map_valid_equal; eauto.
      unfold map_valid; intros.
      destruct (H0 _ _ H3); simplen.
  Qed.
Lemma in_vsmerge_incl_trans : forall v vs vs',
    In v (vsmerge vs) ->
    fst vs = fst vs' ->
    incl (snd vs) (snd vs') ->
    In v (vsmerge vs').
(* hint proof tokens: 47 *)
Proof.
    unfold vsmerge; simpl in *; intuition simpl in *; subst.
    left; auto.
    right.
    eapply incl_tran; eauto.
    apply incl_refl.
  Qed.
Lemma possible_crash_vsupd_vecs_listupd : forall F m x st l avl,
    (F * arrayS st l)%pred m ->
    possible_crash m x ->
    possible_crash (listupd m st (vsupd_vecs l avl)) x.
Proof.
(* original proof tokens: 225 *)

(* No more tactics to try *)
Admitted.

Lemma dwrite_vecs_xcrash_ok : forall cs d raw xp F avl m n n' log hm,
    overlap (map fst avl) m <> true ->
    map_valid m d ->
    Map.Equal m (replay_mem log vmap0) ->
    goodSize addrlen (length d) ->
    ((DLog.rep xp (DLog.Synced n' log) hm * F) * 
      arrayS (DataStart xp) (vsupd_vecs d (firstn n avl)))%pred raw ->
    crash_xform (BUFCACHE.rep cs raw) =p=> 
      crash_xform (exists ms na, 
      << F, rep: xp (Synced na (vsupd_vecs (replay_disk (Map.elements m) d) avl)) ms hm >>).
Proof.
(* original proof tokens: 232 *)

(* No more tactics to try *)
Admitted.

Lemma dwrite_vecs_xcrash_ok_empty : forall cs d raw xp F avl m n n' log hm,
    Map.Empty m ->
    Map.Equal m (replay_mem log vmap0) ->
    goodSize addrlen (length d) ->
    ((DLog.rep xp (DLog.Synced n' log) hm * F) * 
      arrayS (DataStart xp) (vsupd_vecs d (firstn n avl)))%pred raw ->
    crash_xform (BUFCACHE.rep cs raw) =p=> 
        crash_xform (exists ms na, 
        << F, rep: xp (Synced na (vsupd_vecs (replay_disk (Map.elements m) d) avl)) ms hm >>).
(* hint proof tokens: 40 *)
Proof.
    intros.
    eapply dwrite_vecs_xcrash_ok; eauto.
    rewrite overlap_empty; auto.
    apply map_valid_empty; auto.
  Qed.
Lemma crash_xform_applying : forall xp d mm hm,
    crash_xform (rep xp (Applying d) mm hm) =p=>
      exists na d' mm', (rep xp (Synced na d') mm' hm) *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
Proof.
(* original proof tokens: 236 *)
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intro.
eapply pimpl_exists_l; intro; eauto.
eexists.
eapply pimpl_exists_l; [eapply pimpl_exists_l|]; intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intro.
(* Reached max number of model calls *)
Admitted.

Lemma crash_xform_synced : forall xp nr d ms hm,
    crash_xform (rep xp (Synced nr d) ms hm) =p=>
      exists d' ms' nr', rep xp (Synced nr' d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_applying_applying : forall xp d ms hm,
    crash_xform (rep xp (Applying d) ms hm) =p=>
      exists d' ms', rep xp (Applying d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_flushing : forall xp d ents ms hm,
    crash_xform (rep xp (Flushing d ents) ms hm) =p=>
      exists d' ms',
        (exists nr, rep xp (Synced nr d') ms' hm *
          ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
           [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]])) \/
        (rep xp (Rollback d') ms' hm *
          [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]]).
(* hint proof tokens: 388 *)
Proof.
    unfold rep, synced_rep, unsync_rep, map_replay; intros.
    xform_norml.

    - rewrite crash_xform_arrayN_subset.
      rewrite DLog.xform_rep_synced.
      cancel.
      or_l; cancel; eauto; try solve [simplen].
      or_l; cancel.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      eapply length_eq_map_valid; eauto; simplen.

    - rewrite crash_xform_arrayN_subset.
      rewrite DLog.xform_rep_extended.
      cancel.

      or_l; cancel; eauto; try solve [simplen].
      or_l; cancel.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      eapply length_eq_map_valid; eauto; simplen.

      or_l; cancel; eauto; try solve [simplen].
      or_r; cancel.
      eassign (replay_mem (Map.elements ms ++ ents) vmap0).
      erewrite replay_disk_replay_mem; auto.
      rewrite replay_mem_app'.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      rewrite replay_mem_app'.
      symmetry.
      apply replay_mem_app; auto.
      eapply map_valid_replay_mem_synced_list.
      eassign x0.
      3: apply MapFacts.Equal_refl.
      rewrite replay_mem_app'.
      eapply map_valid_replay_mem'; eauto.
      eapply log_valid_replay; eauto.
      auto.

      or_r; cancel; eauto; try solve [simplen].
      eapply length_eq_map_valid; eauto; simplen.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.
Lemma crash_xform_recovering' : forall xp d ms hm,
    crash_xform (rep xp (Recovering d) ms hm) =p=>
      exists d' ms',
        ((exists nr, rep xp (Synced nr d') ms' hm) \/
          rep xp (Rollback d') ms' hm) *
        [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
(* hint proof tokens: 145 *)
Proof.
    unfold rep, synced_rep, map_replay; intros.
    xform_norml.
    rewrite DLog.xform_rep_recovering, crash_xform_arrayN_subset.
    cancel.
    or_r; cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.

    or_l; cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.
Lemma crash_xform_rollback : forall xp d ms hm,
    crash_xform (rep xp (Rollback d) ms hm) =p=>
      exists d' ms', rep xp (Rollback d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
(* hint proof tokens: 94 *)
Proof.
    unfold rep, synced_rep; intros.
    xform_norm.
    rewrite DLog.xform_rep_rollback, crash_xform_arrayN_subset.
    cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    unfold map_replay in *; subst.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.
Lemma crash_xform_before : forall xp d hm,
    crash_xform (would_recover_before xp d hm) =p=>
      exists d' ms' na, rep xp (Synced na d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
(* hint proof tokens: 41 *)
Proof.
    unfold would_recover_before; intros.
    xform_norm.
    rewrite crash_xform_applying; cancel.
    rewrite crash_xform_synced; cancel.
  Qed.
Definition recover_either_pred xp d ents hm :=
    (exists d' ms',
      (exists nr, rep xp (Synced nr d') ms' hm *
        ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]])) \/
      (rep xp (Rollback d') ms' hm *
        [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]]))%pred.
Lemma crash_xform_either : forall xp d ents hm,
    crash_xform (would_recover_either xp d ents hm) =p=>
                  recover_either_pred xp d ents hm.
Proof.
(* original proof tokens: 166 *)
unfold would_recover_either, recover_either_pred; intros.
(* No more tactics to try *)
Admitted.

Lemma crash_xform_recovering : forall xp d ms ents hm,
    crash_xform (rep xp (Recovering d) ms hm) =p=>
      recover_either_pred xp d ents hm.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma either_pred_either : forall xp d hm ents,
    recover_either_pred xp d ents hm =p=>
    exists d', would_recover_either xp d' ents hm.
(* hint proof tokens: 40 *)
Proof.
    unfold recover_either_pred, would_recover_either.
    intros; xform_norm; cancel.
    erewrite rep_rollback_pimpl. cancel.
  Qed.
Lemma recover_idem : forall xp d ents hm,
    crash_xform (recover_either_pred xp d ents hm) =p=>
                 recover_either_pred xp d ents hm.
(* hint proof tokens: 121 *)
Proof.
    intros.
    unfold recover_either_pred.
    xform_norm.

    rewrite crash_xform_synced; cancel.
    or_l; cancel.
    or_l; cancel.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite crash_xform_synced; cancel.
    or_l; cancel.
    or_r; cancel.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite crash_xform_rollback; cancel.
    or_r; cancel.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.
Theorem recover_ok: forall xp cs,
    {< F raw d ents,
    PRE:hm
      BUFCACHE.rep cs raw *
      [[ (F * recover_either_pred xp d ents hm)%pred raw ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists raw',
      BUFCACHE.rep (MSCache ms') raw' *
      [[(exists d' na, F * rep xp (Synced na d') (MSInLog ms') hm' *
        ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]]
      ))%pred raw' ]]
    XCRASH:hm'
      exists cs' raw' ms', BUFCACHE.rep cs' raw' *
      [[ (exists d', F * rep xp (Recovering d') ms' hm' *
         ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]]
        ))%pred raw' ]]
    >} recover xp cs.
Proof.
(* original proof tokens: 512 *)

(* No more tactics to try *)
Admitted.

Theorem dwrite_vecs_ok : forall xp avl ms,
    {< F d na,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[ Forall (fun e => fst e < length d) avl /\ sync_invariant F ]]
    POST:hm' RET:ms' exists na',
      << F, rep: xp (Synced na' (vsupd_vecs d avl)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_before: xp d hm' -- >> \/
      exists na' ms',
      << F, rep: xp (Synced na' (vsupd_vecs d avl)) ms' hm' >>
    >} dwrite_vecs xp avl ms.
(* hint proof tokens: 467 *)
Proof.
    unfold dwrite_vecs, would_recover_before.
    step.

    
    step.
    prestep.
    unfold rep at 1.
    unfold synced_rep, map_replay in *.
    cancel; auto.
    erewrite <- replay_disk_length.
    eauto.

    step.
    unfold rep, synced_rep, map_replay; cancel.
    rewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; auto.
    apply map_valid_vsupd_vecs; auto.
    repeat rewrite replay_disk_empty; auto.

    
    norm'l. unfold stars; cbn.
    xcrash.
    or_r.
    rewrite dwrite_vecs_xcrash_ok_empty; eauto.
    xform_norm; cancel.
    xform_normr; cancel.
    eassign x2; eassign (x1_1, x1_2); eauto.
    pred_apply; eauto.
    pred_apply; rewrite firstn_oob; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.

    xcrash.
    or_l; cancel.
    xform_normr; cancel.

    
    denote rep as Hx; unfold rep, synced_rep, map_replay in Hx.
    destruct_lift Hx.
    step.
    erewrite <- replay_disk_length; eauto.

    step.
    unfold rep, synced_rep, map_replay; cancel.
    erewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; auto.
    apply map_valid_vsupd_vecs; auto.
    apply replay_disk_vsupd_vecs_nonoverlap; auto.
    apply not_true_is_false; auto.

    
    xcrash.
    or_r.
    rewrite dwrite_vecs_xcrash_ok; eauto.
    xform_norm; cancel.
    xform_normr; cancel.
    eassign x2; eassign (x1_1, x1_2); eauto.
    pred_apply; eauto.
    pred_apply; rewrite firstn_oob; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.
  Qed.
Theorem dsync_vecs_ok: forall xp al ms,
    {< F d na,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[ Forall (fun e => e < length d) al /\ sync_invariant F ]]
    POST:hm' RET:ms' exists na',
      << F, rep: xp (Synced na' (vssync_vecs d al)) ms' hm' >>
    CRASH:hm' exists na' ms',
      << F, rep: xp (Synced na' d) ms' hm' >>
    >} dsync_vecs xp al ms.
(* hint proof tokens: 102 *)
Proof.
    unfold dsync_vecs, rep, synced_rep, map_replay.
    step.
    subst; erewrite <- replay_disk_length; eauto.

    step.
    erewrite DLog.rep_hashmap_subset; eauto.
    rewrite vssync_vecs_length; auto.
    apply map_valid_vssync_vecs; auto.
    apply replay_disk_vssync_vecs_comm.
    erewrite DLog.rep_hashmap_subset; eauto.
  Qed.
Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (flush _ _ _) _) => apply flush_ok : prog.
Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
Hint Extern 1 ({{_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
Hint Extern 1 ({{_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
Hint Extern 1 ({{_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.
Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.
End MLog.
