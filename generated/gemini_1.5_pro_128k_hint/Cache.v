Require Import Mem.
Require Import List.
Require Import Prog ProgMonad.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import WordAuto.
Require Import Lia.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ListPred.
Require Import FunctionalExtensionality.
Import AddrMap.
Import ListNotations.
Set Implicit Arguments.
Definition eviction_state : Type := unit.
Definition eviction_init : eviction_state := tt.
Definition eviction_update (s : eviction_state) (a : addr) := s.
Definition eviction_choose (s : eviction_state) : (addr * eviction_state) := (0, s).
Definition cachemap := Map.t (valu * bool).
Record cachestate := mk_cs {
  CSMap : cachemap;
  CSMaxCount : nat;
  CSCount : nat;
  CSEvict : eviction_state
}.
Module BUFCACHE.
Definition writeback a (cs : cachestate) :=
    match (Map.find a (CSMap cs)) with
    | Some (v, true) =>
      Write a v ;;
      Ret (mk_cs (Map.add a (v, false) (CSMap cs)) (CSMaxCount cs) (CSCount cs) (CSEvict cs))
    | _ =>
      Ret cs
    end.
Definition evict a (cs : cachestate) :=
    cs <- writeback a cs;
    match Map.find a (CSMap cs) with
    | Some _ =>
      Ret (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSCount cs - 1) (CSEvict cs))
    | None =>
      Ret (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSCount cs) (CSEvict cs))
    end.
Definition maybe_evict (cs : cachestate) :=
    If (lt_dec (CSCount cs) (CSMaxCount cs)) {
      Ret cs
    } else {
      let (victim, evictor) := eviction_choose (CSEvict cs) in
      match (Map.find victim (CSMap cs)) with
      | Some _ =>
        cs <- evict victim (mk_cs (CSMap cs) (CSMaxCount cs) (CSCount cs) evictor);
        Ret cs
      | None => 
        match (Map.elements (CSMap cs)) with
        | nil => Ret cs
        | (a, v) :: tl =>
          cs <- evict a cs;
          Ret cs
        end
      end
    }.
Definition read a (cs : cachestate) :=
    cs <- maybe_evict cs;
    match Map.find a (CSMap cs) with
    | Some (v, dirty) => Ret ^(cs, v)
    | None =>
      AlertModified;;
      v <- Read a;
      Ret ^(mk_cs (Map.add a (v, false) (CSMap cs))
                 (CSMaxCount cs) (CSCount cs + 1) (eviction_update (CSEvict cs) a), v)
    end.
Definition write a v (cs : cachestate) :=
    cs <- maybe_evict cs;
    match Map.find a (CSMap cs) with
    | Some _ =>
      Ret (mk_cs (Map.add a (v, true) (CSMap cs))
                 (CSMaxCount cs) (CSCount cs) (eviction_update (CSEvict cs) a))
    | None =>
      Ret (mk_cs (Map.add a (v, true) (CSMap cs))
                 (CSMaxCount cs) (CSCount cs + 1) (eviction_update (CSEvict cs) a))
    end.
Definition begin_sync (cs : cachestate) :=
    Ret cs.
Definition sync a (cs : cachestate) :=
    cs <- writeback a cs;
    Ret cs.
Definition end_sync (cs : cachestate) :=
    Sync;;
    Ret cs.
Definition cache0 sz := mk_cs (Map.empty _) sz 0 eviction_init.
Definition init (cachesize : nat) :=
    Sync;;
    Ret (cache0 cachesize).
Definition read_array a i cs :=
    r <- read (a + i) cs;
    Ret r.
Definition write_array a i v cs :=
    cs <- write (a + i) v cs;
    Ret cs.
Definition sync_array a i cs :=
    cs <- sync (a + i) cs;
    Ret cs.
Definition size_valid cs :=
    Map.cardinal (CSMap cs) = CSCount cs /\
    Map.cardinal (CSMap cs) <= CSMaxCount cs /\
    CSMaxCount cs <> 0.
Definition addr_valid (d : rawdisk) (cm : cachemap) :=
    forall a, Map.In a cm -> d a <> None.
Definition addr_clean (cm : cachemap) a :=
    Map.find a cm = None \/ exists v, Map.find a cm = Some (v, false).
Definition addrs_clean cm al :=
    Forall (addr_clean cm) al.
Definition cachepred (cache : cachemap) (a : addr) (vs : valuset) : @pred _ addr_eq_dec valuset :=
    (match Map.find a cache with
    | None => a |+> vs
    | Some (v, false) => a |+> vs * [[ v = fst vs ]]
    | Some (v, true)  => exists v0, a |+> (v0, snd vs) * [[ v = fst vs /\ In v0 (snd vs) ]]
    end)%pred.
Notation mem_pred := (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _).
Definition rep (cs : cachestate) (m : rawdisk) : rawpred :=
    ([[ size_valid cs /\ addr_valid m (CSMap cs) ]] *
     mem_pred (cachepred (CSMap cs)) m)%pred.
Definition synpred (cache : cachemap) (a : addr) (vs : valuset) : @pred _ addr_eq_dec valuset :=
    (exists vsd, a |+> vsd *
    match Map.find a cache with
    | None =>  [[ vs = (fst vsd, nil) ]]
    | Some (v, false) => [[ vs = (fst vsd, nil) /\ v = fst vsd ]]
    | Some (v, true)  => [[ vs = (v, (fst vsd) :: nil) ]]
    end)%pred.
Definition synrep' (cs : cachestate) (m : rawdisk) : rawpred :=
    ([[ size_valid cs /\ addr_valid m (CSMap cs) ]] *
     mem_pred (synpred (CSMap cs)) m)%pred.
Definition synrep (cs : cachestate) (mbase m : rawdisk) : rawpred :=
    (rep cs mbase /\ synrep' cs m)%pred.
Theorem sync_invariant_cachepred : forall cache a vs,
    sync_invariant (cachepred cache a vs).
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Theorem sync_invariant_synpred : forall cache a vs,
    sync_invariant (synpred cache a vs).
(* hint proof tokens: 35 *)
Proof.
    unfold synpred; intros.
    destruct (Map.find a cache); eauto.
    destruct p; destruct b; eauto.
  Qed.
Hint Resolve sync_invariant_cachepred sync_invariant_synpred.
Theorem sync_invariant_rep : forall cs m,
    sync_invariant (rep cs m).
(* hint proof tokens: 14 *)
Proof.
    unfold rep; eauto.
  Qed.
Hint Resolve sync_invariant_rep.
Theorem sync_invariant_synrep' : forall cs m,
    sync_invariant (synrep' cs m).
(* hint proof tokens: 15 *)
Proof.
    unfold synrep'; eauto.
  Qed.
Hint Resolve sync_invariant_synrep'.
Theorem sync_invariant_synrep : forall cs mbase m,
    sync_invariant (synrep cs mbase m).
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Hint Resolve sync_invariant_synrep.
Lemma cachepred_remove_invariant : forall a a' v cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.remove a' cache) a v.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma cachepred_add_invariant : forall a a' v v' cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.add a' v' cache) a v.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma synpred_remove_invariant : forall a a' v cache,
    a <> a' -> synpred cache a v =p=> synpred (Map.remove a' cache) a v.
(* hint proof tokens: 25 *)
Proof.
    unfold synpred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.
Lemma synpred_add_invariant : forall a a' v v' cache,
    a <> a' -> synpred cache a v =p=> synpred (Map.add a' v' cache) a v.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma mem_pred_cachepred_remove_absorb : forall csmap d a w vs p_old,
    d a = Some (w, p_old) ->
    incl vs p_old ->
    mem_pred (cachepred csmap) (mem_except d a) * a |-> (w, vs) =p=>
    mem_pred (cachepred (Map.remove a csmap)) d.
Proof.
(* skipped proof tokens: 84 *)
Admitted.
Lemma size_valid_remove : forall cs a,
    size_valid cs ->
    Map.In a (CSMap cs) ->
    size_valid (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSCount cs - 1) (CSEvict cs)).
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma size_valid_remove_notin : forall cs a,
    size_valid cs ->
    ~ Map.In a (CSMap cs) ->
    size_valid (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSCount cs) (CSEvict cs)).
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Lemma size_valid_remove_cardinal_ok : forall cs a,
    size_valid cs ->
    Map.In a (CSMap cs) ->
    Map.cardinal (Map.remove a (CSMap cs)) < CSMaxCount cs.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Lemma size_valid_cache0 : forall cachesize,
    cachesize <> 0 ->
    size_valid (cache0 cachesize).
(* hint proof tokens: 37 *)
Proof.
    unfold size_valid, cache0; simpl; intros.
    rewrite Map.cardinal_1.
    rewrite MapProperties.elements_empty.
    intuition.
  Qed.
Lemma addr_valid_remove : forall d a cm,
    addr_valid d cm ->
    addr_valid d (Map.remove a cm).
(* hint proof tokens: 31 *)
Proof.
    unfold addr_valid; intros.
    apply H.
    eapply MapFacts.remove_in_iff; eauto.
  Qed.
Lemma addr_valid_empty : forall m,
    addr_valid m (Map.empty (valu * bool)).
(* hint proof tokens: 32 *)
Proof.
    unfold addr_valid; intros.
    apply MapFacts.empty_in_iff in H.
    exfalso; auto.
  Qed.
Lemma addr_valid_mem_valid : forall a cm c d,
    Map.find a cm = Some c ->
    addr_valid d cm ->
    exists vs, d a = Some vs.
(* hint proof tokens: 63 *)
Proof.
    intros.
    assert (Map.In a cm).
    apply MapFacts.in_find_iff.
    destruct (Map.find a cm); try congruence.
    specialize (H0 _ H1).
    destruct (d a); try congruence; eauto.
  Qed.
Lemma addr_valid_ptsto_subset : forall a cm c d,
    Map.find a cm = Some c ->
    addr_valid d cm ->
    exists (F : rawpred) vs, (F * a |+> vs)%pred d.
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Lemma mem_pred_cachepred_add_absorb_clean : forall csmap d a v vs,
    d a = Some (v, vs) ->
    mem_pred (cachepred csmap) (mem_except d a) ✶ a |+> (v, vs) =p=>
    mem_pred (cachepred (Map.add a (v, false) csmap)) d.
(* hint proof tokens: 84 *)
Proof.
    intros.
    eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
    unfold cachepred at 3.
    rewrite MapFacts.add_eq_o by auto.
    unfold ptsto_subset; cancel; eauto.
    rewrite mem_pred_pimpl_except; eauto.
    intros; apply cachepred_add_invariant; eauto.
  Qed.
Lemma addr_clean_cachepred_remove : forall cs a d F vs,
    addr_clean (CSMap cs) a ->
    (F * a |+> vs)%pred d ->
    mem_pred (cachepred (CSMap cs)) d =p=> mem_pred (cachepred (Map.remove a (CSMap cs))) d.
Proof.
(* skipped proof tokens: 140 *)
Admitted.
Lemma size_valid_add_in : forall cs evictor vv v a,
    Map.find a (CSMap cs) = Some v ->
    size_valid cs ->
    size_valid (mk_cs (Map.add a vv (CSMap cs)) (CSMaxCount cs) (CSCount cs) evictor).
(* hint proof tokens: 70 *)
Proof.
    unfold size_valid; intuition; simpl.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
  Qed.
Lemma size_valid_add : forall cs evictor vv a,
    Map.cardinal (CSMap cs) < CSMaxCount cs ->
    Map.find a (CSMap cs) = None ->
    size_valid cs ->
    size_valid (mk_cs (Map.add a vv (CSMap cs)) (CSMaxCount cs) (CSCount cs + 1) evictor).
(* hint proof tokens: 144 *)
Proof.
    unfold size_valid; intuition; simpl.

    destruct (Map.find a0 (CSMap cs)) eqn:?; try congruence.
    rewrite map_add_cardinal. lia.
    intuition repeat deex.
    apply MapFacts.find_mapsto_iff in H3; congruence.

    destruct (Map.find a0 (CSMap cs)) eqn:?.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
    rewrite map_add_cardinal. lia.
    intuition repeat deex.
    apply MapFacts.find_mapsto_iff in H3; congruence.
  Qed.
Lemma addr_valid_add : forall d cm a vv v,
    d a = Some v ->
    addr_valid d cm ->
    addr_valid d (Map.add a vv cm).
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma addr_valid_upd : forall a vs d cm,
    addr_valid d cm ->
    addr_valid (upd d a vs) cm.
(* hint proof tokens: 42 *)
Proof.
    unfold addr_valid; intros.
    destruct (addr_eq_dec a a0); subst.
    rewrite upd_eq; congruence.
    rewrite upd_ne; auto.
  Qed.
Lemma addr_valid_upd_add : forall a vs vc d cm,
    addr_valid d cm ->
    addr_valid (upd d a vs) (Map.add a vc cm).
(* hint proof tokens: 36 *)
Proof.
    intros.
    eapply addr_valid_add; eauto.
    apply upd_eq; auto.
    apply addr_valid_upd; auto.
  Qed.
Lemma incl_vsmerge_in : forall w v0 l l',
    incl l (vsmerge (w, (vsmerge (v0, l')))) ->
    In v0 (vsmerge (w, l')) ->
    incl l (vsmerge (w, l')).
(* hint proof tokens: 42 *)
Proof.
    unfold vsmerge, incl; simpl; intuition subst.
    specialize (H _ H0); intuition.
    specialize (H _ H0); intuition subst; auto.
  Qed.
Lemma incl_vsmerge_in' : forall w v0 l l',
    incl l (vsmerge (w, (vsmerge (v0, l')))) ->
    In v0 l' ->
    incl l (vsmerge (w, l')).
(* hint proof tokens: 35 *)
Proof.
    unfold vsmerge, incl; simpl; intuition subst.
    specialize (H _ H1); intuition subst.
    right; auto.
  Qed.
Lemma incl_vsmerge_in'' : forall a v l,
    In v l ->
    incl a (vsmerge (v, l)) ->
    incl a l.
(* hint proof tokens: 33 *)
Proof.
    unfold vsmerge, incl; intuition simpl in *.
    specialize (H0 _ H1); intuition subst; auto.
  Qed.
Local Hint Resolve incl_vsmerge_in incl_vsmerge_in' incl_vsmerge_in''.
Lemma in_vsmerge_hd : forall w l,
    In w (vsmerge (w, l)).
(* hint proof tokens: 14 *)
Proof.
    unfold vsmerge; intuition.
  Qed.
Lemma in_incl_trans: forall A (a b : list A) x,
    incl a b ->
    In x a ->
    In x b.
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Lemma incl_vsmerge_trans: forall a v l l',
    incl a (vsmerge (v, l')) ->
    incl l' l ->
    incl a (vsmerge (v, l)).
(* hint proof tokens: 28 *)
Proof.
    unfold incl, vsmerge; simpl; intros.
    specialize (H _ H1); intuition.
  Qed.
Lemma incl_vsmerge_in_trans : forall a v l l',
    In v l ->
    incl l' l ->
    incl a (vsmerge (v, l')) ->
    incl a l.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Local Hint Resolve in_vsmerge_hd incl_vsmerge_trans incl_vsmerge_in_trans.
Opaque vsmerge.
Theorem writeback_ok' : forall a cs,
    {< vs0,
    PRE:hm
      a |+> vs0
    POST:hm' RET:cs' exists v,
      ( [[ Map.find a (CSMap cs) = Some (v, true) /\
         cs' = mk_cs (Map.add a (v, false) (CSMap cs)) (CSMaxCount cs) (CSCount cs) (CSEvict cs) ]] *
         a |+> (v, vsmerge vs0)) \/
      ( [[ (Map.find a (CSMap cs) = None \/
          exists v, Map.find a (CSMap cs) = Some (v, false)) /\ cs' = cs ]] * a |+> vs0 )
    CRASH:hm'
      a |+> vs0
    >} writeback a cs.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Theorem writeback_ok : forall a cs,
    {< d vs (F : rawpred),
    PRE:hm
      rep cs d * [[ (F * a |+> vs)%pred d ]]
    POST:hm' RET:cs'
      rep cs' d * [[ addr_clean (CSMap cs') a ]] * 
      [[ Map.In a (CSMap cs) -> Map.In a (CSMap cs') ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} writeback a cs.
(* hint proof tokens: 380 *)
Proof.
    unfold writeback, rep; intros.

    prestep; norml; unfold stars; simpl;
    denote ptsto_subset as Hx; apply ptsto_subset_valid' in Hx; repeat deex.

    
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2.
      destruct (Map.find a (CSMap cs)) eqn:Hm; try congruence.
      destruct p; destruct b; try congruence.
      cancel.
      step.
      erewrite <- upd_nop with (m := d) at 2 by eauto.
      rewrite <- mem_pred_absorb with (hm := d) (a := a).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity.
      unfold ptsto_subset; cancel; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      cancel.
      eapply size_valid_add_in; eauto.
      eapply addr_valid_add; eauto.
      unfold addr_clean; right; eexists; simpl.
      apply MapFacts.add_eq_o; auto.
      eapply MapFacts.add_in_iff; eauto.

      
      unfold ptsto_subset; cancel; eauto.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3; rewrite Hm.
      unfold ptsto_subset; cancel; eauto.

    
    - cancel.
      step.
      unfold addr_clean; right; eexists; eauto.
      cancel.

    
    - cancel.
      step.
      unfold addr_clean; left; auto.
      cancel.

    Unshelve. all: try exact addr_eq_dec.
  Qed.
Hint Extern 1 ({{_}} Bind (writeback _ _) _) => apply writeback_ok : prog.
Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (synrep _ _ _) (synrep _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (mem_pred ?p _) (mem_pred ?p _)) => constructor : okToUnify.
Theorem evict_ok : forall a cs,
    {< d vs (F : rawpred),
    PRE:hm
      rep cs d * [[ (F * a |+> vs)%pred d ]]
    POST:hm' RET:cs'
      rep cs' d *
      [[ ~ Map.In a (CSMap cs') ]] *
      [[ Map.In a (CSMap cs) -> Map.cardinal (CSMap cs') < CSMaxCount cs' ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} evict a cs.
Proof.
(* skipped proof tokens: 167 *)
Admitted.
Hint Extern 1 ({{_}} Bind (evict _ _) _) => apply evict_ok : prog.
Theorem maybe_evict_ok : forall cs,
    {< d,
    PRE:hm
      rep cs d
    POST:hm' RET:cs
      rep cs d * [[ Map.cardinal (CSMap cs) < CSMaxCount cs ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} maybe_evict cs.
(* hint proof tokens: 306 *)
Proof.
    unfold maybe_evict; intros.
    step.
    unfold rep, size_valid in *; step.

    prestep; unfold rep; norml; unfold stars; simpl.

    
    - edestruct addr_valid_ptsto_subset; eauto.
      norm. 2: intuition eauto. cancel.
      step.
      unfold rep; cancel.
      denote ( _ -> _ < _) as Hx; apply Hx.
      apply MapFacts.in_find_iff; congruence.

    
    - unfold size_valid in *; cancel.
      rewrite Map.cardinal_1, Heql; simpl; lia.

    
    - clear Heqo.
      assert (Map.find k (CSMap cs) = Some (p0_1, p0_2)).
      rewrite MapFacts.elements_o, Heql; simpl.
      destruct (MapFacts.eqb k k) eqn:?; auto.
      contradict Heqb.
      unfold MapFacts.eqb, MapOrdProperties.P.F.eq_dec.
      destruct (Nat.eq_dec k k); congruence.

      edestruct addr_valid_ptsto_subset; eauto; repeat deex.
      norm. 2: intuition eauto. cancel.
      step.
      unfold rep; cancel.
      denote ( _ -> _ < _) as Hx; apply Hx.
      apply MapFacts.in_find_iff; congruence.

    Unshelve. all: eauto; exact 0.
  Qed.
Hint Extern 1 ({{_}} Bind (maybe_evict _) _) => apply maybe_evict_ok : prog.
Theorem read_ok : forall cs a,
    {< d (F : rawpred) v vs,
    PRE:hm
      rep cs d * [[ (F * a |+> (v, vs))%pred d ]]
    POST:hm' RET:^(cs, r)
      rep cs d * [[ r = v ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} read a cs.
Proof.
(* skipped proof tokens: 296 *)
Admitted.
Theorem write_ok' : forall cs a v,
    {< d (F : rawpred) v0,
    PRE:hm
      rep cs d * [[ (F * a |+> v0)%pred d ]]
    POST:hm' RET:cs
      exists d',
      rep cs d' * [[ (F * a |+> (v, vsmerge v0))%pred d' ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} write a v cs.
Proof.
(* skipped proof tokens: 689 *)
Admitted.
Lemma cachepred_synpred : forall cm a vs,
    cachepred cm a vs =p=> exists vs', synpred cm a vs' *
      [[ fst vs' = fst vs /\ incl (snd vs') (snd vs) /\
         (addr_clean cm a -> snd vs' = nil) ]].
(* hint proof tokens: 72 *)
Proof.
    unfold cachepred, synpred, addr_clean; intros.
    destruct (Map.find a cm) eqn:?.
    destruct p, b; cancel.
    apply incl_cons; auto; apply incl_nil.
    deex; congruence.
    apply incl_nil.
    cancel.
    apply incl_nil.
  Qed.
Definition avs_match (avs1 avs2 : addr * valuset)  : Prop :=
    let '(a1, vs1) := avs1 in let '(a2, vs2) := avs2 in
    a2 = a1 /\ (fst vs2 = fst vs1) /\ incl (snd vs2) (snd vs1).
Definition nil_if_clean cm (avs : addr * valuset)  : Prop :=
    let '(a, vs) := avs in addr_clean cm a -> snd vs = nil.
Lemma listpred_cachepred_synpred : forall l cm,
    listpred (fun av => cachepred cm (fst av) (snd av)) l =p=> exists l',
    listpred (fun av => synpred cm (fst av) (snd av)) l' *
    [[ Forall2 avs_match l l' /\ Forall (nil_if_clean cm) l' ]].
Proof.
(* skipped proof tokens: 81 *)
Admitted.
Lemma avs_match_map_fst_eq : forall l l',
    Forall2 avs_match l l' ->
    map fst l' = map fst l.
(* hint proof tokens: 35 *)
Proof.
    unfold avs_match; induction 1; simpl; auto.
    f_equal; auto.
    destruct x, y; intuition.
  Qed.
Lemma avs2mem_mem_match : forall V l l',
    map fst l' = map fst l ->
    @mem_match _ V _ (avs2mem addr_eq_dec l) (avs2mem addr_eq_dec l').
(* hint proof tokens: 62 *)
Proof.
    induction l; destruct l'; simpl; try congruence; intros; cbn.
    cbv; intuition.
    destruct a, p; simpl in *.
    inversion H; subst.
    apply mem_match_upd.
    apply IHl; auto.
  Qed.
Lemma addr_valid_mem_match : forall d d' cm,
    mem_match d d' ->
    addr_valid d cm ->
    addr_valid d' cm.
(* hint proof tokens: 49 *)
Proof.
    unfold addr_valid; intros.
    specialize (H0 _ H1).
    edestruct mem_match_cases with (a := a); eauto; intuition.
    repeat deex; congruence.
  Qed.
Lemma avs_match_addr_valid : forall l l' cm,
    Forall2 avs_match l l' ->
    addr_valid (avs2mem addr_eq_dec l) cm ->
    addr_valid (avs2mem addr_eq_dec l') cm.
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Lemma avs_match_addr_valid' : forall l l' cm,
    Forall2 avs_match l' l ->
    addr_valid (avs2mem addr_eq_dec l) cm ->
    addr_valid (avs2mem addr_eq_dec l') cm.
Proof.
(* skipped proof tokens: 47 *)
Admitted.
Lemma avs_match_possible_sync : forall l l',
    Forall2 avs_match l l' ->
    possible_sync (avs2mem addr_eq_dec l) (avs2mem addr_eq_dec l').
Proof.
(* skipped proof tokens: 153 *)
Admitted.
Lemma avs_match_sync_invariant : forall l l' F,
    Forall2 avs_match l l' ->
    sync_invariant F ->
    F (avs2mem addr_eq_dec l) ->
    F (avs2mem addr_eq_dec l').
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma synpred_cachepred_sync : forall vs cm a,
    sync_xform (synpred cm a vs) =p=> cachepred cm a vs.
(* hint proof tokens: 104 *)
Proof.
    unfold cachepred, synpred; intros.
    rewrite sync_xform_exists_comm.
    apply pimpl_exists_l; intro vs0.
    rewrite sync_xform_sep_star_dist.
    destruct vs0 as [v0 l0].
    destruct (Map.find a cm) eqn:?; try destruct p, b;
    rewrite sync_xform_lift_empty, sync_xform_ptsto_subset_precise;
    unfold ptsto_subset; cancel; apply incl_nil.
  Qed.
Lemma sync_xform_listpred_synpred_cachepred : forall l cm,
    sync_xform (listpred (fun x => synpred cm (fst x) (snd x)) l) =p=>
    listpred (fun x => cachepred cm (fst x) (snd x)) l.
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Lemma rep_synrep_split : forall cs d F,
    rep cs d /\ (exists d', synrep' cs d' * [[ F d' ]]) =p=>
    (exists d', (rep cs d ⋀ synrep' cs d') * [[ F d' ]]).
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Lemma synrep_rep : forall cs d0 d,
    synrep cs d0 d =p=> rep cs d0.
(* hint proof tokens: 24 *)
Proof.
    unfold synrep; intros.
    apply pimpl_l_and; eauto.
  Qed.
Lemma nil_if_clean_synced : forall l a cm vs,
    Forall (nil_if_clean cm) l ->
    addr_clean cm a ->
    avs2mem addr_eq_dec l a = Some vs ->
    NoDup (map fst l) ->
    snd vs = nil.
(* hint proof tokens: 104 *)
Proof.
    induction l; simpl; intros.
    cbv in H1; congruence.
    inversion H; inversion H2; subst.
    destruct a; cbn in H1; simpl in *.
    destruct (addr_eq_dec n a0); subst.
    rewrite upd_eq in H1 by auto; inversion H1; subst; eauto.
    rewrite upd_ne in H1 by auto.
    eapply IHl; eauto; simpl in *.
  Qed.
Lemma rep_synrep : forall (F : rawpred) d0 cs,
    F d0 ->
    sync_invariant F ->
    rep cs d0 =p=> exists d, synrep cs d0 d * 
      [[ F d /\ forall a vs, addr_clean (CSMap cs) a -> d a = Some vs -> snd vs = nil ]].
Proof.
(* skipped proof tokens: 153 *)
Admitted.
Theorem begin_sync_ok : forall cs,
    {< d F,
    PRE:hm
      rep cs d * [[ F d /\ sync_invariant F ]]
    POST:hm' RET:cs exists d',
      synrep cs d d' * [[ F d' ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} begin_sync cs.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Theorem end_sync_ok : forall cs,
    {< d0 d,
    PRE:hm
      synrep cs d0 d
    POST:hm' RET:cs
      rep cs d
    CRASH:hm'
      exists cs', rep cs' d0
    >} end_sync cs.
(* hint proof tokens: 189 *)
Proof.
    unfold end_sync, synrep, synrep'.
    step.
    prestep; unfold mem_pred.
    norml; unfold stars, mem_pred_one; simpl.
    rewrite sync_xform_sep_star_dist. rewrite sync_xform_and_dist.
    rewrite sep_star_and_distr'. rewrite pimpl_r_and.
    unfold rep, mem_pred, mem_pred_one. 
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    norml; unfold stars; simpl.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    cancel.
    rewrite sync_xform_listpred_synpred_cachepred.
    rewrite sync_xform_sync_invariant by auto.
    cancel.
    all: auto.
    rewrite pimpl_l_and.
    cancel.
  Qed.
Theorem sync_ok' : forall cs a,
    {< d0 d (F F' : rawpred) v0 v',
    PRE:hm
      synrep cs d0 d * [[ sync_invariant F ]] *
      [[ (F * a |+> v0)%pred d ]] *
      [[ (F' * a |+> v')%pred d0 ]]
    POST:hm' RET:cs exists d,
      synrep cs d0 d *
      [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH:hm'
      exists cs', rep cs' d0
    >} sync a cs.
Proof.
(* original proof tokens: 1656 *)

(* No more tactics to try *)
Admitted.

Theorem sync_synrep_helper_1 : forall m cs d0 d a (F : @pred _ addr_eq_dec _) v,
    synrep cs d0 d m ->
    (F * a |+> v)%pred d ->
    exists (F0 : @pred _ addr_eq_dec _) v0,
    (F0 * a |+> v0)%pred d0.
(* hint proof tokens: 216 *)
Proof.
    unfold synrep, rep, synrep', ptsto_subset; intros.
    case_eq (d0 a); intros.
    - destruct p.
      eapply any_sep_star_ptsto in H1.
      pred_apply.
      safecancel.
      eassign (w, l).
      eassign l.
      cancel.
      firstorder.
    - destruct H.
      destruct_lift H.
      destruct_lift H2.
      destruct_lift H0.
      apply ptsto_valid' in H0.
      eapply mem_pred_absent_lm in H; eauto.
      eapply mem_pred_absent_hm in H2; eauto.
      congruence.

      unfold synpred, ptsto_subset; intros.
      destruct (Map.find a0 (CSMap cs)); try destruct p; try destruct b; cancel.

      unfold cachepred, ptsto_subset; intros.
      destruct (Map.find a0 (CSMap cs)); try destruct p; try destruct b; cancel.
  Qed.
Theorem sync_synrep_helper_2 : forall cs d0 d a (F : @pred _ addr_eq_dec _) v,
    (F * a |+> v)%pred d ->
    synrep cs d0 d =p=> synrep cs d0 d * exists (F0 : @pred _ addr_eq_dec _) v0,
    [[ (F0 * a |+> v0)%pred d0 ]].
(* hint proof tokens: 39 *)
Proof.
    unfold pimpl; intros.
    eapply sync_synrep_helper_1 in H; eauto; repeat deex.
    pred_apply; cancel.
  Qed.
Theorem sync_ok : forall cs a,
    {< d0 d (F : rawpred) v0,
    PRE:hm
      synrep cs d0 d *
      [[ (F * a |+> v0)%pred d ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:cs exists d,
      synrep cs d0 d *
      [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH:hm'
      exists cs', rep cs' d0
    >} sync a cs.
(* hint proof tokens: 63 *)
Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply sync_ok'.
    intros; norml; unfold stars; simpl.
    rewrite sync_synrep_helper_2 by eauto.
    safecancel.
    eauto.
    step.
  Qed.
Hint Extern 1 ({{_}} Bind (read _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (sync _ _) _) => apply sync_ok : prog.
Hint Extern 1 ({{_}} Bind (begin_sync _) _) => apply begin_sync_ok : prog.
Hint Extern 1 ({{_}} Bind (end_sync _) _) => apply end_sync_ok : prog.
Definition sync_one a (cs : cachestate) :=
    cs <- begin_sync cs;
    cs <- sync a cs;
    cs <- end_sync cs;
    Ret cs.
Theorem sync_one_ok : forall cs a,
    {< d (F : rawpred) v0,
    PRE:hm
      rep cs d * [[ sync_invariant F /\ (F * a |+> v0)%pred d ]]
    POST:hm' RET:cs
      exists d',
      rep cs d' * [[ (F * a |+> (fst v0, nil))%pred d' ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} sync_one a cs.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Definition sync_two a1 a2 (cs : cachestate) :=
    cs <- begin_sync cs;
    cs <- sync a1 cs;
    cs <- sync a2 cs;
    cs <- end_sync cs;
    Ret cs.
Theorem sync_two_ok : forall cs a1 a2,
    {< d (F : rawpred) v1 v2,
    PRE:hm
      rep cs d * [[ sync_invariant F /\ (F * a1 |+> v1 * a2 |+> v2)%pred d ]]
    POST:hm' RET:cs
      exists d',
      rep cs d' * [[ (F * a1 |+> (fst v1, nil) * a2 |+> (fst v2, nil))%pred d' ]]
    CRASH:hm'
      exists cs' d, rep cs' d
    >} sync_two a1 a2 cs.
Proof.
(* skipped proof tokens: 16 *)
Admitted.
Lemma xform_cachepred_ptsto : forall m a vs,
    crash_xform (cachepred m a vs) =p=> 
      exists v, [[ In v (vsmerge vs) ]] * a |=> v.
Proof.
(* skipped proof tokens: 115 *)
Admitted.
Lemma xform_mem_pred_cachepred : forall cs hm,
    crash_xform (mem_pred (cachepred cs) hm) =p=> 
      exists m', [[ possible_crash hm m' ]] *
      mem_pred (cachepred (Map.empty _)) m'.
Proof.
(* skipped proof tokens: 221 *)
Admitted.
Lemma crash_xform_rep: forall cs m,
    crash_xform (rep cs m) =p=>
       exists m' cs', [[ possible_crash m m' ]] * rep cs' m'.
(* hint proof tokens: 87 *)
Proof.
    unfold rep; intros.
    xform_norm.
    rewrite xform_mem_pred_cachepred.
    cancel.
    eassign (cache0 (CSMaxCount cs)); cancel.
    all: unfold cache0; simpl; eauto.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    eapply MapFacts.empty_in_iff; eauto.
  Qed.
Lemma crash_xform_rep_pred : forall cs m (F : pred),
    F%pred m ->
    crash_xform (rep cs m) =p=>
    exists m' cs', rep cs' m' * [[ (crash_xform F)%pred m' ]].
(* hint proof tokens: 33 *)
Proof.
    intros.
    rewrite crash_xform_rep.
    norm. cancel. split; auto.
    exists m; eauto.
  Qed.
Lemma listpred_cachepred_mem_except : forall a v l m buf,
    listpred (mem_pred_one (cachepred buf)) ((a, v) :: l) m ->
    listpred (mem_pred_one (cachepred buf)) l (mem_except m a).
(* hint proof tokens: 74 *)
Proof.
    unfold mem_pred_one; simpl; intros.
    unfold cachepred at 1 in H.
    destruct (Map.find a buf) eqn: Heq; try destruct p, b;
    unfold ptsto_subset in H; destruct_lift H;
    eapply ptsto_mem_except; pred_apply; eauto.
  Qed.
Lemma mem_pred_cachepred_refl : forall m m' m'' cm,
    mem_pred (cachepred cm) m' m'' ->
    mem_match m m' ->
    mem_pred (cachepred (Map.empty (valu * bool))) m m.
Proof.
(* skipped proof tokens: 433 *)
Admitted.
Lemma mem_pred_cachepred_refl_arrayN : forall l start m,
    arrayN (@ptsto _ _ _) start l m ->
    mem_pred (cachepred (Map.empty (valu * bool))) m m.
Proof.
(* skipped proof tokens: 281 *)
Admitted.
Lemma arrayS_arrayN : forall l start,
    arrayS start l =p=> exists l', arrayN (@ptsto _ _ _) start l'.
(* hint proof tokens: 63 *)
Proof.
    induction l; simpl; intros.
    exists nil; simpl; eauto.
    rewrite IHl.
    unfold ptsto_subset.
    norml; unfold stars; simpl.
    exists ((a_cur, old) :: l'); simpl.
    pred_apply; cancel.
  Qed.
Lemma mem_pred_cachepred_refl_arrayS : forall l start m,
    arrayS start l m ->
    mem_pred (cachepred (Map.empty (valu * bool))) m m.
(* hint proof tokens: 40 *)
Proof.
    intros.
    apply arrayS_arrayN in H.
    destruct_lift H.
    eapply mem_pred_cachepred_refl_arrayN; eauto.
  Qed.
Lemma possible_crash_mem_match : forall (m1 m2 : rawdisk),
    possible_crash m1 m2 ->
    @mem_match _ _ addr_eq_dec m1 m2.
Proof.
(* skipped proof tokens: 52 *)
Admitted.
Lemma listpred_cachepred_notin : forall cs l m a,
    ~ In a (map fst l) ->
    listpred (mem_pred_one (cachepred cs)) l m ->
    m a = None.
(* hint proof tokens: 120 *)
Proof.
    induction l; intros; eauto.
    destruct a; subst; simpl in *; intuition.
    unfold mem_pred_one at 1, cachepred at 1 in H0; simpl in *.
    destruct (Map.find n cs) eqn: Heq; try destruct p0, b;
    unfold ptsto_subset in *; destruct_lifts;
    eapply notindomain_mem_except with (a' := n); eauto;
    apply IHl; eauto;
    eapply ptsto_mem_except; eauto.
  Qed.
Lemma mem_pred_cachepred_none : forall (m1 m2 : mem) cs a,
    mem_pred (cachepred cs) m1 m2 ->
    m1 a = None ->
    m2 a = None.
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma mem_pred_cachepred_some : forall (m1 m2 : mem) cs a v,
    mem_pred (cachepred cs) m1 m2 ->
    synced_mem m1 ->
    m1 a = Some v ->
    m2 a = Some v.
(* hint proof tokens: 135 *)
Proof.
    intros.
    specialize (H0 a); intuition try congruence; repeat deex.
    rewrite H0 in H1; inversion_clear H1; subst.
    eapply mem_pred_extract in H; eauto.
    unfold cachepred in H at 2.
    destruct (Map.find a cs) eqn:?; try destruct p, b;
    unfold ptsto_subset in H; destruct_lift H;
    denote incl as Hx; apply incl_in_nil in Hx; subst.
    intuition.
    eapply ptsto_valid'; eauto.
    eapply ptsto_valid'; eauto.
  Qed.
Lemma mem_pred_cachepred_eq : forall (m1 m2 : mem) cs,
    mem_pred (cachepred cs) m1 m2 ->
    synced_mem m1 ->
    m1 = m2.
(* hint proof tokens: 58 *)
Proof.
    intros.
    apply functional_extensionality; intros.
    destruct (m1 x) eqn: Heq.
    erewrite mem_pred_cachepred_some; eauto.
    eapply mem_pred_cachepred_none in H; eauto.
  Qed.
Lemma mem_pred_possible_crash_trans : forall m m1 m2 cs,
    possible_crash m m1 ->
    mem_pred (cachepred cs) m1 m2 ->
    possible_crash m1 m2.
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_rep_r: forall m m' cs',
    possible_crash m m' ->
    rep cs' m' =p=> crash_xform (rep (cache0 (CSMaxCount cs')) m).
Proof.
(* skipped proof tokens: 121 *)
Admitted.
Lemma crash_xform_rep_r_pred : forall cs m (F : pred),
    (crash_xform F)%pred m ->
    rep cs m =p=> exists m', crash_xform (rep (cache0 (CSMaxCount cs)) m') * [[ F m' ]].
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Definition init_load := init.
Definition init_recover := init.
Lemma sync_xform_cachepred : forall m a vs,
    sync_xform (cachepred m a vs) =p=> 
      exists v, [[ In v (vsmerge vs) ]] * a |=> v.
Proof.
(* skipped proof tokens: 135 *)
Admitted.
Lemma sync_xform_mem_pred_cachepred : forall cm m,
    sync_xform (mem_pred (cachepred cm) m) =p=> exists m',
      mem_pred (cachepred (Map.empty (valu * bool))) m' * [[ possible_crash m m' ]].
(* hint proof tokens: 221 *)
Proof.
    intros.
    rewrite sync_xform_mem_pred.
    unfold mem_pred at 1.
    xform_norm; subst.

    rename hm_avs into l.
    revert H; revert l.
    induction l; simpl; intros.
    cancel.
    apply mem_pred_empty_mem.
    unfold possible_crash; intuition.

    inversion H; destruct a; subst; simpl in *.
    unfold mem_pred_one; simpl.

    rewrite IHl by auto.
    xform_norm.
    rewrite sync_xform_cachepred.
    norml; unfold stars; simpl.
    apply pimpl_exists_r.
    exists (upd m' n (v, nil)).
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3; unfold ptsto_subset.
    rewrite MapFacts.empty_o; cancel.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    apply possible_crash_upd; eauto.
  Qed.
Theorem init_recover_ok : forall cachesize,
    {< d F,
    PRE:hm
      exists cs, rep cs d *
      [[ F d ]] * [[ cachesize <> 0 ]]
    POST:hm' RET:cs
      exists d', rep cs d' * [[ (crash_xform F) d' ]]
    CRASH:hm'
      exists cs, rep cs d
    >} init_recover cachesize.
Proof.
(* skipped proof tokens: 115 *)
Admitted.
Hint Extern 1 ({{_}} Bind (init_recover _) _) => apply init_recover_ok : prog.
Lemma sync_xform_arrayS : forall l start,
    sync_xform (arrayS start l) =p=> arrayS start l.
(* hint proof tokens: 52 *)
Proof.
    induction l; simpl; intros.
    rewrite sync_xform_emp; cancel.
    rewrite sync_xform_sep_star_dist.
    rewrite sync_xform_ptsto_subset_preserve.
    rewrite IHl.
    cancel.
  Qed.
Theorem init_load_ok : forall cachesize,
    {!< disk,
    PRE:vm,hm
      arrayS 0 disk *
      [[ cachesize <> 0 ]]
    POST:vm',hm' RET:cs
      exists d,
      rep cs d *
      [[ arrayS 0 disk d ]] *
      [[ vm' = vm ]]
    CRASH:hm'
      arrayS 0 disk
    >!} init_load cachesize.
Proof.
(* skipped proof tokens: 173 *)
Admitted.
Hint Extern 1 ({{_}} Bind (init_load _) _) => apply init_load_ok : prog.
Theorem write_ok : forall cs a v,
    {< d (F : rawpred) v0,
    PRE:hm
      rep cs d * [[ (F * a |+> v0)%pred d ]]
    POST:hm' RET:cs
      exists d',
      rep cs d' * [[ (F * a |+> (v, vsmerge v0))%pred d' ]]
    XCRASH:hm'
      exists cs' d', rep cs' d' *
      [[  (F * a |+> (v, vsmerge v0))%pred d' ]]
    >} write a v cs.
(* hint proof tokens: 235 *)
Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel.
    cancel.
    xcrash_rewrite.

    rewrite crash_xform_rep.
    unfold rep at 1; xform_norm.
    edestruct ptsto_subset_valid' with (a := a); eauto; intuition.
    edestruct possible_crash_sel_exis; eauto; intuition.
    rewrite mem_pred_extract with (a := a) by eauto.

    cancel; xform_normr.
    rewrite <- crash_xform_rep_r.
    unfold rep; cancel.
    eapply pimpl_trans2.
    eapply mem_pred_absorb_nop with (a := a).
    2: apply pimpl_refl.
    eauto.
    eauto.
    eauto.
    eapply ptsto_subset_upd; eauto.
    2: eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    2: apply incl_tl; apply incl_refl.
    apply incl_cons2; auto.
  Qed.
Theorem read_array_ok : forall a i cs,
    {< d F vs,
    PRE:hm
      rep cs d * [[ (F * arrayN ptsto_subset a vs)%pred d ]] * [[ i < length vs ]]
    POST:hm' RET:^(cs, v)
      rep cs d * [[ v = fst (selN vs i ($0, nil)) ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} read_array a i cs.
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Lemma write_array_xcrash_ok : forall cs d F a i v vs,
    (F * arrayN ptsto_subset a vs)%pred d ->
    i < length vs ->
    crash_xform (rep cs d) =p=>
    crash_xform (exists cs' d', rep cs' d' *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]).
Proof.
(* skipped proof tokens: 228 *)
Admitted.
Theorem write_array_ok : forall a i v cs,
    {< d F vs,
    PRE:hm
      rep cs d * [[ (F * arrayN ptsto_subset a vs)%pred d ]] * [[ i < length vs ]]
    POST:hm' RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]
    XCRASH:hm' exists cs' d',
      rep cs' d' *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]
    >} write_array a i v cs.
(* hint proof tokens: 115 *)
Proof.
    unfold write_array, vsupd.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel.

    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite surjective_pairing with (p := selN vs i ($0, nil)).
    cancel.

    step.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.

    cancel.
    xcrash_rewrite.
    apply write_array_xcrash_ok; auto.
  Qed.
Theorem sync_array_ok : forall a i cs,
    {< d0 d (F : rawpred) vs,
    PRE:hm
      synrep cs d0 d *
      [[ (F * arrayN ptsto_subset a vs)%pred d ]] * 
      [[ i < length vs /\ sync_invariant F ]]
    POST:hm' RET:cs exists d',
      synrep cs d0 d' *
      [[ (F * arrayN ptsto_subset a (vssync vs i))%pred d' ]]
    CRASH:hm'
      exists cs', rep cs' d0
    >} sync_array a i cs.
(* hint proof tokens: 59 *)
Proof.
    unfold sync_array, vssync.
    safestep.
    rewrite isolateN_fwd with (i:=i) by auto; cancel.
    eauto.
    step.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.
Hint Extern 1 ({{_}} Bind (write _ _ _) _) => apply write_ok : prog.
Hint Extern 1 ({{_}} Bind (read_array _ _ _) _) => apply read_array_ok : prog.
Hint Extern 1 ({{_}} Bind (write_array _ _ _ _) _) => apply write_array_ok : prog.
Hint Extern 1 ({{_}} Bind (sync_array _ _ _) _) => apply sync_array_ok : prog.
Definition read_range A a nr (vfold : A -> valu -> A) a0 cs :=
    let^ (cs, r) <- ForN i < nr
    Ghost [ F crash d vs ]
    Loopvar [ cs pf ]
    Invariant
      rep cs d * [[ (F * arrayN ptsto_subset a vs)%pred d ]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) a0 ]]
    OnCrash  crash
    Begin
      let^ (cs, v) <- read_array a i cs;
      Ret ^(cs, vfold pf v)
    Rof ^(cs, a0);
    Ret ^(cs, r).
Definition write_range a l cs :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN ptsto_subset a (vsupd_range vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      cs <- write_array a i (selN l i $0) cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.
Definition sync_range a nr cs :=
    let^ (cs) <- ForN i < nr
    Ghost [ F crash vs d0 ]
    Loopvar [ cs ]
    Invariant
      exists d', synrep cs d0 d' *
      [[ (F * arrayN ptsto_subset a (vssync_range vs i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.
Definition write_vecs a l cs :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      let v := selN l i (0, $0) in
      cs <- write_array a (fst v) (snd v) cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.
Definition sync_vecs a l cs :=
    let^ (cs) <- ForEach i irest l
    Ghost [ F crash vs d0 ]
    Loopvar [ cs ]
    Invariant
      exists d' iprefix, synrep cs d0 d' *
      [[ iprefix ++ irest = l ]] *
      [[ (F * arrayN ptsto_subset a (vssync_vecs vs iprefix))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;
      Ret ^(cs)
    Rof ^(cs);
    Ret cs.
Definition sync_vecs_now a l cs :=
    cs <- begin_sync cs;
    cs <- sync_vecs a l cs;
    cs <- end_sync cs;
    Ret cs.
Definition sync_all cs :=
    cs <- sync_vecs_now 0 (map fst (Map.elements (CSMap cs))) cs;
    Ret cs.
Hint Extern 0 (okToUnify (arrayN ?pts ?a _) (arrayN ?pts ?a _)) => constructor : okToUnify.
Theorem read_range_ok : forall A a nr vfold (a0 : A) cs,
    {< d F vs,
    PRE:hm
      rep cs d * [[ (F * arrayS a vs)%pred d ]] * [[ nr <= length vs ]]
    POST:hm' RET:^(cs, r)
      rep cs d * [[ r = fold_left vfold (firstn nr (map fst vs)) a0 ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} read_range a nr vfold a0 cs.
Proof.
(* skipped proof tokens: 88 *)
Admitted.
Lemma vsupd_range_xcrash_firstn' : forall l F a n vs cs' d',
    (F * arrayN ptsto_subset a (vsupd_range vs (firstn n l)))%pred d' ->
    length l <= length vs ->
    crash_xform (rep cs' d') =p=>
    crash_xform (exists cs d, rep cs d * 
      [[ (F * arrayN ptsto_subset a (vsupd_range vs l))%pred d ]]).
Proof.
(* skipped proof tokens: 266 *)
Admitted.
Lemma vsupd_range_xcrash_firstn : forall F a n l vs,
    length l <= length vs ->
    crash_xform (exists cs' d', rep cs' d' *
      [[ (F * arrayN ptsto_subset a (vsupd_range vs (firstn n l)))%pred d' ]]) =p=>
    crash_xform (exists cs d, rep cs d * 
      [[ (F * arrayN ptsto_subset a (vsupd_range vs l))%pred d ]]).
(* hint proof tokens: 47 *)
Proof.
    intros.
    xform_norm.
    erewrite vsupd_range_xcrash_firstn'; eauto.
    xform_norm.
    do 2 (xform_normr; cancel).
  Qed.
Theorem write_range_ok : forall a l cs,
    {< d F vs,
    PRE:hm
      rep cs d * [[ (F * arrayS a vs)%pred d ]] * [[ length l <= length vs ]]
    POST:hm' RET:cs
      exists d', rep cs d' *
      [[ (F * arrayS a (vsupd_range vs l))%pred d' ]]
    XCRASH:hm'
      exists cs' d', rep cs' d' *
      [[ (F * arrayS a (vsupd_range vs l))%pred d' ]]
    >} write_range a l cs.
Proof.
(* skipped proof tokens: 157 *)
Admitted.
Theorem sync_range_ok : forall a n cs,
    {< d d0 F vs,
    PRE:hm
      synrep cs d0 d *
      [[ (F * arrayS a vs)%pred d ]] *
      [[ n <= length vs /\ sync_invariant F ]]
    POST:hm' RET:cs
      exists d', synrep cs d0 d' *
      [[ (F * arrayS a (vssync_range vs n))%pred d' ]]
    CRASH:hm'
      exists cs', rep cs' d0
    >} sync_range a n cs.
(* hint proof tokens: 64 *)
Proof.
    unfold sync_range; intros.
    step.
    step.
    rewrite vssync_range_length; lia.

    step.
    apply arrayN_unify.
    apply vssync_range_progress; lia.

    step.

    Unshelve. all: try exact tt.
  Qed.
Local Hint Resolve vsupd_vecs_length_ok.
Local Hint Resolve vssync_vecs_length_ok.
Lemma vsupd_vecs_mem_exis : forall F a l vs d,
    (F * arrayN ptsto_subset a vs)%pred d ->
    Forall (fun e => fst e < length vs) l ->
    exists d', (F * arrayN ptsto_subset a (vsupd_vecs vs l))%pred d' /\ mem_incl d d'.
Proof.
(* skipped proof tokens: 361 *)
Admitted.
Lemma vsupd_vecs_xcrash_firstn' : forall F a l n vs cs' d',
    (F * arrayN ptsto_subset a (vsupd_vecs vs (firstn n l)))%pred d' ->
    Forall (fun e => fst e < length vs) l ->
    crash_xform (rep cs' d') =p=>
    crash_xform (exists cs d, rep cs d * 
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs l))%pred d ]]).
Proof.
(* skipped proof tokens: 305 *)
Admitted.
Lemma vsupd_vecs_xcrash_firstn : forall F a n l vs,
    Forall (fun e => fst e < length vs) l ->
    crash_xform (exists cs' d', rep cs' d' *
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs (firstn n l)))%pred d' ]]) =p=>
    crash_xform (exists cs d, rep cs d * 
      [[ (F * arrayN ptsto_subset a (vsupd_vecs vs l))%pred d ]]).
(* hint proof tokens: 48 *)
Proof.
    intros.
    xform_norm.
    erewrite vsupd_vecs_xcrash_firstn'; eauto.
    xform_norm.
    do 2 (xform_normr; cancel).
  Qed.
Theorem write_vecs_ok : forall a l cs,
    {< d F vs,
    PRE:hm
      rep cs d * [[ (F * arrayS a vs)%pred d ]] *
      [[ Forall (fun e => fst e < length vs) l ]]
    POST:hm' RET:cs
      exists d', rep cs d' *
      [[ (F * arrayS a (vsupd_vecs vs l))%pred d' ]]
    XCRASH:hm'
      exists cs' d', rep cs' d' *
      [[ (F * arrayS a (vsupd_vecs vs l))%pred d' ]]
    >} write_vecs a l cs.
(* hint proof tokens: 121 *)
Proof.
    unfold write_vecs.
    safestep. auto. auto.
    step.
    prestep; unfold rep; cancel.

    erewrite firstn_S_selN_expand by auto.
    setoid_rewrite vsupd_vecs_app; simpl.
    cancel.

    repeat xcrash_rewrite.
    setoid_rewrite vsupd_vecs_progress; auto.
    apply vsupd_vecs_xcrash_firstn; auto.

    step.
    rewrite firstn_oob; auto.
    xcrash.
    Unshelve. exact tt.
  Qed.
Theorem sync_vecs_ok : forall a l cs,
    {< d d0 F vs,
    PRE:hm
      synrep cs d0 d *
      [[ (F * arrayS a vs)%pred d ]] *
      [[ Forall (fun e => e < length vs) l /\ sync_invariant F ]]
    POST:hm' RET:cs
      exists d', synrep cs d0 d' *
      [[ (F * arrayS a (vssync_vecs vs l))%pred d' ]]
    CRASH:hm'
      exists cs', rep cs' d0
    >} sync_vecs a l cs.
(* hint proof tokens: 108 *)
Proof.
    unfold sync_vecs; intros.
    step.
    apply app_nil_l.
    cancel.
    step.
    rewrite vssync_vecs_length.
    eapply Forall_inv with (P := fun x => x < length vs).
    eauto using forall_app_l.
    step.
    apply cons_nil_app.
    rewrite vssync_vecs_app; cancel.
    step.
    rewrite app_nil_r. cancel.
    Unshelve. all: eauto; constructor.
  Qed.
Theorem sync_vecs_now_ok : forall a l cs,
    {< d F vs,
    PRE:hm
      rep cs d *
      [[ (F * arrayS a vs)%pred d ]] *
      [[ Forall (fun e => e < length vs) l /\ sync_invariant F ]]
    POST:hm' RET:cs
      exists d', rep cs d' *
      [[ (F * arrayS a (vssync_vecs vs l))%pred d' ]]
    CRASH:hm'
      exists cs', rep cs' d
    >} sync_vecs_now a l cs.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (read_range _ _ _ _ _) _) => apply read_range_ok : prog.
Hint Extern 1 ({{_}} Bind (write_range _ _ _) _) => apply write_range_ok : prog.
Hint Extern 1 ({{_}} Bind (sync_range _ _ _) _) => apply sync_range_ok : prog.
Hint Extern 1 ({{_}} Bind (write_vecs _ _ _) _) => apply write_vecs_ok : prog.
Hint Extern 1 ({{_}} Bind (sync_vecs _ _ _) _) => apply sync_vecs_ok : prog.
Hint Extern 1 ({{_}} Bind (sync_vecs_now _ _ _) _) => apply sync_vecs_now_ok : prog.
End BUFCACHE.
Global Opaque BUFCACHE.init_load.
Global Opaque BUFCACHE.init_recover.
Global Opaque BUFCACHE.read.
Global Opaque BUFCACHE.write.
Global Opaque BUFCACHE.sync.
Global Opaque BUFCACHE.begin_sync.
Global Opaque BUFCACHE.end_sync.
Global Opaque BUFCACHE.read_array.
Global Opaque BUFCACHE.write_array.
Global Opaque BUFCACHE.sync_array.
Global Opaque BUFCACHE.read_range.
Global Opaque BUFCACHE.write_range.
Global Opaque BUFCACHE.sync_range.
Global Opaque BUFCACHE.write_vecs.
Global Opaque BUFCACHE.sync_vecs.
