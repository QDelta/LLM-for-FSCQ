Require Import Eqdep_dec Arith Lia List ListUtils Rounding Psatz.
Require Import Word WordAuto AsyncDisk Pred PredCrash GenSepN Array SepAuto.
Require Import Rec Prog BasicProg Hoare RecArrayUtils Log.
Require Import FMapAVL FMapMem.
Require Import MapUtils.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Import ListNotations.
Set Implicit Arguments.
Module LogRecArray (RA : RASig).
Module Defs := RADefs RA.
Import RA Defs.
Definition items_valid xp (items : itemlist) :=
    xparams_ok xp /\ RAStart xp <> 0 /\
    length items = (RALen xp) * items_per_val /\
    Forall Rec.well_formed items.
Definition rep xp (items : itemlist) :=
    ( exists vl, [[ vl = ipack items ]] *
      [[ items_valid xp items ]] *
      arrayN (@ptsto _ addr_eq_dec valuset) (RAStart xp) (synced_list vl))%pred.
Definition get lxp xp ix ms :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- LOG.read_array lxp (RAStart xp) bn ms;
    Ret ^(ms, selN_val2block v off).
Definition put lxp xp ix item ms :=
    let '(bn, off) := (ix / items_per_val, ix mod items_per_val) in
    let^ (ms, v) <- LOG.read_array lxp (RAStart xp) bn ms;
    let v' := block2val_updN_val2block v off item in
    ms <- LOG.write_array lxp (RAStart xp) bn v' ms;
    Ret ms.
Definition read lxp xp nblocks ms :=
    let^ (ms, r) <- LOG.read_range lxp (RAStart xp) nblocks iunpack nil ms;
    Ret ^(ms, r).
Definition write lxp xp items ms :=
    ms <- LOG.write_range lxp (RAStart xp) (ipack items) ms;
    Ret ms.
Definition init lxp xp ms :=
    ms <- LOG.write_range lxp (RAStart xp) (repeat $0 (RALen xp)) ms;
    Ret ms.
Definition ifind lxp xp (cond : item -> addr -> bool) ms :=
    let^ (ms, ret) <- ForN i < (RALen xp)
    Hashmap hm
    Ghost [ F m xp items Fm crash sm m1 m2 ]
    Loopvar [ ms ret ]
    Invariant
    LOG.rep lxp F (LOG.ActiveTxn m1 m2) ms sm hm *
                              [[[ m ::: Fm * rep xp items ]]] *
                              [[ forall st,
                                   ret = Some st ->
                                   cond (snd st) (fst st) = true
                                   /\ (fst st) < length items
                                   /\ snd st = selN items (fst st) item0 ]]
    OnCrash  crash
    Begin
      If (is_some ret) {
        Ret ^(ms, ret)
      } else {
        let^ (ms, v) <- LOG.read_array lxp (RAStart xp) i ms;
        let r := ifind_block cond (val2block v) (i * items_per_val) in
        match r with
        
        | None => Ret ^(ms, None)
        
        | Some ifs => Ret ^(ms, Some ifs)
        end
      }
    Rof ^(ms, None);
    Ret ^(ms, ret).
Local Hint Resolve items_per_val_not_0 items_per_val_gt_0 items_per_val_gt_0'.
Lemma items_valid_updN : forall xp items a v,
    items_valid xp items ->
    Rec.well_formed v ->
    items_valid xp (updN items a v).
(* hint proof tokens: 36 *)
Proof.
    unfold items_valid; intuition.
    rewrite length_updN; auto.
    apply Forall_wellformed_updN; auto.
  Qed.
Lemma items_valid_upd_range : forall xp items len a v,
    items_valid xp items ->
    Rec.well_formed v ->
    items_valid xp (upd_range items a len v).
(* hint proof tokens: 23 *)
Proof.
    induction len; simpl; intros; auto using items_valid_updN.
  Qed.
Lemma ifind_length_ok : forall xp i items,
    i < RALen xp ->
    items_valid xp items ->
    i < length (synced_list (ipack items)).
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma items_valid_length_eq : forall xp a b,
    items_valid xp a ->
    items_valid xp b ->
    length (ipack a) = length (ipack b).
(* hint proof tokens: 25 *)
Proof.
    unfold items_valid; intuition.
    eapply ipack_length_eq; eauto.
  Qed.
Theorem get_ok : forall lxp xp ix ms,
    {< F Fm m0 sm m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ ix < length items ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm' *
          [[ r = selN items ix item0 ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} get lxp xp ix ms.
(* hint proof tokens: 103 *)
Proof.
    unfold get, rep.
    safestep.
    rewrite synced_list_length, ipack_length.
    apply div_lt_divup; auto.

    safestep.
    subst; rewrite synced_list_selN; simpl.
    erewrite selN_val2block_equiv.
    apply ipack_selN_divmod; auto.
    apply list_chunk_wellformed; auto.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.
  Qed.
Theorem put_ok : forall lxp xp ix e ms,
    {< F Fm m0 sm m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ ix < length items /\ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm hm' *
          [[[ m' ::: Fm * rep xp (updN items ix e) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} put lxp xp ix e ms.
Proof.
(* original proof tokens: 155 *)

(* No more tactics to try *)
Admitted.

Theorem read_ok : forall lxp xp nblocks ms,
    {< F Fm m0 sm m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ nblocks <= RALen xp ]] *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm' *
          [[ r = firstn (nblocks * items_per_val) items ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} read lxp xp nblocks ms.
(* hint proof tokens: 83 *)
Proof.
    unfold read, rep.
    hoare.

    rewrite synced_list_length, ipack_length.
    unfold items_valid in *; intuition.
    substl (length items); rewrite divup_mul; auto.

    subst; rewrite synced_list_map_fst.
    unfold items_valid in *; intuition.
    eapply iunpack_ipack_firstn; eauto.
  Qed.
Theorem write_ok : forall lxp xp items ms,
    {< F Fm m0 sm m old,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ items_valid xp items ]] *
          [[[ m ::: Fm * rep xp old ]]]
    POST:hm' RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm hm' *
          [[[ m' ::: Fm * rep xp items ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} write lxp xp items ms.
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Theorem init_ok : forall lxp xp ms,
    {< F Fm m0 sm m vsl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ xparams_ok xp /\ RAStart xp <> 0 /\ length vsl = RALen xp ]] *
          [[[ m ::: Fm * arrayN (@ptsto _ addr_eq_dec _) (RAStart xp) vsl ]]]
    POST:hm' RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm hm' *
          [[[ m' ::: Fm * rep xp (repeat item0 ((RALen xp) * items_per_val) ) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.
Proof.
(* original proof tokens: 87 *)

(* No more tactics to try *)
Admitted.

Hint Extern 0 (okToUnify (LOG.arrayP (RAStart _) _) (LOG.arrayP (RAStart _) _)) =>
  constructor : okToUnify.
Hint Resolve
       ifind_list_ok_cond
       ifind_result_inbound
       ifind_result_item_ok.
Theorem ifind_ok : forall lxp xp cond ms,
    {< F Fm m0 sm m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm' *
        ( [[ r = None ]] \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true
                         /\ (fst st) < length items
                         /\ snd st = selN items (fst st) item0 ]])
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} ifind lxp xp cond ms.
Proof.
(* original proof tokens: 186 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (get _ _ _ _) _) => apply get_ok : prog.
Hint Extern 1 ({{_}} Bind (put _ _ _ _ _) _) => apply put_ok : prog.
Hint Extern 1 ({{_}} Bind (read _ _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (write _ _ _ _) _) => apply write_ok : prog.
Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (ifind _ _ _ _) _) => apply ifind_ok : prog.
Definition get_array lxp xp ix ms :=
    r <- get lxp xp ix ms;
    Ret r.
Definition put_array lxp xp ix item ms :=
    r <- put lxp xp ix item ms;
    Ret r.
Definition read_array lxp xp nblocks ms :=
    r <- read lxp xp nblocks ms;
    Ret r.
Definition ifind_array lxp xp cond ms :=
    r <- ifind lxp xp cond ms;
    Ret r.
Theorem get_array_ok : forall lxp xp ix ms,
    {< F Fm Fi m0 sm m items e,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * (ix |-> e) ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm' * [[ r = e ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} get_array lxp xp ix ms.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Theorem put_array_ok : forall lxp xp ix e ms,
    {< F Fm Fi m0 sm m items e0,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * (ix |-> e0) ]]]
    POST:hm' RET:ms' exists m' items',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm hm' *
          [[ items' = updN items ix e ]] *
          [[[ m' ::: Fm * rep xp items' ]]] *
          [[[ items' ::: Fi * (ix |-> e) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} put_array lxp xp ix e ms.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma read_array_length_ok : forall l xp Fm Fi m items nblocks,
    length l = nblocks * items_per_val ->
    (Fm * rep xp items)%pred (list2nmem m) ->
    (Fi * arrayN (@ptsto _ addr_eq_dec _) 0 l)%pred (list2nmem items) ->
    nblocks <= RALen xp.
(* hint proof tokens: 77 *)
Proof.
    unfold rep; intuition.
    destruct_lift H0.
    unfold items_valid in *; subst; intuition.
    apply list2nmem_arrayN_length in H1.
    rewrite H, H3 in H1.
    eapply Nat.mul_le_mono_pos_r.
    apply items_per_val_gt_0.
    auto.
  Qed.
Lemma read_array_list_ok : forall (l : list item) nblocks items Fi,
    length l = nblocks * items_per_val ->
    (Fi ✶ arrayN (@ptsto _ addr_eq_dec _) 0 l)%pred (list2nmem items) ->
    firstn (nblocks * items_per_val) items = l.
Proof.
(* original proof tokens: 39 *)
intros.
rewrite <- H.
eapply list2nmem_arrayN_length in H0.
rewrite H, Nat.mul_comm in H0.
eauto using Nat.mul_le_mono_pos_l.
(* No more tactics to try *)
Admitted.

Theorem read_array_ok : forall lxp xp nblocks ms,
    {< F Fm Fi m0 sm m items l,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ length l = (nblocks * items_per_val)%nat ]] *
          [[[ m ::: Fm * rep xp items ]]] *
          [[[ items ::: Fi * arrayN (@ptsto _ addr_eq_dec _) 0 l ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm' *
          [[ r = l ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} read_array lxp xp nblocks ms.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem ifind_array_ok : forall lxp xp cond ms,
    {< F Fm m0 sm m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: Fm * rep xp items ]]]
    POST:hm' RET:^(ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm' *
        ( [[ r = None ]] \/ exists st,
          [[ r = Some st /\ cond (snd st) (fst st) = true ]] *
          [[[ items ::: arrayN_ex (@ptsto _ addr_eq_dec _) items (fst st) * (fst st) |-> (snd st) ]]] )
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} ifind_array lxp xp cond ms.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Fact eq_rect_eq : forall (a : nat) (f : nat -> Type) v1 v2 c H,
    eq_rect a f v1 c H = eq_rect a f v2 c H -> v1 = v2.
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 17 *)

unfold eq_rect; intros.
subst.
auto.
Qed.

Ltac eq_rect_eq := match goal with [H : eq_rect _ _ _ _ _ = eq_rect _ _ _ _ _ |- _] =>
      apply eq_rect_eq in H;
      eapply f_equal in H;
      rewrite Rec.of_to_id in H;
      rewrite Rec.of_to_id in H
    end.
Lemma ipack_inj : forall ra l1 l2,
    items_valid ra l1 ->
    items_valid ra l2 ->
    ipack l1 =ipack l2 -> l1 = l2.
Proof.
(* original proof tokens: 417 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (get_array _ _ _ _) _) => apply get_array_ok : prog.
Hint Extern 1 ({{_}} Bind (put_array _ _ _ _ _) _) => apply put_array_ok : prog.
Hint Extern 1 ({{_}} Bind (read_array _ _ _ _) _) => apply read_array_ok : prog.
Hint Extern 1 ({{_}} Bind (ifind_array _ _ _ _) _) => apply ifind_array_ok : prog.
Hint Extern 0 (okToUnify (rep ?xp _) (rep ?xp _)) => constructor : okToUnify.
Theorem rep_inj : forall F1 F2 l1 l2 ra m,
    (F1 * rep ra l1)%pred m -> (F2 * rep ra l2)%pred m -> l1 = l2.
(* hint proof tokens: 138 *)
Proof.
    intros.
    unfold rep in *.
    repeat match goal with
      [ H : (_ * (exis _))%pred _ |- _ ] => destruct_lift H
      end.
    match goal with
      [ H : context[synced_list _] |- _] =>  eapply arrayN_unify', synced_list_inj in H
    end.
    eapply ipack_inj; eauto.
    repeat rewrite synced_list_length.
    repeat rewrite ipack_length.
    f_equal.
    unfold items_valid in *; intuition.
    unfold item in *.
    lia.
    eassumption.
  Qed.
Lemma items_wellformed : forall F xp l m,
    (F * rep xp l)%pred m -> Forall Rec.well_formed l.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma items_wellformed_pimpl : forall xp l,
    rep xp l =p=> [[ Forall Rec.well_formed l ]] * rep xp l.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma item_wellformed : forall F xp m l i,
    (F * rep xp l)%pred m -> Rec.well_formed (selN l i item0).
(* hint proof tokens: 57 *)
Proof.
    intros.
    destruct (lt_dec i (length l)).
    apply Forall_selN; auto.
    eapply items_wellformed; eauto.
    rewrite selN_oob by lia.
    apply item0_wellformed.
  Qed.
Lemma items_length_ok : forall F xp l m,
    (F * rep xp l)%pred m ->
    length l = (RALen xp) * items_per_val.
(* hint proof tokens: 24 *)
Proof.
    unfold rep, items_valid; intuition.
    destruct_lift H; auto.
  Qed.
Lemma items_length_ok_pimpl : forall xp l,
    rep xp l =p=> [[ length l = ((RALen xp) * items_per_val)%nat ]] * rep xp l.
(* hint proof tokens: 16 *)
Proof.
    unfold rep, items_valid; cancel.
  Qed.
Theorem xform_rep : forall xp l,
    crash_xform (rep xp l) <=p=> rep xp l.
(* hint proof tokens: 66 *)
Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite crash_xform_arrayN_synced; cancel.
    cancel.
    xform_normr; cancel.
    rewrite <- crash_xform_arrayN_r; eauto.
    apply possible_crash_list_synced_list.
  Qed.
End LogRecArray.
Module LogRecArrayCache (RA : RASig).
Module LRA := LogRecArray RA.
Module Defs := LRA.Defs.
Import RA LRA.Defs.
Module Cache := FMapAVL.Make(Nat_as_OT).
Module CacheDefs := MapDefs Nat_as_OT Cache.
Definition Cache_type := Cache.t item.
Module M := MapMem Nat_as_OT Cache.
Definition cache0 : Cache_type := Cache.empty item.
Definition cache_ptsto i (v : item) : @pred _ addr_eq_dec _ :=
    ( i |-> v \/ emp )%pred.
Definition cache_rep (items : itemlist) (c : Cache_type) :=
     arrayN cache_ptsto 0 items (M.mm _ c).
Definition rep xp (items : itemlist) c :=
    ( LRA.rep xp items * [[ cache_rep items c ]] )%pred.
Definition get lxp xp ix cache ms :=
    match Cache.find ix cache with
    | Some v =>
      Ret ^(cache, ms, v)
    | None =>
      let^ (ms, v) <- LRA.get lxp xp ix ms;
      AlertModified;;
      Ret ^(Cache.add ix v cache, ms, v)
    end.
Definition put lxp xp ix item cache ms :=
    ms <- LRA.put lxp xp ix item ms;
    Ret ^(Cache.add ix item cache, ms).
Definition read := LRA.read.
Definition write := LRA.write.
Definition init := LRA.init.
Definition ifind := LRA.ifind.
Definition get_array lxp xp ix cache ms :=
    r <- get lxp xp ix cache ms;
    Ret r.
Definition put_array lxp xp ix item cache ms :=
    r <- put lxp xp ix item cache ms;
    Ret r.
Definition read_array lxp xp nblocks ms :=
    r <- read lxp xp nblocks ms;
    Ret r.
Definition ifind_array lxp xp cond ms :=
    r <- ifind lxp xp cond ms;
    Ret r.
Definition read_ok := LRA.read_ok.
Definition write_ok := LRA.write_ok.
Definition init_ok := LRA.init_ok.
Definition ifind_ok := LRA.ifind_ok.
Hint Extern 1 ({{_}} Bind (read _ _ _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (write _ _ _ _) _) => apply write_ok : prog.
Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
Lemma item_wellformed : forall F xp m i l cache,
    (F ✶ rep xp l cache)%pred m ->
    Rec.well_formed (selN l i item0).
(* hint proof tokens: 30 *)
Proof.
    unfold rep.
    intros.
    destruct_lifts.
    eauto using LRA.item_wellformed.
  Qed.
Lemma items_length_ok_pimpl : forall xp l cache,
    rep xp l cache =p=>
    [[ length l = (RALen xp * items_per_val)%nat ]] ✶ rep xp l cache.
(* hint proof tokens: 38 *)
Proof.
    unfold rep.
    intros xp l c m H.
    rewrite LRA.items_length_ok_pimpl in H.
    pred_apply.
    cancel.
  Qed.
Lemma xform_rep : forall xp l c,
    crash_xform (rep xp l c) <=p=> rep xp l c.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma cache_rep_empty : forall l,
    cache_rep l (Cache.empty _).
Proof.
(* original proof tokens: 82 *)
unfold cache_rep.
induction l; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma rep_clear_cache: forall xp items cache,
    rep xp items cache =p=> rep xp items cache0.
(* hint proof tokens: 19 *)
Proof.
    unfold rep. cancel.
    apply cache_rep_empty.
  Qed.
Lemma arrayN_cache_ptsto_oob: forall l i m x,
    arrayN (cache_ptsto) x l m -> i >= length l + x \/ i < x -> m i = None.
(* hint proof tokens: 88 *)
Proof.
    induction l; cbn; intros; auto.
    unfold sep_star in H.
    rewrite sep_star_is in H.
    unfold sep_star_impl in H.
    repeat deex.
    all: eapply mem_union_sel_none.
    all : solve [
      cbv in H2; intuition auto; apply H3; lia |
      eapply IHl; eauto; lia].
  Qed.
Lemma cache_rep_some : forall items i cache v d,
    Cache.find i cache = Some v ->
    i < length items ->
    cache_rep items cache ->
    v = selN items i d.
Proof.
(* original proof tokens: 241 *)

(* No more tactics to try *)
Admitted.

Lemma cache_rep_add : forall items i cache d,
    i < length items ->
    cache_rep items cache ->
    cache_rep items (Cache.add i (selN items i d) cache).
(* hint proof tokens: 249 *)
Proof.
    unfold cache_rep in *.
    intros.
    rewrite M.mm_add_upd.
    destruct (M.mm _ cache i) eqn:?.
    eapply cache_rep_some in H0 as ?; eauto.
    rewrite Mem.upd_nop; eauto.
    rewrite Heqo. f_equal. eauto.
    generalize dependent (M.mm _ cache). clear cache.
    intros.
    eapply arrayN_mem_upd_none; eauto.
    edestruct arrayN_except as [H' _]; eauto; apply H' in H0; clear H'.
    unfold sep_star in *.
    rewrite sep_star_is in *.
    unfold sep_star_impl in *.
    repeat deex.
    apply mem_union_none_sel in Heqo.
    cbv [cache_ptsto or ptsto] in *.
    intuition try congruence.
    apply emp_empty_mem_only in H5. subst.
    rewrite mem_union_empty_mem'. auto.
    cbv [cache_ptsto ptsto or].
    left.
    intuition (destruct addr_eq_dec); eauto; congruence.
  Unshelve.
    exact item0.
  Qed.
Lemma cache_ptsto_upd : forall i v0 v m,
    cache_ptsto i v0 m -> cache_ptsto i v (Mem.upd m i v).
Proof.
(* original proof tokens: 107 *)

(* No more tactics to try *)
Admitted.

Lemma cache_rep_updN : forall items cache i v,
    i < length items ->
    cache_rep items cache ->
    cache_rep (updN items i v) (Cache.add i v cache).
(* hint proof tokens: 484 *)
Proof.
    unfold cache_rep in *.
    intros.
    rewrite M.mm_add_upd.
    generalize dependent (M.mm _ cache). clear cache.
    intros.
    edestruct arrayN_isolate as [H' _]; eauto; apply H' in H0; clear H'.
    edestruct arrayN_isolate as [_ H']; [| apply H'; clear H'].
    rewrite length_updN; eauto.
    simpl in *.
    rewrite selN_updN_eq by auto.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    revert H0.
    unfold_sep_star.
    intuition repeat deex.
    assert (mem_disjoint m0 (Mem.upd m3 i v)).
    cbv [cache_ptsto or ptsto] in H6.
    cbv [mem_disjoint Mem.upd] in *.
    intuition repeat deex.
    destruct addr_eq_dec; subst; eauto 10.
    destruct addr_eq_dec; subst; eauto 10.
    erewrite arrayN_cache_ptsto_oob in H6; eauto; try congruence.
    rewrite firstn_length_l; lia.
    apply mem_disjoint_union in H0 as ?.
    assert (mem_disjoint (Mem.upd m3 i v) m2).
    cbv [cache_ptsto or ptsto] in H6.
    cbv [mem_disjoint Mem.upd] in *.
    intuition repeat deex.
    destruct addr_eq_dec; subst; eauto 10.
    destruct addr_eq_dec; subst; eauto 10.
    erewrite arrayN_cache_ptsto_oob in H9; eauto; try congruence; lia.
    repeat eexists; try eapply cache_ptsto_upd; eauto.
    rewrite mem_union_comm with (m1 := m0) by auto.
    repeat rewrite <- mem_union_upd.
    f_equal.
    apply mem_union_comm, mem_disjoint_comm; auto.
    apply mem_disjoint_mem_union_split_l; auto.
    apply mem_disjoint_comm.
    eapply mem_disjoint_union_2.
    apply mem_disjoint_comm.
    eauto.
  Unshelve. all : eauto.
  Qed.
Theorem get_array_ok : forall lxp xp ix cache ms,
    {< F Fm m0 sm m items,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ ix < length items ]] *
          [[[ m ::: Fm * rep xp items cache ]]]
    POST:hm' RET:^(cache', ms', r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm' *
          [[[ m ::: Fm * rep xp items cache' ]]] *
          [[ r = selN items ix item0 ]]
    CRASH:hm' exists ms',
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} get_array lxp xp ix cache ms.
(* hint proof tokens: 34 *)
Proof.
    unfold get_array, get, rep.
    hoare.
    all : eauto using cache_rep_some, cache_rep_add.
  Qed.
Theorem put_array_ok : forall lxp xp ix e cache ms,
    {< F Fm Fi m0 sm m items e0,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ Rec.well_formed e ]] *
          [[[ m ::: Fm * rep xp items cache ]]] *
          [[[ items ::: Fi * (ix |-> e0) ]]]
    POST:hm' RET:^(cache', ms') exists m' items',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' sm hm' *
          [[ items' = updN items ix e ]] *
          [[[ m' ::: Fm * rep xp items' cache' ]]] *
          [[[ items' ::: Fi * (ix |-> e) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} put_array lxp xp ix e cache ms.
(* hint proof tokens: 74 *)
Proof.
    unfold put_array, put, rep.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    eapply cache_rep_updN; eauto.
    eapply list2nmem_ptsto_bound; eauto.
    eapply list2nmem_updN; eauto.
  Qed.
Hint Extern 1 ({{_}} Bind (get_array _ _ _ _ _) _) => apply get_array_ok : prog.
Hint Extern 1 ({{_}} Bind (put_array _ _ _ _ _ _) _) => apply put_array_ok : prog.
Hint Extern 0 (okToUnify (rep ?xp _ _) (rep ?xp _ _)) => constructor : okToUnify.
End LogRecArrayCache.
