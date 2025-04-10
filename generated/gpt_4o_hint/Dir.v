Require Import Coq.Strings.String.
Require Import Mem.
Require Import Prog.
Require Import List.
Require Import Word.
Require Import Rec.
Require Import BFile.
Require Import BasicProg.
Require Import Log.
Require Import Hoare.
Require Import Pred PredCrash.
Require Import Lia.
Require Import Rec.
Require Import Array.
Require Import ListPred.
Require Import GenSepN.
Require Import BFile.
Require Import FileRecArray.
Require Import Bool.
Require Import SepAuto.
Require Import Log.
Require Import Cache.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import Errno.
Require Import DestructVarname.
Import ListNotations.
Import PeanoNat.
Require HexString.
Set Implicit Arguments.
Module DIR.
Definition filename_len := (HexString.to_nat "0x400"  - addrlen - addrlen).
Definition filename := word filename_len.
Module DentSig <: FileRASig.
Definition itemtype : Rec.type := Rec.RecF
        ([("name",  Rec.WordF filename_len);
          ("inum",  Rec.WordF addrlen);
          ("valid", Rec.WordF 1);
          ("isdir", Rec.WordF 1);
          ("unused", Rec.WordF (addrlen - 2))
         ]).
Definition items_per_val := valulen / (Rec.len itemtype).
Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
(* hint proof tokens: 33 *)
Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is. apply Nat.eqb_eq.
      compute; reflexivity.
    Qed.
End DentSig.
Module Dent := FileRecArray DentSig.
Definition dent := Dent.Defs.item.
Definition dent0 := Dent.Defs.item0.
Fact resolve_selN_dent0 : forall l i d,
    d = dent0 -> selN l i d = selN l i dent0.
(* hint proof tokens: 14 *)
Proof.
    intros; subst; auto.
  Qed.
Hint Rewrite resolve_selN_dent0 using reflexivity : defaults.
Definition bit2bool bit := if (bit_dec bit) then false else true.
Definition bool2bit bool : word 1 := if (bool_dec bool true) then $1 else $0.
Definition DEIsDir (de : dent) := Eval compute_rec in de :-> "isdir".
Definition DEValid (de : dent) := Eval compute_rec in de :-> "valid".
Definition DEName  (de : dent) := Eval compute_rec in de :-> "name".
Definition DEInum  (de : dent) := Eval compute_rec in # (de :-> "inum").
Definition mk_dent (name : filename) inum isdir : dent := Eval cbn in
      dent0 :=> "valid" := $1 :=>
                "name" := name :=>
                "inum" := $ inum :=>
                "isdir" := bool2bit isdir.
Definition is_dir   (de : dent) := bit2bool (DEIsDir de).
Definition is_valid (de : dent) := bit2bool (DEValid de).
Definition name_is  (n : filename) (de : dent) :=
      if (weq n (DEName de)) then true else false.
Definition dmatch (de: dent) : @pred filename (@weq filename_len) (addr * bool) :=
    if bool_dec (is_valid de) false then emp
    else (DEName de) |-> (DEInum de, is_dir de) * [[ DEInum de <> 0 ]].
Definition rep f dmap :=
    exists delist,
    (Dent.rep f delist)%pred (list2nmem (BFILE.BFData f)) /\
    listpred dmatch delist dmap.
Definition rep_macro Fm Fi m bxp ixp inum dmap ilist frees f ms sm : (@pred _ addr_eq_dec valuset) :=
    (exists flist,
    [[[ m ::: Fm * BFILE.rep bxp sm ixp flist ilist frees (BFILE.MSAllocC ms) (BFILE.MSCache ms) (BFILE.MSICache ms) (BFILE.MSDBlocks ms) ]]] *
    [[[ flist ::: Fi * inum |-> f ]]] *
    [[ rep f dmap ]])%pred.
Definition lookup_f name de (_ : addr) := (is_valid de) && (name_is name de).
Definition ifind_lookup_f lxp ixp dnum name ms :=
    Dent.ifind lxp ixp dnum (lookup_f name) ms.
Definition ifind_invalid lxp ixp dnum ms :=
    Dent.ifind lxp ixp dnum (fun de _ => negb (is_valid de)) ms.
Definition lookup lxp ixp dnum name ms :=
    let^ (ms, r) <- ifind_lookup_f lxp ixp dnum name ms;
    match r with
    | None => Ret ^(ms, None)
    | Some (_, de) => Ret ^(ms, Some (DEInum de, is_dir de))
    end.
Definition readent := (filename * (addr * bool))%type.
Definition readdir lxp ixp dnum ms :=
    let^ (ms, dents) <- Dent.readall lxp ixp dnum ms;
    let r := map (fun de => (DEName de, (DEInum de, is_dir de))) (filter is_valid dents) in
    Ret ^(ms, r).
Definition unlink lxp ixp dnum name ms :=
    let^ (ms, r) <- ifind_lookup_f lxp ixp dnum name ms;
    match r with
    | None => Ret ^(ms, 0, Err ENOENT)
    | Some (ix, _) =>
        ms <- Dent.put lxp ixp dnum ix dent0 ms;
        Ret ^(ms, ix, OK tt)
    end.
Definition link' lxp bxp ixp dnum name inum isdir ms :=
    let de := mk_dent name inum isdir in
    let^ (ms, r) <- ifind_invalid lxp ixp dnum ms;
    match r with
    | Some (ix, _) =>
        ms <- Dent.put lxp ixp dnum ix de ms;
        Ret ^(ms, ix+1, OK tt)
    | None =>
        let^ (ms, ok) <- Dent.extend lxp bxp ixp dnum de ms;
        Ret ^(ms, 0, ok)
    end.
Definition link'' lxp bxp ixp dnum name inum isdir (ix0:addr) ms :=
    let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;
    Ret ^(ms, ix, r0).
Definition link lxp bxp ixp dnum name inum isdir ix0 ms :=
    let de := mk_dent name inum isdir in
    let^ (ms, len) <- BFILE.getlen lxp ixp dnum ms;
    If (Compare_dec.lt_dec ix0 (len * Dent.RA.items_per_val)) {
      let^ (ms, res) <- Dent.get lxp ixp dnum ix0 ms;
      match (is_valid res) with
      | true =>
        let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;
        Ret ^(ms, ix, r0)
      | false => 
        ms <- Dent.put lxp ixp dnum ix0 de ms;
        Ret ^(ms, ix0+1, OK tt)
      end
    } else {

      let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;
      Ret ^(ms, ix, r0) 
    }.
Fact bit2bool_0 : bit2bool $0 = false.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Fact bit2bool_1 : bit2bool $1 = true.
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Fact bit2bool_1_ne : bit2bool $1 <> false.
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Fact bit2bool_0_ne : bit2bool $0 <> true.
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Local Hint Resolve bit2bool_0 bit2bool_1 bit2bool_0_ne bit2bool_1_ne.
Lemma bit2bool2bit : forall b, bit2bool (bool2bit b) = b.
(* hint proof tokens: 16 *)
Proof.
    destruct b; cbn; auto.
  Qed.
Lemma bool2bit2bool : forall b,  bool2bit (bit2bool b) = b.
(* hint proof tokens: 26 *)
Proof.
    unfold bit2bool; intros.
    destruct (bit_dec b); subst; auto.
  Qed.
Lemma lookup_f_ok: forall name de a,
    lookup_f name de a = true ->
    is_valid de = true /\ DEName de = name.
(* hint proof tokens: 57 *)
Proof.
    unfold lookup_f, name_is; intuition.
    apply andb_true_iff in H; tauto.
    destruct (weq name (DEName de)); auto.
    contradict H.
    rewrite andb_true_iff; easy.
  Qed.
Lemma lookup_f_nf: forall name de a,
    lookup_f name de a = false ->
    is_valid de = false \/ DEName de <> name.
(* hint proof tokens: 42 *)
Proof.
    unfold lookup_f, name_is; intuition.
    apply andb_false_iff in H; intuition.
    destruct (weq name (DEName de)); intuition.
  Qed.
Lemma lookup_notindomain': forall l ix name,
    Forall (fun e => (lookup_f name e ix) = false) l
    -> listpred dmatch l =p=> notindomain name.
(* hint proof tokens: 135 *)
Proof.
    induction l; unfold pimpl; simpl; intros.
    apply emp_notindomain; auto.
    inversion H; subst.

    destruct (Sumbool.sumbool_of_bool (is_valid a)).
    destruct (lookup_f_nf name a ix); try congruence.
    eapply notindomain_mem_except; eauto.
    eapply ptsto_mem_except.
    pred_apply; unfold dmatch at 1.
    rewrite e, IHl by eauto; simpl; cancel.

    pred_apply; rewrite IHl by eauto; cancel.
    unfold dmatch; rewrite e; simpl; auto.
  Qed.
Lemma lookup_notindomain: forall l name,
    (forall i, i < length l -> lookup_f name (selN l i dent0) i = false) ->
    listpred dmatch l =p=> notindomain name.
(* hint proof tokens: 36 *)
Proof.
    intros.
    eapply lookup_notindomain' with (ix := 0).
    eapply selN_Forall; eauto.
  Qed.
Definition dmatch_ex name (de: dent) : @pred filename (@weq filename_len) (addr * bool) :=
    if (name_is name de) then emp
    else dmatch de.
Definition dmatch_ex_same : forall de,
    dmatch_ex (DEName de) de = emp.
(* hint proof tokens: 37 *)
Proof.
    unfold dmatch_ex, name_is; intros.
    destruct (weq (DEName de) (DEName de)); congruence.
  Qed.
Definition dmatch_ex_diff : forall name de,
    name <> (DEName de) ->
    dmatch_ex name de = dmatch de.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Lemma dmatch_ex_ptsto : forall l name v,
    (name |-> v * listpred dmatch l) 
    =p=> (name |-> v * listpred (dmatch_ex name) l).
Proof.
(* skipped proof tokens: 188 *)
Admitted.
Lemma lookup_ptsto: forall l name ix,
    ix < length l ->
    lookup_f name (selN l ix dent0) ix = true ->
    listpred dmatch l =p=> listpred (dmatch_ex name) l *
       (name |-> (DEInum (selN l ix dent0), is_dir (selN l ix dent0))).
(* hint proof tokens: 240 *)
Proof.
    induction l; intros.
    simpl; inversion H.
    pose proof (lookup_f_ok _ _ _ H0) as [Hx Hy].
    destruct ix; subst; simpl in *.
    unfold dmatch at 1; rewrite Hx, dmatch_ex_same; simpl.
    eapply pimpl_trans with (b := (DEName a |-> _ * listpred dmatch l * _)%pred).
    cancel. rewrite dmatch_ex_ptsto; cancel.

    assert (ix < length l) by lia.
    rewrite IHl; eauto; try solve [ cancel ].
    unfold dmatch_ex at 2, dmatch, name_is.
    destruct (bool_dec (is_valid _) false);
    destruct (weq (DEName _) _); try solve [ cancel ].
    rewrite e; repeat destruct_prod.
    unfold pimpl; intros; exfalso.
    eapply ptsto_conflict_F with (m := m) (a := DEName (w, (w0, (w1, (w2, (w3, u)))))).
    pred_apply; cancel.
  Qed.
Definition readmatch (de: readent) : @pred _ (@weq filename_len) _ :=
    fst de |-> snd de.
Lemma readmatch_ok : forall l,
    listpred dmatch l =p=> listpred readmatch
      (map (fun de => (DEName de, (DEInum de, is_dir de))) (filter is_valid l)).
(* hint proof tokens: 41 *)
Proof.
    induction l; simpl; auto.
    unfold dmatch at 1; destruct (is_valid a); simpl.
    rewrite IHl; cancel.
    cancel.
  Qed.
Lemma dmatch_dent0_emp :  dmatch dent0 = emp.
(* hint proof tokens: 37 *)
Proof.
    unfold dmatch, dent0.
    destruct (bool_dec (is_valid _) false); auto.
    contradict n.
    compute; auto.
  Qed.
Lemma listpred_dmatch_dent0_emp : forall l i dmap,
    listpred dmatch l dmap ->
    is_valid (selN l i dent0) = true ->
    i < length l ->
    listpred dmatch (updN l i dent0) (mem_except dmap (DEName (selN l i dent0))).
Proof.
(* skipped proof tokens: 68 *)
Admitted.
Lemma dmatch_mk_dent : forall name inum isdir,
    goodSize addrlen inum ->
    dmatch (mk_dent name inum isdir) = (name |-> (inum, isdir) * [[ inum <> 0 ]])%pred.
(* hint proof tokens: 53 *)
Proof.
    unfold dmatch, mk_dent, is_valid, is_dir; intros; cbn.
    rewrite bit2bool_1, wordToNat_natToWord_idempotent', bit2bool2bit; auto.
  Qed.
Lemma listpred_dmatch_mem_upd : forall l i dmap name inum isdir,
    notindomain name dmap ->
    negb (is_valid (selN l i dent0)) = true ->
    listpred dmatch l dmap ->
    i < length l -> inum <> 0 ->
    goodSize addrlen inum ->
    listpred dmatch (updN l i (mk_dent name inum isdir)) (Mem.upd dmap name (inum, isdir)).
Proof.
(* skipped proof tokens: 105 *)
Admitted.
Lemma listpred_dmatch_repeat_dent0 : forall n,
    listpred dmatch (repeat dent0 n) <=p=> emp.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma listpred_dmatch_ext_mem_upd : forall l dmap name inum isdir,
    notindomain name dmap ->
    (forall i, i < length l -> negb (is_valid (selN l i dent0)) = false) ->
    listpred dmatch l dmap ->
    goodSize addrlen inum -> inum <> 0 ->
    listpred dmatch (l ++ @updN (Rec.data Dent.RA.itemtype) (Dent.Defs.block0) 0 (mk_dent name inum isdir))
                    (Mem.upd dmap name (inum, isdir)).
Proof.
(* original proof tokens: 143 *)
intros; unfold updN; simpl; apply listpred_app.
apply listpred_app.
(* No more tactics to try *)
Admitted.

Lemma listpred_dmatch_eq_mem : forall l m m',
    listpred dmatch l m -> listpred dmatch l m' ->
    m = m'.
(* hint proof tokens: 188 *)
Proof.
    induction l; cbn; intros m m' H H'.
    - apply emp_empty_mem_only in H.
      apply emp_empty_mem_only in H'.
      congruence.
    - unfold dmatch at 1 in H.
      unfold dmatch at 1 in H'.
      destruct bool_dec.
      apply IHl; pred_apply; cancel.
      eapply pimpl_trans in H; [| cancel..].
      eapply pimpl_trans in H'; [| cancel..].
      revert H. revert H'.
      unfold_sep_star.
      intros. repeat deex.
      match goal with H1 : (ptsto _ _ ?m), H2 : (ptsto _ _ ?m') |- _ =>
        assert (m = m') by (eapply ptsto_complete; eauto); subst
      end.
      f_equal.
      eauto.
  Qed.
Lemma listpred_dmatch_notindomain: forall delist dmap name x,
    notindomain name dmap ->
    listpred dmatch delist (upd dmap name x) ->
    listpred dmatch delist =p=> notindomain name * name |-> x.
(* hint proof tokens: 50 *)
Proof.
    intros. intros m ?.
    replace m with (upd dmap name x) in * by (eauto using listpred_dmatch_eq_mem).
    apply ptsto_upd_disjoint; auto.
  Qed.
Lemma dmatch_no_0_inum: forall f m, dmatch f m ->
    forall name isdir, m name = Some (0, isdir) -> False.
Proof.
(* skipped proof tokens: 104 *)
Admitted.
Lemma listpred_dmatch_no_0_inum: forall dmap m,
    listpred dmatch dmap m ->
    forall name isdir, m name = Some (0, isdir) -> False.
(* hint proof tokens: 105 *)
Proof.
    induction dmap; cbn; intros.
    congruence.
    revert H.
    unfold_sep_star.
    intros. repeat deex.
    unfold mem_union in *.
    destruct (m1 name) eqn:?.
    denote (Some _ = Some _) as Hs; inversion Hs; subst; clear Hs.
    eauto using dmatch_no_0_inum.
    eauto.
  Unshelve.
    all: eauto.
  Qed.
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSCache := BFILE.MSCache.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSDBlocks := BFILE.MSDBlocks.
Theorem lookup_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 sm m dmap ilist frees f,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms' sm *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]] *
         ( [[ r = None /\ notindomain name dmap ]] \/
           exists inum isdir Fd,
           [[ r = Some (inum, isdir) /\ inum <> 0 /\
                   (Fd * name |-> (inum, isdir))%pred dmap ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} lookup lxp ixp dnum name ms.
Proof.
(* skipped proof tokens: 140 *)
Admitted.
Theorem readdir_ok : forall lxp bxp ixp dnum ms,
    {< F Fm Fi m0 sm m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms',r)
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms' sm *
             [[ listpred readmatch r dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSCache ms' = MSCache ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
             [[ MSDBlocks ms' = MSDBlocks ms ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} readdir lxp ixp dnum ms.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Local Hint Resolve mem_except_notindomain.
Theorem unlink_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', hint, r) exists m' dmap',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             exists f', rep_macro Fm Fi m' bxp ixp dnum dmap' ilist frees f' ms' sm *
             [[ dmap' = mem_except dmap name ]] *
             [[ notindomain name dmap' ]] *
             [[ r = OK tt -> indomain name dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} unlink lxp ixp dnum name ms.
Proof.
(* skipped proof tokens: 169 *)
Admitted.
Theorem link'_ok : forall lxp bxp ixp dnum name inum isdir ms,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm *
             [[ notindomain name dmap ]] *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:hm' RET:^(ms', ixhint', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm')
        \/  ([[ r = OK tt ]] *
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' f' ms' sm *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} link' lxp bxp ixp dnum name inum isdir ms.
Proof.
(* original proof tokens: 186 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{ _ }} Bind (link' _ _ _ _ _ _ _ _) _) => apply link'_ok : prog.
Theorem link_ok : forall lxp bxp ixp dnum name inum isdir ixhint ms,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm *
             [[ notindomain name dmap ]] *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:hm' RET:^(ms', ixhint', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm')
        \/  ([[ r = OK tt ]] * 
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' f' ms' sm *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} link lxp bxp ixp dnum name inum isdir ixhint ms.
Proof.
(* skipped proof tokens: 404 *)
Admitted.
Hint Extern 1 ({{_}} Bind (lookup _ _ _ _ _) _) => apply lookup_ok : prog.
Hint Extern 1 ({{_}} Bind (unlink _ _ _ _ _) _) => apply unlink_ok : prog.
Hint Extern 1 ({{_}} Bind (link _ _ _ _ _ _ _ _ _) _) => apply link_ok : prog.
Hint Extern 1 ({{_}} Bind (readdir _ _ _ _) _) => apply readdir_ok : prog.
Hint Extern 0 (okToUnify (rep ?f _) (rep ?f _)) => constructor : okToUnify.
Theorem dmatch_complete : forall de m1 m2, dmatch de m1 -> dmatch de m2 -> m1 = m2.
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Lemma listpred_dmatch_eq : forall l m1 m2,
    listpred dmatch l m1
    -> listpred dmatch l m2
    -> m1 = m2.
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma rep_mem_eq : forall f m1 m2,
    rep f m1 ->
    rep f m2 ->
    m1 = m2.
(* hint proof tokens: 45 *)
Proof.
    unfold rep; intros.
    repeat deex.
    pose proof (Dent.rep_items_eq H0 H1); subst.
    eapply listpred_dmatch_eq; eauto.
  Qed.
Theorem bfile0_empty : rep BFILE.bfile0 empty_mem.
(* hint proof tokens: 73 *)
Proof.
    unfold rep, Dent.rep, Dent.items_valid.
    exists nil; firstorder.
    exists nil; simpl.
    setoid_rewrite Dent.Defs.ipack_nil.
    assert (emp (list2nmem (@nil valuset))) by firstorder.
    pred_apply; cancel.
    apply Forall_nil.
  Qed.
Theorem rep_no_0_inum: forall f m, rep f m ->
    forall name isdir, m name = Some (0, isdir) -> False.
(* hint proof tokens: 31 *)
Proof.
    unfold rep. intros. repeat deex.
    eauto using listpred_dmatch_no_0_inum.
  Qed.
Theorem crash_eq : forall f f' m1 m2,
    BFILE.file_crash f f' ->
    rep f m1 ->
    rep f' m2 ->
    m1 = m2.
Proof.
(* skipped proof tokens: 73 *)
Admitted.
Theorem crash_rep : forall f f' m,
    BFILE.file_crash f f' ->
    rep f m ->
    rep f' m.
Proof.
(* skipped proof tokens: 38 *)
Admitted.
End DIR.
