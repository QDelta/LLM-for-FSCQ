Require Import Coq.Strings.String.
Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Hashmap.
Require Import HashmapProg.
Require Import Pred PredCrash.
Require Import Prog ProgMonad.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Lia.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import WordAuto.
Require Import Cache.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import AsyncDisk.
Require Import RecArrayUtils.
Require Import AsyncRecArray.
Import ListNotations.
Set Implicit Arguments.
Module PaddedLog.
Module DescSig <: RASig.
Definition xparams := log_xparams.
Definition RAStart := LogDescriptor.
Definition RALen := LogDescLen.
Definition xparams_ok (xp : xparams) := goodSize addrlen ((RAStart xp) + (RALen xp)).
Definition itemtype := Rec.WordF addrlen.
Definition items_per_val := valulen / addrlen.
Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

End DescSig.
Module DataSig <: RASig.
Definition xparams := log_xparams.
Definition RAStart := LogData.
Definition RALen := LogLen.
Definition xparams_ok (xp : xparams) := goodSize addrlen ((RAStart xp) + (RALen xp)).
Definition itemtype := Rec.WordF valulen.
Definition items_per_val := 1.
Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
(* hint proof tokens: 32 *)
Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is. apply Nat.eqb_eq. compute; reflexivity.
    Qed.
End DataSig.
Module Desc := AsyncRecArray DescSig.
Module Data := AsyncRecArray DataSig.
Module DescDefs := Desc.Defs.
Module DataDefs := Data.Defs.
Module Hdr.
Definition header_type := Rec.RecF ([("previous_ndesc", Rec.WordF addrlen);
                                         ("previous_ndata", Rec.WordF addrlen);
                                         ("ndesc", Rec.WordF addrlen);
                                         ("ndata", Rec.WordF addrlen);
                                         ("addr_checksum", Rec.WordF hashlen);
                                         ("valu_checksum", Rec.WordF hashlen)]).
Definition header := Rec.data header_type.
Definition hdr := ((nat * nat) * (nat * nat) * (word hashlen * word hashlen))%type.
Definition previous_length (header : hdr) := fst (fst header).
Definition current_length (header : hdr) := snd (fst header).
Definition checksum (header : hdr) := snd header.
Definition mk_header (len : hdr) : header :=
      ($ (fst (previous_length len)),
      ($ (snd (previous_length len)),
      ($ (fst (current_length len)),
      ($ (snd (current_length len)),
      (fst (checksum len),
      (snd (checksum len), tt)))))).
Theorem hdrsz_ok : Rec.len header_type <= valulen.
(* hint proof tokens: 21 *)
Proof.
      rewrite valulen_is. apply leb_complete. compute. trivial.
    Qed.
Local Hint Resolve hdrsz_ok.
Lemma plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.
(* hint proof tokens: 16 *)
Proof.
      apply le_plus_minus_r; auto.
    Qed.
Definition hdr2val (h : header) : valu.
set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
rewrite plus_minus_header in r.
refine r.
Defined.
Definition val2hdr (v : valu) : header.
apply Rec.of_word.
rewrite <- plus_minus_header in v.
refine (split1 _ _ v).
Defined.
Arguments hdr2val: simpl never.
Lemma val2hdr2val : forall h,
      val2hdr (hdr2val h) = h.
(* hint proof tokens: 58 *)
Proof.
      unfold val2hdr, hdr2val.
      unfold eq_rec_r, eq_rec.
      intros.
      rewrite <- plus_minus_header.
      unfold zext.
      autorewrite with core; auto.
      simpl; destruct h; tauto.
    Qed.
Arguments val2hdr: simpl never.
Opaque val2hdr.
Definition xparams := log_xparams.
Definition LAHdr := LogHeader.
Inductive state : Type :=
    | Synced : hdr -> state
    | Unsync : hdr -> hdr -> state
    .
Definition hdr_goodSize header :=
      goodSize addrlen (fst (previous_length header)) /\
      goodSize addrlen (snd (previous_length header)) /\
      goodSize addrlen (fst (current_length header)) /\
      goodSize addrlen (snd (current_length header)).
Definition state_goodSize st :=
      match st with
      | Synced n => hdr_goodSize n
      | Unsync n o => hdr_goodSize n /\ hdr_goodSize o
      end.
Definition rep xp state : @rawpred :=
      ([[ state_goodSize state ]] *
      match state with
      | Synced n =>
         (LAHdr xp) |+> (hdr2val (mk_header n), nil)
      | Unsync n o =>
         (LAHdr xp) |+> (hdr2val (mk_header n), [hdr2val (mk_header o)]%list)
      end)%pred.
Definition xform_rep_synced : forall xp n,
      crash_xform (rep xp (Synced n)) =p=> rep xp (Synced n).
(* hint proof tokens: 40 *)
Proof.
      unfold rep; intros; simpl.
      xform; auto.
      rewrite crash_xform_ptsto_subset'.
      cancel.
      rewrite H1; auto.
    Qed.
Definition xform_rep_unsync : forall xp n o,
      crash_xform (rep xp (Unsync n o)) =p=> rep xp (Synced n) \/ rep xp (Synced o).
(* hint proof tokens: 45 *)
Proof.
      unfold rep; intros; simpl.
      xform.
      rewrite crash_xform_ptsto_subset; unfold ptsto_subset.
      cancel.
      or_l; cancel.
      cancel.
    Qed.
Definition read xp cs := Eval compute_rec in
      let^ (cs, v) <- BUFCACHE.read (LAHdr xp) cs;
      let header := (val2hdr v) in
      Ret ^(cs, ((# (header :-> "previous_ndesc"), # (header :-> "previous_ndata")),
                (# (header :-> "ndesc"), # (header :-> "ndata")),
                (header :-> "addr_checksum", header :-> "valu_checksum"))).
Definition write xp n cs :=
      cs <- BUFCACHE.write (LAHdr xp) (hdr2val (mk_header n)) cs;
      Ret cs.
Definition sync xp cs :=
      cs <- BUFCACHE.sync (LAHdr xp) cs;
      Ret cs.
Definition sync_now xp cs :=
      cs <- BUFCACHE.begin_sync cs;
      cs <- BUFCACHE.sync (LAHdr xp) cs;
      cs <- BUFCACHE.end_sync cs;
      Ret cs.
Definition init xp cs :=
      h <- Hash default_valu;
      cs <- BUFCACHE.write (LAHdr xp) (hdr2val (mk_header ((0, 0), (0, 0), (h, h)))) cs;
      cs <- BUFCACHE.begin_sync cs;
      cs <- BUFCACHE.sync (LAHdr xp) cs;
      cs <- BUFCACHE.end_sync cs;
      Ret cs.
Local Hint Unfold rep state_goodSize : hoare_unfold.
Theorem write_ok : forall xp n cs,
    {< F d old,
    PRE:hm         BUFCACHE.rep cs d *
                   [[ hdr_goodSize n ]] *
                   [[ previous_length n = current_length old \/
                      previous_length old = current_length n ]] *
                   [[ (F * rep xp (Synced old))%pred d ]]
    POST:hm' RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Unsync n old))%pred d' ]]
    XCRASH:hm'     exists cs' d', BUFCACHE.rep cs' d' * 
                   [[ (F * rep xp (Unsync n old))%pred d' ]]
    >} write xp n cs.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Theorem read_ok : forall xp cs,
    {< F d n,
    PRE:hm         BUFCACHE.rep cs d *
                   [[ (F * rep xp (Synced n))%pred d ]]
    POST:hm' RET: ^(cs, r)
                   BUFCACHE.rep cs d *
                   [[ (F * rep xp (Synced n))%pred d ]] *
                   [[ r = n ]]
    CRASH:hm' exists cs', BUFCACHE.rep cs' d
    >} read xp cs.
Proof.
(* skipped proof tokens: 81 *)
Admitted.
Theorem sync_ok : forall xp cs,
    {< F d0 d n old,
    PRE:hm         BUFCACHE.synrep cs d0 d *
                   [[ (F * rep xp (Unsync n old))%pred d ]] *
                   [[ sync_invariant F ]]
    POST:hm' RET: cs
                   exists d', BUFCACHE.synrep cs d0 d' *
                   [[ (F * rep xp (Synced n))%pred d' ]]
    CRASH:hm'  exists cs', BUFCACHE.rep cs' d0
    >} sync xp cs.
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Theorem sync_now_ok : forall xp cs,
    {< F d n old,
    PRE:hm         BUFCACHE.rep cs d *
                   [[ (F * rep xp (Unsync n old))%pred d ]] *
                   [[ sync_invariant F ]]
    POST:hm' RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Synced n))%pred d' ]]
    CRASH:hm'  exists cs', BUFCACHE.rep cs' d
    >} sync_now xp cs.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Theorem init_ok : forall xp cs,
    {< F d v0,
    PRE:hm         BUFCACHE.rep cs d *
                   [[ (F * (LAHdr xp) |+> v0)%pred d ]] *
                   [[ sync_invariant F ]]
    POST:hm' RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Synced ((0, 0), (0, 0),
                          (hash_fwd default_valu, hash_fwd default_valu))))%pred d' ]]
    CRASH:hm'  any
    >} init xp cs.
(* hint proof tokens: 76 *)
Proof.
      unfold init, rep; intros.
      step.
      step.
      step.
      step.
      step.
      prestep; unfold rep; safecancel.
      unfold hdr_goodSize; cbn.
      repeat split; apply zero_lt_pow2.
      all: apply pimpl_any.
      Unshelve. exact tt.
    Qed.
Theorem sync_invariant_rep : forall xp st,
      sync_invariant (rep xp st).
Proof.
(* skipped proof tokens: 17 *)
Admitted.
Hint Resolve sync_invariant_rep.
Hint Extern 1 ({{_}} Bind (write _ _ _) _) => apply write_ok : prog.
Hint Extern 1 ({{_}} Bind (read _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (sync _ _) _) => apply sync_ok : prog.
Hint Extern 1 ({{_}} Bind (sync_now _ _) _) => apply sync_now_ok : prog.
Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
End Hdr.
Definition entry := (addr * valu)%type.
Definition contents := list entry.
Inductive state :=
  
  | Synced (l: contents)

  
  | Truncated (old: contents)

  
  | Extended (old: contents) (new: contents)

  
  | ExtendedCrashed (old: contents) (new: contents)

  
  | Rollback (old: contents)

  
  | RollbackUnsync (old: contents)
  .
Definition ent_addr (e : entry) := addr2w (fst e).
Definition ent_valu (e : entry) := snd e.
Definition ndesc_log (log : contents) := (divup (length log) DescSig.items_per_val).
Definition ndesc_list T (l : list T) := (divup (length l) DescSig.items_per_val).
Fixpoint log_nonzero (log : contents) : list entry :=
    match log with
    | (0, _) :: rest => log_nonzero rest
    | e :: rest => e :: log_nonzero rest
    | nil => nil
    end.
Definition vals_nonzero (log : contents) := map ent_valu (log_nonzero log).
Fixpoint nonzero_addrs (al : list addr) : nat :=
    match al with
    | 0 :: rest => nonzero_addrs rest
    | e :: rest => S (nonzero_addrs rest)
    | nil => 0
    end.
Fixpoint combine_nonzero (al : list addr) (vl : list valu) : contents :=
    match al, vl with
    | 0 :: al', v :: vl' => combine_nonzero al' vl
    | a :: al', v :: vl' => (a, v) :: (combine_nonzero al' vl')
    | _, _ => nil
    end.
Definition ndata_log (log : contents) := nonzero_addrs (map fst log) .
Definition addr_valid (e : entry) := goodSize addrlen (fst e).
Definition entry_valid (ent : entry) := fst ent <> 0 /\ addr_valid ent.
Definition rep_contents xp (log : contents) : rawpred :=
    ( [[ Forall addr_valid log ]] *
     Desc.array_rep xp 0 (Desc.Synced (map ent_addr log)) *
     Data.array_rep xp 0 (Data.Synced (vals_nonzero log)) *
     Desc.avail_rep xp (ndesc_log log) (LogDescLen xp - (ndesc_log log)) *
     Data.avail_rep xp (ndata_log log) (LogLen xp - (ndata_log log))
     )%pred.
Definition padded_addr (al : list addr) :=
    setlen al (roundup (length al) DescSig.items_per_val) 0.
Definition padded_log (log : contents) :=
    setlen log (roundup (length log) DescSig.items_per_val) (0, $0).
Definition rep_contents_unmatched xp (old : contents) new_addr new_valu : rawpred :=
    ( [[ Forall addr_valid old ]] *
      
     Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old))) *
     Desc.array_rep xp (ndesc_log old) (Desc.Synced new_addr) *
     Data.array_rep xp 0 (Data.Synced (vals_nonzero (padded_log old))) *
     Data.array_rep xp (ndata_log old) (Data.Synced new_valu) *
     Desc.avail_rep xp (ndesc_log old + ndesc_list new_addr) (LogDescLen xp - (ndesc_log old) - (ndesc_list new_addr)) *
     Data.avail_rep xp (ndata_log old + length new_valu) (LogLen xp - (ndata_log old) - (length new_valu))
     )%pred.
Definition loglen_valid xp ndesc ndata :=
    ndesc <= LogDescLen xp  /\ ndata <= LogLen xp.
Definition loglen_invalid xp ndesc ndata :=
    ndesc > LogDescLen xp \/ ndata > LogLen xp.
Definition checksums_match (l : contents) h hm :=
    hash_list_rep (rev (DescDefs.ipack (map ent_addr l))) (fst h) hm /\
    hash_list_rep (rev (vals_nonzero l)) (snd h) hm.
Definition hide_or (P : Prop) := P.
Opaque hide_or.
Definition rep_inner xp (st : state) hm : rawpred :=
  (match st with
  | Synced l =>
      exists prev_len h,
       Hdr.rep xp (Hdr.Synced (prev_len,
                              (ndesc_log l, ndata_log l),
                              h)) *
       rep_contents xp l *
       [[ checksums_match l h hm ]]

  | Truncated old =>
      exists prev_len h h',
       Hdr.rep xp (Hdr.Unsync ((ndesc_log old, ndata_log old), (0, 0), h')
                              (prev_len, (ndesc_log old, ndata_log old), h)) *
       rep_contents xp old *
       [[ checksums_match old h hm ]] *
       [[ checksums_match [] h' hm ]]

  | Extended old new =>
      exists prev_len h h',
       Hdr.rep xp (Hdr.Unsync ((ndesc_log old, ndata_log old),
                                (ndesc_log old + ndesc_log new,
                                 ndata_log old + ndata_log new), h')
                               (prev_len, (ndesc_log old, ndata_log old), h)) *
       rep_contents xp old *
       [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                          (ndata_log old + ndata_log new) ]] *
       [[ checksums_match old h hm ]] *
       [[ checksums_match (padded_log old ++ new) h' hm ]] *
       [[ Forall entry_valid new ]]

  | ExtendedCrashed old new =>
      exists h synced_addr synced_valu ndesc,
        Hdr.rep xp (Hdr.Synced ((ndesc_log old, ndata_log old),
                                (ndesc_log old + ndesc_log new,
                                 ndata_log old + ndata_log new),
                                h)) *
        rep_contents_unmatched xp old synced_addr synced_valu *
        [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                           (ndata_log old + ndata_log new) ]] *
        
        [[ length synced_addr = (ndesc * DescSig.items_per_val)%nat ]] *
        [[ ndesc = ndesc_log new ]] *
        [[ length synced_valu = ndata_log new ]] *
        [[ checksums_match (padded_log old ++ new) h hm ]] *
        [[ Forall entry_valid new ]]

  | Rollback old =>
      exists synced_addr synced_valu h new,
        Hdr.rep xp (Hdr.Synced ((ndesc_log old, ndata_log old),
                                (ndesc_log old + ndesc_log new,
                                 ndata_log old + ndata_log new),
                                 h)) *
        rep_contents_unmatched xp old synced_addr synced_valu *
        [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                           (ndata_log old + ndata_log new) ]] *
        
        [[ length synced_addr = ((ndesc_log new) * DescSig.items_per_val)%nat ]] *
        [[ length synced_valu = ndata_log new ]] *
        [[ checksums_match (padded_log old ++ new) h hm ]] *
        [[ hide_or (DescDefs.ipack (map ent_addr (padded_log new)) <> DescDefs.ipack synced_addr \/
            vals_nonzero new <> synced_valu) ]] *
        [[ Forall entry_valid new ]]

  | RollbackUnsync old =>
      exists synced_addr synced_valu h h' new prev_len,
         Hdr.rep xp (Hdr.Unsync (prev_len, (ndesc_log old, ndata_log old), h')
                                ((ndesc_log old, ndata_log old),
                                 (ndesc_log old + ndesc_log new,
                                  ndata_log old + ndata_log new), h)) *
        rep_contents_unmatched xp old synced_addr synced_valu *
        [[ loglen_valid xp (ndesc_log old + ndesc_log new)
                           (ndata_log old + ndata_log new) ]] *
        
        [[ length synced_addr = ((ndesc_log new) * DescSig.items_per_val)%nat ]] *
        [[ length synced_valu = ndata_log new ]] *
        [[ checksums_match old h' hm ]] *
        [[ checksums_match (padded_log old ++ new) h hm ]] *
        [[ hide_or (DescDefs.ipack (map ent_addr (padded_log new)) <> DescDefs.ipack synced_addr \/
            vals_nonzero new <> synced_valu) ]] *
        [[ Forall entry_valid new ]]

  end)%pred.
Definition xparams_ok xp := 
    DescSig.xparams_ok xp /\ DataSig.xparams_ok xp /\
    (LogLen xp) = DescSig.items_per_val * (LogDescLen xp).
Definition rep xp st hm:=
    ([[ xparams_ok xp ]] * rep_inner xp st hm)%pred.
Definition would_recover' xp l hm :=
    (rep xp (Synced l) hm \/
      rep xp (Rollback l) hm \/
      rep xp (RollbackUnsync l) hm)%pred.
Definition would_recover xp F l hm :=
    (exists cs d,
      BUFCACHE.rep cs d *
      [[ (F * would_recover' xp l hm)%pred d ]])%pred.
Theorem sync_invariant_rep : forall xp st hm,
    sync_invariant (rep xp st hm).
(* hint proof tokens: 33 *)
Proof.
    unfold rep, rep_inner, rep_contents, rep_contents_unmatched.
    destruct st; intros; eauto 50.
  Qed.
Hint Resolve sync_invariant_rep.
Theorem sync_invariant_would_recover' : forall xp l hm,
    sync_invariant (would_recover' xp l hm).
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Theorem sync_invariant_would_recover : forall xp F l hm,
    sync_invariant (would_recover xp F l hm).
(* hint proof tokens: 18 *)
Proof.
    unfold would_recover; intros; eauto.
  Qed.
Hint Resolve sync_invariant_would_recover sync_invariant_would_recover'.
Local Hint Unfold rep rep_inner rep_contents xparams_ok: hoare_unfold.
Definition avail xp cs :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(_, (ndesc, _), _) := nr in
    Ret ^(cs, ((LogLen xp) - ndesc * DescSig.items_per_val)).
Definition read xp cs :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(_, (ndesc, ndata), _) := nr in
    let^ (cs, wal) <- Desc.read_all xp ndesc cs;
    let al := map (@wordToNat addrlen) wal in
    let^ (cs, vl) <- Data.read_all xp ndata cs;
    Ret ^(cs, combine_nonzero al vl).
Remove Hints Forall_nil.
Lemma Forall_True : forall A (l : list A),
    Forall (fun _ : A => True) l.
(* hint proof tokens: 18 *)
Proof.
    intros; rewrite Forall_forall; auto.
  Qed.
Hint Resolve Forall_True.
Lemma combine_nonzero_ok : forall l,
    combine_nonzero (map fst l) (vals_nonzero l) = log_nonzero l.
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma combine_nonzero_nil : forall a,
    combine_nonzero a nil = nil.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Local Hint Resolve combine_nonzero_nil.
Lemma combine_nonzero_app_zero : forall a b,
    combine_nonzero (a ++ [0]) b = combine_nonzero a b.
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma combine_nonzero_app_zeros : forall n a b,
    combine_nonzero (a ++ repeat 0 n) b = combine_nonzero a b.
(* hint proof tokens: 43 *)
Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply combine_nonzero_app_zero.
  Qed.
Local Hint Resolve roundup_ge DescDefs.items_per_val_gt_0.
Lemma combine_nonzero_padded_addr : forall a b,
    combine_nonzero (padded_addr a) b = combine_nonzero a b.
Proof.
(* skipped proof tokens: 87 *)
Admitted.
Lemma map_fst_repeat : forall A B n (a : A) (b : B),
    map fst (repeat (a, b) n) = repeat a n.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma map_entaddr_repeat_0 : forall n b,
    map ent_addr (repeat (0, b) n) = repeat $0 n.
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma combine_nonzero_padded_log : forall l b,
    combine_nonzero (map fst (padded_log l)) b = combine_nonzero (map fst l) b.
(* hint proof tokens: 95 *)
Proof.
    unfold padded_log, setlen, roundup; intros.
    induction l; simpl.
    rewrite divup_0; simpl; auto.
    
    rewrite <- IHl.
    destruct a, b, n; simpl; auto;
    repeat rewrite firstn_oob; simpl; auto;
    repeat rewrite map_app;
    setoid_rewrite map_fst_repeat;
    repeat rewrite combine_nonzero_app_zeros; auto.
  Qed.
Lemma addr_valid_padded : forall l,
    Forall addr_valid l -> Forall addr_valid (padded_log l).
(* hint proof tokens: 71 *)
Proof.
    unfold padded_log, setlen, roundup; intros.
    rewrite firstn_oob; simpl; auto.
    apply Forall_append; auto.
    rewrite Forall_forall; intros.
    apply repeat_spec in H0; subst.
    unfold addr_valid; simpl.
    apply zero_lt_pow2.
  Qed.
Lemma padded_addr_valid : forall l,
    Forall addr_valid (padded_log l) ->
    Forall addr_valid l.
(* hint proof tokens: 38 *)
Proof.
    unfold padded_log, setlen; intros.
    rewrite firstn_oob in H; auto.
    eapply forall_app_r; eauto.
  Qed.
Local Hint Resolve addr_valid_padded padded_addr_valid.
Lemma map_wordToNat_ent_addr : forall l,
    Forall addr_valid l ->
    (map (@wordToNat _) (map ent_addr l)) = map fst l.
(* hint proof tokens: 75 *)
Proof.
    unfold ent_addr, addr2w.
    induction l; intros; simpl; auto.
    rewrite IHl; f_equal.
    rewrite wordToNat_natToWord_idempotent'; auto.
    apply Forall_inv in H; unfold addr_valid in H; auto.
    eapply Forall_cons2; eauto.
  Qed.
Lemma combine_nonzero_padded_wordToNat : forall l,
    Forall addr_valid l ->
    combine_nonzero (map (@wordToNat _) (map ent_addr (padded_log l))) (vals_nonzero l) = log_nonzero l.
(* hint proof tokens: 51 *)
Proof.
    intros; unfold ent_addr, addr2w.
    rewrite <- combine_nonzero_ok.
    rewrite <- combine_nonzero_padded_log.
    f_equal.
    rewrite map_wordToNat_ent_addr; auto.
  Qed.
Lemma vals_nonzero_addrs : forall l,
    length (vals_nonzero l) = nonzero_addrs (map fst l).
(* hint proof tokens: 27 *)
Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.
Lemma log_nonzero_addrs : forall l,
    length (log_nonzero l) = nonzero_addrs (map fst l).
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Lemma desc_ipack_padded : forall l,
    DescDefs.ipack (map ent_addr l) = DescDefs.ipack (map ent_addr (padded_log l)).
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Local Hint Resolve combine_nonzero_padded_wordToNat.
Lemma desc_padding_synced_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Synced (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Synced (map ent_addr l)).
(* hint proof tokens: 131 *)
Proof.
     unfold Desc.array_rep, Desc.synced_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H0.
     rewrite firstn_oob, map_app in H0 by auto.
     apply Desc.items_valid_app in H0; intuition.
     apply eq_sym; apply desc_ipack_padded.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     apply desc_ipack_padded.
  Qed.
Lemma desc_padding_unsync_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Unsync (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Unsync (map ent_addr l)).
(* hint proof tokens: 128 *)
Proof.
     unfold Desc.array_rep, Desc.unsync_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H.
     rewrite firstn_oob, map_app in H by auto.
     apply Desc.items_valid_app in H; intuition.
     apply eq_sym; apply desc_ipack_padded.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     apply desc_ipack_padded.
  Qed.
Lemma goodSize_ndesc : forall l,
    goodSize addrlen (length l) -> goodSize addrlen (ndesc_log l).
(* hint proof tokens: 65 *)
Proof.
    intros; unfold ndesc_log.
    eapply goodSize_trans; [ apply divup_le | eauto ].
    destruct (mult_O_le (length l) DescSig.items_per_val); auto.
    contradict H0; apply DescDefs.items_per_val_not_0.
  Qed.
Local Hint Resolve goodSize_ndesc.
Lemma padded_log_length: forall l,
    length (padded_log l) = roundup (length l) DescSig.items_per_val.
(* hint proof tokens: 24 *)
Proof.
    unfold padded_log, roundup; intros.
    rewrite setlen_length; auto.
  Qed.
Lemma nonzero_addrs_app_zero : forall a,
    nonzero_addrs (a ++ [0]) = nonzero_addrs a.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma nonzero_addrs_app_zeros : forall n a,
    nonzero_addrs (a ++ repeat 0 n) = nonzero_addrs a.
(* hint proof tokens: 44 *)
Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply nonzero_addrs_app_zero.
  Qed.
Lemma nonzero_addrs_padded_log : forall l,
    nonzero_addrs (map fst (padded_log l)) = nonzero_addrs (map fst l).
Proof.
(* skipped proof tokens: 105 *)
Admitted.
Lemma vals_nonzero_length : forall l,
    length (vals_nonzero l) <= length l.
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Lemma vals_nonzero_app : forall a b,
    vals_nonzero (a ++ b) = vals_nonzero a ++ vals_nonzero b.
(* hint proof tokens: 39 *)
Proof.
    unfold vals_nonzero; induction a; intros; simpl; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.
Lemma log_nonzero_repeat_0 : forall n,
    log_nonzero (repeat (0, $0) n) = nil.
(* hint proof tokens: 15 *)
Proof.
    induction n; simpl; auto.
  Qed.
Lemma log_nonzero_app : forall a b,
    log_nonzero (a ++ b) = log_nonzero a ++ log_nonzero b.
(* hint proof tokens: 34 *)
Proof.
    induction a; simpl; intros; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.
Lemma vals_nonzero_padded_log : forall l,
    vals_nonzero (padded_log l) = vals_nonzero l.
(* hint proof tokens: 151 *)
Proof.
    unfold vals_nonzero, padded_log, setlen, roundup; simpl.
    induction l; intros; simpl; auto.
    rewrite firstn_oob; simpl; auto.
    rewrite log_nonzero_repeat_0; auto.

    destruct a, n.
    rewrite <- IHl.
    repeat rewrite firstn_oob; simpl; auto.
    repeat rewrite log_nonzero_app, map_app.
    repeat rewrite log_nonzero_repeat_0; auto.

    repeat rewrite firstn_oob; simpl; auto.
    f_equal.
    repeat rewrite log_nonzero_app, map_app.
    repeat rewrite log_nonzero_repeat_0; auto.
    simpl; rewrite app_nil_r; auto.
  Qed.
Lemma ndata_log_goodSize : forall l,
    goodSize addrlen (length l) -> goodSize addrlen (ndata_log l).
(* hint proof tokens: 43 *)
Proof.
    unfold ndata_log; intros.
    rewrite <- vals_nonzero_addrs.
    eapply goodSize_trans.
    apply vals_nonzero_length; auto.
    auto.
  Qed.
Local Hint Resolve ndata_log_goodSize.
Lemma padded_log_idem : forall l,
    padded_log (padded_log l) = padded_log l.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma padded_log_app : forall l1 l2,
    padded_log (padded_log l1 ++ l2) = padded_log l1 ++ padded_log l2.
Proof.
(* skipped proof tokens: 71 *)
Admitted.
Ltac solve_checksums :=
  try (match goal with
    | [ |- checksums_match _ _ _ ]
      => unfold checksums_match in *
    end; intuition;
    [
      solve_hash_list_rep;
      try (rewrite map_app;
      erewrite DescDefs.ipack_app;
      try solve [ rewrite map_length, padded_log_length; unfold roundup; eauto ];
      rewrite rev_app_distr)
      | solve_hash_list_rep;
      try rewrite vals_nonzero_app, vals_nonzero_padded_log, rev_app_distr;
      try rewrite padded_log_app, map_app, rev_app_distr
    ];
    repeat match goal with
    | [ H: context[hash_list_rep (_ ++ [])] |- _ ]
      => rewrite app_nil_r in H
    end;
    try rewrite <- desc_ipack_padded in *;
    solve_hash_list_rep).
Arguments Desc.array_rep : simpl never.
Arguments Data.array_rep : simpl never.
Arguments Desc.avail_rep : simpl never.
Arguments Data.avail_rep : simpl never.
Arguments divup : simpl never.
Hint Extern 0 (okToUnify (Hdr.rep _ _) (Hdr.rep _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (Desc.array_rep _ _ _) (Desc.array_rep _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (Data.array_rep _ _ _) (Data.array_rep _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (Desc.avail_rep _ _ _) (Desc.avail_rep _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (Data.avail_rep _ _ _) (Data.avail_rep _ _ _)) => constructor : okToUnify.
Definition avail_ok : forall xp cs,
    {< F l d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ r = (LogLen xp) - roundup (length l) DescSig.items_per_val ]]
    CRASH:hm_crash exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} avail xp cs.
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Definition read_ok : forall xp cs,
    {< F l d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ r = log_nonzero l ]]
    CRASH:hm_crash exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} read xp cs.
Proof.
(* skipped proof tokens: 192 *)
Admitted.
Lemma goodSize_0 : forall sz, goodSize sz 0.
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma ndesc_log_nil : ndesc_log nil = 0.
(* hint proof tokens: 24 *)
Proof.
    unfold ndesc_log; simpl.
    rewrite divup_0; auto.
  Qed.
Lemma ndata_log_nil : ndata_log nil = 0.
(* hint proof tokens: 17 *)
Proof.
    unfold ndata_log; simpl; auto.
  Qed.
Local Hint Resolve goodSize_0.
Definition init xp cs :=
    cs <- Hdr.init xp cs;
    Ret cs.
Definition trunc xp cs :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(_, current_length, _) := nr in
    h <- Hash default_valu;
    cs <- Hdr.write xp (current_length, (0, 0), (h, h)) cs;
    cs <- Hdr.sync_now xp cs;
    Ret cs.
Local Hint Resolve Forall_nil.
Definition initrep xp :=
    (exists hdr, LogHeader xp |+> hdr *
     Desc.avail_rep xp 0 (LogDescLen xp) *
     Data.avail_rep xp 0 (LogLen xp))%pred.
Definition init_ok' : forall xp cs,
    {< F d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * initrep xp)%pred d ]] *
          [[ xparams_ok xp /\ sync_invariant F ]]
    POST:hm' RET: cs  exists d',
          BUFCACHE.rep cs d' *
          [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:hm_crash any
    >} init xp cs.
Proof.
(* skipped proof tokens: 122 *)
Admitted.
Definition init_ok : forall xp cs,
    {< F l d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             xparams_ok xp ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: cs  exists d',
          BUFCACHE.rep cs d' *
          [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:hm_crash any
    >} init xp cs.
Proof.
(* skipped proof tokens: 172 *)
Admitted.
Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
Lemma helper_sep_star_reorder : forall (a b c d : rawpred),
    a * b * c * d =p=> (a * c) * (b * d).
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma helper_add_sub_0 : forall a b,
    a <= b -> a + (b - a) + 0 = b.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma helper_trunc_ok : forall xp l prev_len h,
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr l)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero l)) *
    Desc.avail_rep xp (ndesc_log l) (LogDescLen xp - ndesc_log l) *
    Data.avail_rep xp (ndata_log l) (LogLen xp - ndata_log l) *
    Hdr.rep xp (Hdr.Synced (prev_len, (0, 0), h))
    =p=>
    Hdr.rep xp (Hdr.Synced (prev_len, (ndesc_log [], ndata_log []), h)) *
    Desc.array_rep xp 0 (Desc.Synced []) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero [])) *
    Desc.avail_rep xp (ndesc_log []) (LogDescLen xp - ndesc_log []) *
    Data.avail_rep xp (ndata_log []) (LogLen xp - ndata_log []).
Proof.
(* skipped proof tokens: 166 *)
Admitted.
Definition trunc_ok : forall xp cs,
    {< F l d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: cs  exists d',
          BUFCACHE.rep cs d' *
          [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:hm_crash exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * (rep xp (Synced l) hm_crash))%pred d' ]] \/
          [[ (F * (rep xp (Truncated l) hm_crash))%pred d' ]] )
    >} trunc xp cs.
(* hint proof tokens: 291 *)
Proof.
    unfold trunc.
    step.
    step.
    step.

    unfold Hdr.rep in H0.
    destruct_lift H0.
    unfold Hdr.hdr_goodSize in *; intuition.

    step.
    step.

    
    cancel_by helper_trunc_ok.
    solve_checksums.
    replace (DescDefs.ipack (map ent_addr [])) with (@nil valu).
    solve_hash_list_rep; auto.
    symmetry. apply DescDefs.ipack_nil.
    auto.

    
    repeat xcrash_rewrite.
    xform_norm. cancel. xform_normr; cancel.
    or_r; cancel.
    solve_checksums.
    solve_checksums; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    solve_hash_list_rep; auto.

    repeat xcrash_rewrite.
    xform_norm; cancel. xform_normr; cancel.
    or_r; cancel.
    solve_checksums.
    solve_checksums; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    solve_hash_list_rep; auto.

    xcrash_rewrite.
    xform_normr; cancel.
    or_l; cancel.
    solve_checksums.

    xcrash_rewrite.
    xform_normr; cancel.
    or_l; cancel.
    solve_checksums.

    Unshelve.
    constructor.
  Qed.
Theorem loglen_valid_dec xp ndesc ndata :
    {loglen_valid xp ndesc ndata} + {loglen_invalid xp ndesc ndata }.
Proof.
    unfold loglen_valid, loglen_invalid.
    destruct (lt_dec (LogDescLen xp) ndesc);
    destruct (lt_dec (LogLen xp) ndata); simpl; auto.
    left; intuition.
  Qed.
Remove Hints goodSize_0.
Definition entry_valid_ndata : forall l,
    Forall entry_valid l -> ndata_log l = length l.
Proof.
(* skipped proof tokens: 76 *)
Admitted.
Lemma loglen_valid_desc_valid : forall xp old new,
    DescSig.xparams_ok xp ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    Desc.items_valid xp (ndesc_log old) (map ent_addr new).
(* hint proof tokens: 61 *)
Proof.
    unfold Desc.items_valid, loglen_valid.
    intuition.
    unfold DescSig.RALen; lia.
    autorewrite with lists; unfold DescSig.RALen.
    apply divup_ge; auto.
    unfold ndesc_log in *; lia.
  Qed.
Local Hint Resolve loglen_valid_desc_valid.
Lemma loglen_valid_data_valid : forall xp old new,
    DataSig.xparams_ok xp ->
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    Data.items_valid xp (ndata_log old) (map ent_valu new).
Proof.
(* original proof tokens: 77 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve loglen_valid_data_valid.
Lemma helper_loglen_desc_valid_extend : forall xp new old,
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndesc_log new + (LogDescLen xp - ndesc_log old - ndesc_log new) 
      = LogDescLen xp - ndesc_log old.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma helper_loglen_data_valid_extend : forall xp new old,
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndata_log new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.
(* hint proof tokens: 22 *)
Proof.
    unfold loglen_valid, ndata_log; intros.
    lia.
  Qed.
Lemma helper_loglen_data_valid_extend_entry_valid : forall xp new old,
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.
(* hint proof tokens: 31 *)
Proof.
    intros.
    rewrite <- entry_valid_ndata by auto.
    apply helper_loglen_data_valid_extend; auto.
  Qed.
Lemma padded_desc_valid : forall xp st l,
    Desc.items_valid xp st (map ent_addr l)
    -> Desc.items_valid xp st (map ent_addr (padded_log l)).
Proof.
(* skipped proof tokens: 61 *)
Admitted.
Lemma mul_le_mono_helper : forall a b,
    b > 0 -> a <= a * b.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma loglen_valid_goodSize_l : forall xp a b,
    loglen_valid xp a b -> DescSig.xparams_ok xp -> DataSig.xparams_ok xp ->
    goodSize addrlen a.
Proof.
(* skipped proof tokens: 52 *)
Admitted.
Lemma loglen_valid_goodSize_r : forall xp a b,
    loglen_valid xp a b -> DescSig.xparams_ok xp -> DataSig.xparams_ok xp ->
    goodSize addrlen b.
Proof.
(* skipped proof tokens: 52 *)
Admitted.
Lemma ent_valid_addr_valid : forall l,
    Forall entry_valid l -> Forall addr_valid l.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Local Hint Resolve ent_valid_addr_valid.
Local Hint Resolve Forall_append DescDefs.items_per_val_not_0.
Lemma helper_add_sub : forall a b,
    a <= b -> a + (b - a) = b.
(* hint proof tokens: 12 *)
Proof.
    intros; lia.
  Qed.
Lemma nonzero_addrs_app : forall a b,
    nonzero_addrs (a ++ b) = nonzero_addrs a + nonzero_addrs b.
(* hint proof tokens: 30 *)
Proof.
    induction a; intros; simpl; auto.
    destruct a; auto.
    rewrite IHa; lia.
  Qed.
Lemma ndata_log_app : forall a b,
    ndata_log (a ++ b) = ndata_log a + ndata_log b.
(* hint proof tokens: 32 *)
Proof.
    unfold ndata_log;  intros.
    repeat rewrite map_app.
    rewrite nonzero_addrs_app; auto.
  Qed.
Lemma ndesc_log_padded_log : forall l,
    ndesc_log (padded_log l) = ndesc_log l.
(* hint proof tokens: 33 *)
Proof.
    unfold ndesc_log; intros.
    rewrite padded_log_length.
    unfold roundup; rewrite divup_divup; auto.
  Qed.
Lemma ndesc_log_app : forall a b,
    length a = roundup (length a) DescSig.items_per_val ->
    ndesc_log (a ++ b) = ndesc_log a + ndesc_log b.
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma ndesc_log_padded_app : forall a b,
    ndesc_log (padded_log a ++ b) = ndesc_log a + ndesc_log b.
(* hint proof tokens: 42 *)
Proof.
    intros.
    rewrite ndesc_log_app.
    rewrite ndesc_log_padded_log; auto.
    rewrite padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.
Lemma ndata_log_padded_log : forall a,
    ndata_log (padded_log a) = ndata_log a.
Proof.
(* original proof tokens: 78 *)

(* No more tactics to try *)
Admitted.

Lemma ndata_log_padded_app : forall a b,
    ndata_log (padded_log a ++ b) = ndata_log a + ndata_log b.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma log_nonzero_rev_comm : forall l,
    log_nonzero (rev l) = rev (log_nonzero l).
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma entry_valid_vals_nonzero : forall l,
    Forall entry_valid l ->
    log_nonzero l = l.
(* hint proof tokens: 78 *)
Proof.
    unfold entry_valid; induction l; simpl; auto.
    destruct a, n; simpl; auto; intros.
    exfalso.
    rewrite Forall_forall in H; intuition.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    eapply Forall_cons2; eauto.
  Qed.
Lemma nonzero_addrs_entry_valid : forall l,
    Forall entry_valid l ->
    nonzero_addrs (map fst l) = length l.
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Lemma desc_ipack_injective : forall l1 l2 n1 n2,
    length l1 = n1 * DescSig.items_per_val ->
    length l2 = n2 * DescSig.items_per_val ->
    DescDefs.ipack l1 = DescDefs.ipack l2 ->
    l1 = l2.
Proof.
(* skipped proof tokens: 48 *)
Admitted.
Lemma ndesc_log_ndesc_list : forall l,
    ndesc_log l = ndesc_list (map ent_addr (padded_log l)).
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma extend_ok_helper : forall F xp old new,
    Forall entry_valid new ->
    Data.array_rep xp (ndata_log old) (Data.Synced (map ent_valu new)) *
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr old)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero old)) *
    Desc.avail_rep xp (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
      (LogDescLen xp - ndesc_log old - ndesc_log new) *
    Data.avail_rep xp (ndata_log old + divup (length (map ent_valu new)) DataSig.items_per_val)
      (LogLen xp - ndata_log old - ndata_log new) *
    Desc.array_rep xp (ndesc_log old) (Desc.Synced (map ent_addr (padded_log new))) * F
    =p=>
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old ++ new))) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero (padded_log old ++ new))) *
    Desc.avail_rep xp (ndesc_log (padded_log old ++ new)) 
                      (LogDescLen xp - ndesc_log (padded_log old ++ new)) *
    Data.avail_rep xp (ndata_log (padded_log old ++ new))
                      (LogLen xp - ndata_log (padded_log old ++ new)) * F.
Proof.
(* skipped proof tokens: 219 *)
Admitted.
Lemma nonzero_addrs_bound : forall l,
    nonzero_addrs l <= length l.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 27 *)

Proof.
  induction l; simpl.
  - lia.
  - destruct a; simpl; lia.
Qed.

Lemma extend_ok_synced_hdr_helper : forall xp prev_len old new h,
    Hdr.rep xp (Hdr.Synced (prev_len,
                            (ndesc_log old + ndesc_log new,
                             ndata_log old + ndata_log new),
                            h))
    =p=>
    Hdr.rep xp (Hdr.Synced (prev_len,
                            (ndesc_log (padded_log old ++ new),
                             ndata_log (padded_log old ++ new)),
                            h)).
(* hint proof tokens: 28 *)
Proof.
    intros.
    rewrite ndesc_log_padded_app, ndata_log_padded_app; auto.
  Qed.
Local Hint Resolve extend_ok_synced_hdr_helper.
Lemma nonzero_addrs_roundup : forall B (l : list (addr * B)) n,
    n > 0 ->
    nonzero_addrs (map fst l) <= (divup (length l) n) * n.
(* hint proof tokens: 36 *)
Proof.
    intros.
    eapply le_trans.
    apply nonzero_addrs_bound.
    rewrite map_length.
    apply roundup_ge; auto.
  Qed.
Lemma loglen_invalid_overflow : forall xp old new,
    LogLen xp = DescSig.items_per_val * LogDescLen xp ->
    loglen_invalid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length (padded_log old ++ new) > LogLen xp.
(* hint proof tokens: 110 *)
Proof.
    unfold loglen_invalid, ndesc_log, ndata_log; intros.
    rewrite app_length; repeat rewrite padded_log_length.
    unfold roundup; intuition.
    rewrite H.
    setoid_rewrite <- Nat.mul_comm at 2.
    apply divup_add_gt; auto.

    eapply lt_le_trans; eauto.
    apply Nat.add_le_mono.
    apply nonzero_addrs_roundup; auto.
    erewrite <- map_length.
    apply nonzero_addrs_bound.
  Qed.
Hint Rewrite Desc.array_rep_avail Data.array_rep_avail
     padded_log_length divup_mul divup_1 map_length
     ndesc_log_padded_log nonzero_addrs_padded_log using auto: extend_crash.
Hint Unfold roundup ndata_log : extend_crash.
Ltac extend_crash :=
     repeat (autorewrite with extend_crash; autounfold with extend_crash; simpl);
     setoid_rewrite <- Desc.avail_rep_merge at 3;
     [ setoid_rewrite <- Data.avail_rep_merge at 3 | ];
     [ cancel
     | apply helper_loglen_data_valid_extend_entry_valid; auto
     | apply helper_loglen_desc_valid_extend; auto ].
Lemma log_nonzero_padded_log : forall l,
    log_nonzero (padded_log l) = log_nonzero l.
(* hint proof tokens: 50 *)
Proof.
    unfold padded_log, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    rewrite log_nonzero_app.
    rewrite log_nonzero_repeat_0, app_nil_r; auto.
  Qed.
Lemma log_nonzero_padded_app : forall l new,
    Forall entry_valid new ->
    log_nonzero l ++ new = log_nonzero (padded_log l ++ padded_log new).
Proof.
(* skipped proof tokens: 41 *)
Admitted.
Lemma log_nonzero_app_padded : forall l new,
    Forall entry_valid new ->
    log_nonzero l ++ new = log_nonzero (l ++ padded_log new).
(* hint proof tokens: 38 *)
Proof.
    intros.
    rewrite log_nonzero_app, log_nonzero_padded_log.
    f_equal.
    rewrite entry_valid_vals_nonzero; auto.
  Qed.
Definition extend xp log cs :=
    
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(_, (ndesc, ndata), (h_addr, h_valu)) := nr in
    let '(nndesc, nndata) := ((ndesc_log log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
      h_addr <- hash_list h_addr (DescDefs.nopad_ipack (map ent_addr log));
      h_valu <- hash_list h_valu (vals_nonzero log);
      cs <- Desc.write_aligned xp ndesc (map ent_addr log) cs;
      cs <- Data.write_aligned xp ndata (map ent_valu log) cs;
      cs <- Hdr.write xp ((ndesc, ndata),
                          (ndesc + nndesc, ndata + nndata),
                          (h_addr, h_valu)) cs;
      
      cs <- BUFCACHE.begin_sync cs;
      cs <- Desc.sync_aligned xp ndesc nndesc cs;
      cs <- Data.sync_aligned xp ndata nndata cs;
      cs <- Hdr.sync xp cs;
      cs <- BUFCACHE.end_sync cs;
      
      Ret ^(cs, true)
    } else {
      Ret ^(cs, false)
    }.
Lemma rep_hashmap_subset : forall xp hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st hm
        =p=> rep xp st hm'.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma would_recover'_hashmap_subset : forall xp l hm hm',
    (exists l, hashmap_subset l hm hm') ->
    would_recover' xp l hm
    =p=> would_recover' xp l hm'.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Definition extend_ok : forall xp new cs,
    {< F old d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced old) hm)%pred d ]] *
          [[ Forall entry_valid new /\ sync_invariant F ]]
    POST:hm' RET: ^(cs, r) exists d',
          BUFCACHE.rep cs d' * (
          [[ r = true /\
             (F * rep xp (Synced ((padded_log old) ++ new)) hm')%pred d' ]] \/
          [[ r = false /\ length ((padded_log old) ++ new) > LogLen xp /\
             (F * rep xp (Synced old) hm')%pred d' ]])
    XCRASH:hm_crash exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * rep xp (Synced old) hm_crash)%pred d' ]] \/
          [[ (F * rep xp (Extended old new) hm_crash)%pred d' ]])
    >} extend xp new cs.
(* hint proof tokens: 823 *)
Proof.
    unfold extend.
    step.
    step.

    
    - 
      rewrite <- DescDefs.ipack_nopad_ipack_eq.
      step.
      unfold checksums_match in *; intuition.
      solve_hash_list_rep.
      step.
      unfold checksums_match in *; intuition.
      solve_hash_list_rep.

      safestep.
      rewrite Desc.avail_rep_split. cancel.
      autorewrite with lists; apply helper_loglen_desc_valid_extend; auto.

      safestep.
      rewrite Data.avail_rep_split. cancel.
      autorewrite with lists.
      rewrite divup_1; rewrite <- entry_valid_ndata by auto.
      apply helper_loglen_data_valid_extend; auto.

      
      safestep.
      denote Hdr.rep as Hx; unfold Hdr.rep in Hx.
      destruct_lift Hx.
      unfold Hdr.hdr_goodSize in *; intuition.
      eapply loglen_valid_goodSize_l; eauto.
      eapply loglen_valid_goodSize_r; eauto.

      
      step.
      eauto 10.
      prestep. norm. cancel. intuition simpl.
      instantiate ( 1 := map ent_addr (padded_log new) ).
      rewrite desc_padding_unsync_piff.
      pred_apply; cancel.
      rewrite map_length, padded_log_length; auto.
      apply padded_desc_valid.
      apply loglen_valid_desc_valid; auto.
      eauto 10.

      safestep.
      autorewrite with lists.
      rewrite entry_valid_ndata, Nat.mul_1_r; auto.
      eauto 10.

      
      safestep.
      eauto 10.
      step.

      
      safestep.
      or_l; cancel.
      cancel_by extend_ok_helper; auto.
      solve_checksums.

      
      
      cancel.
      repeat xcrash_rewrite.
      xform_norm. cancel. xform_normr. cancel.
      or_r. cancel.
      extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.


      
      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_l; cancel. extend_crash.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_l; cancel.
      rewrite Desc.avail_rep_merge. cancel.
      rewrite map_length.
      apply helper_loglen_desc_valid_extend; auto.
      solve_checksums.

      xcrash.
      or_l; cancel.
      solve_checksums.

      xcrash.
      or_l; cancel.
      solve_checksums.

    
    - safestep.
      or_r; cancel.
      apply loglen_invalid_overflow; auto.
      solve_checksums.

    
    - xcrash.
      or_l; cancel.
      solve_checksums.
  Qed.
Hint Extern 1 ({{_}} Bind (avail _ _) _) => apply avail_ok : prog.
Hint Extern 1 ({{_}} Bind (read _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (trunc _ _) _) => apply trunc_ok : prog.
Hint Extern 1 ({{_}} Bind (extend _ _ _) _) => apply extend_ok : prog.
Theorem entry_valid_dec : forall ent,
    {entry_valid ent} + {~ entry_valid ent}.
Proof.
    unfold entry_valid, addr_valid, goodSize; intuition.
    destruct (addr_eq_dec (fst ent) 0); destruct (lt_dec (fst ent) (pow2 addrlen)).
    right; tauto.
    right; tauto.
    left; tauto.
    right; tauto.
  Qed.
Theorem rep_synced_length_ok : forall F xp l d hm,
    (F * rep xp (Synced l) hm)%pred d -> length l <= LogLen xp.
(* hint proof tokens: 72 *)
Proof.
    unfold rep, rep_inner, rep_contents, xparams_ok.
    unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
    intros; destruct_lifts.
    rewrite map_length, Nat.sub_0_r in H17.
    rewrite H5, Nat.mul_comm; auto.
  Qed.
Lemma xform_rep_synced : forall xp l hm,
    crash_xform (rep xp (Synced l) hm) =p=> rep xp (Synced l) hm.
Proof.
(* skipped proof tokens: 96 *)
Admitted.
Lemma xform_rep_truncated : forall xp l hm,
    crash_xform (rep xp (Truncated l) hm) =p=>
      rep xp (Synced l) hm \/ rep xp (Synced nil) hm.
Proof.
(* skipped proof tokens: 101 *)
Admitted.
Lemma xform_rep_extendedcrashed : forall xp old new hm,
    crash_xform (rep xp (ExtendedCrashed old new) hm) =p=> rep xp (ExtendedCrashed old new) hm.
Proof.
(* skipped proof tokens: 109 *)
Admitted.
Theorem rep_extended_facts' : forall xp d old new hm,
    (rep xp (Extended old new) hm)%pred d ->
    Forall entry_valid new /\
    LogLen xp >= ndata_log old + ndata_log new /\ LogDescLen xp >= ndesc_log old + ndesc_log new.
(* hint proof tokens: 70 *)
Proof.
    unfold rep, rep_inner, rep_contents, xparams_ok.
    unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
    intros; destruct_lifts.
    intuition.
    unfold loglen_valid in *; intuition.
    unfold loglen_valid in *; intuition.
  Qed.
Theorem rep_extended_facts : forall xp old new hm,
    rep xp (Extended old new) hm =p=>
    (rep xp (Extended old new) hm *
      [[ LogLen xp >= ndata_log old + ndata_log new ]] *
      [[ LogDescLen xp >= ndesc_log old + ndesc_log new ]] *
      [[ Forall entry_valid new ]] )%pred.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
Lemma helper_sep_star_distr: forall AT AEQ V (a b c d : @pred AT AEQ V),
    a * b * c * d =p=> (c * a) * (d * b).
(* hint proof tokens: 12 *)
Proof.
    intros; cancel.
  Qed.
Lemma helper_add_sub_add : forall a b c,
    b >= c + a -> a + (b - (c + a)) = b - c.
(* hint proof tokens: 12 *)
Proof.
    intros; lia.
  Qed.
Lemma xform_rep_extended_helper : forall xp old new,
    xparams_ok xp
    -> LogLen xp >= ndata_log old + ndata_log new
    -> LogDescLen xp >= ndesc_log old + ndesc_log new
    -> Forall addr_valid old
    -> Forall entry_valid new
    -> crash_xform (Data.avail_rep xp (ndata_log old) (LogLen xp - ndata_log old)) *
        crash_xform (Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old)) *
        crash_xform (Data.array_rep xp 0 (Data.Synced (vals_nonzero old))) *
        crash_xform (Desc.array_rep xp 0 (Desc.Synced (map ent_addr old)))
      =p=> exists synced_addr synced_valu ndesc,
        rep_contents_unmatched xp old synced_addr synced_valu *
        [[ length synced_addr = (ndesc * DescSig.items_per_val)%nat ]] *
        [[ ndesc = ndesc_log new ]] *
        [[ length synced_valu = ndata_log new ]].
(* hint proof tokens: 316 *)
Proof.
    intros.
    rewrite Data.avail_rep_split with (n1:=ndata_log new).
    rewrite Desc.avail_rep_split with (n1:=ndesc_log new).
    xform.
    erewrite Data.xform_avail_rep_array_rep, Desc.xform_avail_rep_array_rep.
    norml. unfold stars; simpl.
    norm.
    unfold stars; simpl.
    cancel.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    unfold rep_contents_unmatched.
    rewrite vals_nonzero_padded_log, desc_padding_synced_piff.
    cancel.
    replace (ndesc_list _) with (ndesc_log new).
    replace (length l) with (ndata_log new).
    cancel.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try lia.
    unfold ndesc_list.
    substl (length l0).
    unfold ndesc_log.
    rewrite divup_divup; auto.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try lia.
    intuition; auto.
    all: unfold DescSig.RALen, DataSig.RALen, xparams_ok in *;
          try lia; auto; intuition.

    apply mult_le_compat_r; lia.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try lia.
  Qed.
Lemma sep_star_pimpl_trans : forall AT AEQ V (F p q r: @pred AT AEQ V),
    p =p=> q ->
    F * q =p=> r ->
    F * p =p=> r.
(* hint proof tokens: 15 *)
Proof.
    intros.
    cancel; auto.
  Qed.
Lemma xform_rep_extended' : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       rep xp (Synced old) hm \/
       rep xp (ExtendedCrashed old new) hm.
Proof.
(* skipped proof tokens: 150 *)
Admitted.
Lemma rep_synced_app_pimpl : forall xp old new hm,
    rep xp (Synced (padded_log old ++ new)) hm =p=>
    rep xp (Synced (padded_log old ++ padded_log new)) hm.
Proof.
(* skipped proof tokens: 291 *)
Admitted.
Lemma rep_extendedcrashed_pimpl : forall xp old new hm,
    rep xp (ExtendedCrashed old new) hm
    =p=> rep xp (Synced ((padded_log old) ++ new)) hm \/
          rep xp (Rollback old) hm.
Proof.
(* skipped proof tokens: 471 *)
Admitted.
Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       rep xp (Synced old) hm \/
       rep xp (Synced (padded_log old ++ new)) hm \/
       rep xp (Rollback old) hm.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma xform_rep_rollback : forall xp old hm,
    crash_xform (rep xp (Rollback old) hm) =p=>
      rep xp (Rollback old) hm.
Proof.
(* skipped proof tokens: 93 *)
Admitted.
Lemma recover_desc_avail_helper : forall T xp old (new : list T) ndata,
    loglen_valid xp (ndesc_log old + ndesc_list new) ndata ->
    (Desc.avail_rep xp (ndesc_log old) (ndesc_list new)
     * Desc.avail_rep xp (ndesc_log old + ndesc_list new)
         (LogDescLen xp - ndesc_log old - ndesc_list new))
    =p=> Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old).
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Lemma recover_data_avail_helper : forall T xp old (new : list T) ndesc,
    loglen_valid xp ndesc (ndata_log old + length new) ->
    Data.avail_rep xp (ndata_log old)
          (divup (length new) DataSig.items_per_val)
    * Data.avail_rep xp (ndata_log old + length new)
        (LogLen xp - ndata_log old - length new)
    =p=> Data.avail_rep xp (nonzero_addrs (map fst old))
           (LogLen xp - nonzero_addrs (map fst old)).
(* hint proof tokens: 68 *)
Proof.
    intros.
    replace DataSig.items_per_val with 1 by (cbv; auto); try lia.
    rewrite divup_1, Data.avail_rep_merge;
    eauto.
    rewrite le_plus_minus_r;
    auto.
    unfold loglen_valid in *;
    lia.
  Qed.
Lemma xform_rep_rollbackunsync : forall xp l hm,
    crash_xform (rep xp (RollbackUnsync l) hm) =p=>
      rep xp (Rollback l) hm \/
      rep xp (Synced l) hm.
Proof.
(* skipped proof tokens: 219 *)
Admitted.
Lemma xform_would_recover' : forall xp l hm,
    crash_xform (would_recover' xp l hm) =p=>
      rep xp (Synced l) hm \/
      rep xp (Rollback l) hm.
(* hint proof tokens: 51 *)
Proof.
    unfold would_recover'.
    intros.
    xform.
    cancel; (rewrite xform_rep_synced ||
              rewrite xform_rep_rollback ||
              rewrite xform_rep_rollbackunsync); cancel.
  Qed.
Lemma weq2 : forall sz (x y : word sz) (a b : word sz),
    {x = y /\ a = b} + {(x = y /\ a <> b) \/
                        (x <> y /\ a = b) \/
                        (x <> y /\ a <> b)}.
Proof.
    intros.
    destruct (weq x y); destruct (weq a b); intuition.
  Qed.
Definition recover xp cs :=
    let^ (cs, header) <- Hdr.read xp cs;
    let '((prev_ndesc, prev_ndata),
          (ndesc, ndata),
          (addr_checksum, valu_checksum)) := header in
    let^ (cs, wal) <- Desc.read_all xp ndesc cs;
    let^ (cs, vl) <- Data.read_all xp ndata cs;
    default_hash <- Hash default_valu;
    h_addr <- hash_list default_hash (DescDefs.ipack wal);
    h_valu <- hash_list default_hash vl;
    If (weq2 addr_checksum h_addr valu_checksum h_valu) {
      Ret cs
    } else {
      Debug "hash mismatch" 0;;
      let^ (cs, wal) <- Desc.read_all xp prev_ndesc cs;
      let^ (cs, vl) <- Data.read_all xp prev_ndata cs;
      addr_checksum <- hash_list default_hash (DescDefs.ipack wal);
      valu_checksum <- hash_list default_hash vl;
      cs <- Hdr.write xp ((prev_ndesc, prev_ndata),
                          (prev_ndesc, prev_ndata),
                          (addr_checksum, valu_checksum)) cs;
      cs <- Hdr.sync_now xp cs;
      Ret cs
    }.
Lemma recover_read_ok_helper : forall xp old new,
     Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old ++ new))) =p=>
      Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old ++ padded_log new))).
(* hint proof tokens: 81 *)
Proof.
    intros.
    repeat rewrite map_app.
    rewrite Desc.array_rep_synced_app_rev.
    rewrite <- Desc.array_rep_synced_app.
    cancel.
    rewrite desc_padding_synced_piff.
    cancel.
    rewrite map_length, padded_log_length. unfold roundup; eauto.
    rewrite map_length, padded_log_length. unfold roundup; eauto.
  Qed.
Lemma recover_ok_addr_helper : forall xp old new,
    Desc.array_rep xp 0
        (Desc.Synced
          (map ent_addr (padded_log old) ++ map ent_addr (padded_log new))) =p=>
    Desc.array_rep xp 0
      (Desc.Synced (map ent_addr (padded_log old ++ new))).
(* hint proof tokens: 86 *)
Proof.
    intros.
    rewrite map_app.
    eapply pimpl_trans; [ | eapply Desc.array_rep_synced_app ].
    rewrite Desc.array_rep_synced_app_rev.
    cancel.
    apply desc_padding_synced_piff.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
  Qed.
Definition recover_ok_Synced : forall xp cs,
    {< F l d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET:cs'
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced l) hm')%pred d ]]
    CRASH:hm_crash exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} recover xp cs.
Proof.
(* skipped proof tokens: 313 *)
Admitted.
Definition recover_ok_Rollback : forall xp cs,
    {< F old d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * rep xp (Rollback old) hm)%pred d ]] *
          [[ sync_invariant F ]]
    POST:hm' RET:cs' exists d',
          BUFCACHE.rep cs' d' *
          [[ (F * rep xp (Synced old) hm')%pred d' ]]
    XCRASH:hm_crash exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * rep xp (Rollback old) hm_crash)%pred d' ]] \/
          [[ (F * rep xp (RollbackUnsync old) hm_crash)%pred d' ]])
    >} recover xp cs.
Proof.
(* skipped proof tokens: 1768 *)
Admitted.
Definition recover_ok : forall xp cs,
    {< F st l,
    PRE:hm
      exists d, BUFCACHE.rep cs d *
          [[ (F * rep xp st hm)%pred d ]] *
          [[ st = Synced l \/ st = Rollback l ]] *
          [[ sync_invariant F ]]
    POST:hm' RET:cs' exists d',
          BUFCACHE.rep cs' d' *
          [[ (F * rep xp (Synced l) hm')%pred d' ]]
    XCRASH:hm'
          would_recover xp F l hm'
    >} recover xp cs.
(* hint proof tokens: 204 *)
Proof.
    unfold would_recover, would_recover'; intros.
    eapply pimpl_ok2; monad_simpl; try eapply nop_ok.
    intros. norm'l. unfold stars; cbn.
    intuition; subst.

    
    - cancel.
      eapply pimpl_ok2; monad_simpl; try apply recover_ok_Synced.
      cancel.
      eassign l.
      cancel.
      hoare.
      norm'l. xcrash.
      xcrash.
      xcrash.
      or_l; cancel.

    
    - cancel.
      eapply pimpl_ok2; monad_simpl; try apply recover_ok_Rollback.
      intros; norm. cancel. intuition simpl. eauto. auto.
      step.
      cancel.
      xcrash.
      or_r; or_l; cancel.
      or_r; or_r; cancel.
      xcrash.
      or_r; or_l; cancel.
  Qed.
Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.
End PaddedLog.
Module DLog.
Definition entry := (addr * valu)%type.
Definition contents := list entry.
Inductive state :=
  
  | Synced (navail : nat) (l: contents)
  
  | Truncated  (old: contents)
  
  | ExtendedUnsync (old: contents)
  
  | Extended  (old: contents) (new: contents)
  
  | Rollback (l: contents)
  
  | Recovering (l: contents).
Definition rep_common l padded : rawpred :=
      ([[ l = PaddedLog.log_nonzero padded /\
         length padded = roundup (length padded) PaddedLog.DescSig.items_per_val ]])%pred.
Definition rep xp st hm :=
    (match st with
    | Synced navail l =>
          exists padded, rep_common l padded *
          [[ navail = (LogLen xp) - (length padded) ]] *
          PaddedLog.rep xp (PaddedLog.Synced padded) hm
    | Truncated l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.Truncated padded) hm
    | ExtendedUnsync l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.Synced padded) hm
    | Extended l new =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.Extended padded new) hm
    | Rollback l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.Rollback padded) hm
    | Recovering l =>
          exists padded, rep_common l padded *
          PaddedLog.would_recover' xp padded hm
    end)%pred.
Theorem sync_invariant_rep : forall xp st hm,
    sync_invariant (rep xp st hm).
(* hint proof tokens: 22 *)
Proof.
    unfold rep, rep_common; destruct st; intros; eauto.
  Qed.
Hint Resolve sync_invariant_rep.
Local Hint Unfold rep rep_common : hoare_unfold.
Section UnifyProof.
Hint Extern 0 (okToUnify (PaddedLog.rep _ _) (PaddedLog.rep _ _)) => constructor : okToUnify.
Definition read xp cs :=
    r <- PaddedLog.read xp cs;
    Ret r.
Definition read_ok : forall xp cs,
    {< F l d nr,
    PRE:hm    BUFCACHE.rep cs d * 
              [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:hm'   RET: ^(cs, r)
              BUFCACHE.rep cs d *
              [[ r = l /\ (F * rep xp (Synced nr l) hm')%pred d ]]
    CRASH:hm' exists cs',
              BUFCACHE.rep cs' d *
              [[ (F * rep xp (Synced nr l) hm')%pred d ]]
    >} read xp cs.
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Definition init xp cs :=
    cs <- PaddedLog.init xp cs;
    Ret cs.
Definition trunc xp cs :=
    cs <- PaddedLog.trunc xp cs;
    Ret cs.
Definition trunc_ok : forall xp cs,
    {< F l d nr,
    PRE:hm    BUFCACHE.rep cs d *
              [[ (F * rep xp (Synced nr l) hm)%pred d ]] * 
              [[  sync_invariant F ]]
    POST:hm' RET: cs exists d',
              BUFCACHE.rep cs d' *
              [[ (F * rep xp (Synced (LogLen xp) nil) hm')%pred d' ]]
    XCRASH:hm' exists cs d',
              BUFCACHE.rep cs d' * (
              [[ (F * rep xp (Synced nr l) hm')%pred d' ]] \/
              [[ (F * rep xp (Truncated l) hm')%pred d' ]])
    >} trunc xp cs.
(* hint proof tokens: 59 *)
Proof.
    unfold trunc.
    safestep.
    eassign F; cancel.
    eauto.
    step.
    unfold roundup; rewrite divup_0; lia.

    
    xcrash.
    or_l; cancel.
    or_r; cancel.
  Qed.
Definition avail xp cs :=
    r <- PaddedLog.avail xp cs;
    Ret r.
Definition avail_ok : forall xp cs,
    {< F l d nr,
    PRE:hm BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]] *
          [[ r = nr ]]
    CRASH:hm' exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]]
    >} avail xp cs.
(* hint proof tokens: 20 *)
Proof.
    unfold avail.
    step.
    step.
    cancel.
  Qed.
End UnifyProof.
Definition init_ok : forall xp cs,
    {< F l d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * PaddedLog.DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: cs  exists d' nr,
          BUFCACHE.rep cs d' *
          [[ (F * rep xp (Synced nr nil) hm')%pred d' ]]
    XCRASH:hm_crash any
    >} init xp cs.
(* hint proof tokens: 127 *)
Proof.
    unfold init, rep.
    step.
    unfold PaddedLog.xparams_ok, PaddedLog.DescSig.xparams_ok, PaddedLog.DataSig.xparams_ok; intuition.
    substl (LogDescriptor xp); unfold PaddedLog.DescSig.RALen.
    eapply goodSize_trans; [ | eauto ]; lia.
    substl (LogData xp); substl (LogDescriptor xp); unfold PaddedLog.DataSig.RALen.
    eapply goodSize_trans; [ | eauto ]; lia.
    step.
    rewrite roundup_0; auto.
  Qed.
Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
Local Hint Resolve PaddedLog.DescDefs.items_per_val_gt_0.
Lemma extend_length_ok' : forall l new,
    length l = roundup (length l) PaddedLog.DescSig.items_per_val ->
    length (l ++ PaddedLog.padded_log new)
      = roundup (length (l ++ PaddedLog.padded_log new)) PaddedLog.DescSig.items_per_val.
(* hint proof tokens: 44 *)
Proof.
    intros.
    repeat rewrite app_length.
    repeat rewrite PaddedLog.padded_log_length.
    rewrite H.
    rewrite roundup_roundup_add, roundup_roundup; auto.
  Qed.
Lemma extend_length_ok : forall l new,
    length l = roundup (length l) PaddedLog.DescSig.items_per_val ->
    length (PaddedLog.padded_log l ++ PaddedLog.padded_log new)
      = roundup (length (PaddedLog.padded_log l ++ PaddedLog.padded_log new)) PaddedLog.DescSig.items_per_val.
(* hint proof tokens: 34 *)
Proof.
    intros.
    apply extend_length_ok'.
    rewrite PaddedLog.padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.
Lemma helper_extend_length_ok : forall xp padded new F d hm,
    length padded = roundup (length padded) PaddedLog.DescSig.items_per_val
    -> length (PaddedLog.padded_log padded ++ new) > LogLen xp
    -> (F * PaddedLog.rep xp (PaddedLog.Synced padded) hm)%pred d
    -> length new > LogLen xp - length padded.
Proof.
(* original proof tokens: 59 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve extend_length_ok helper_extend_length_ok PaddedLog.log_nonzero_padded_app.
Definition extend xp new cs :=
    r <- PaddedLog.extend xp new cs;
    Ret r.
Definition rounded n := roundup n PaddedLog.DescSig.items_per_val.
Definition entries_valid l := Forall PaddedLog.entry_valid l.
Lemma extend_navail_ok : forall xp padded new, 
    length padded = roundup (length padded) PaddedLog.DescSig.items_per_val ->
    LogLen xp - length padded - rounded (length new)
    = LogLen xp - length (PaddedLog.padded_log padded ++ PaddedLog.padded_log new).
Proof.
(* skipped proof tokens: 61 *)
Admitted.
Local Hint Resolve extend_navail_ok PaddedLog.rep_synced_app_pimpl.
Definition extend_ok : forall xp new cs,
    {< F old d nr,
    PRE:hm    BUFCACHE.rep cs d *
              [[ (F * rep xp (Synced nr old) hm)%pred d ]] *
              [[ entries_valid new /\ sync_invariant F ]]
    POST:hm' RET: ^(cs, r) exists d',
              BUFCACHE.rep cs d' * (
              [[ r = true /\
                (F * rep xp (Synced (nr - (rounded (length new))) (old ++ new)) hm')%pred d' ]] \/
              [[ r = false /\ length new > nr /\
                (F * rep xp (Synced nr old) hm')%pred d' ]])
    XCRASH:hm' exists cs' d',
              BUFCACHE.rep cs' d' * (
              [[ (F * rep xp (Synced nr old) hm')%pred d' ]] \/
              [[ (F * rep xp (Extended old new) hm')%pred d' ]])
    >} extend xp new cs.
(* hint proof tokens: 94 *)
Proof.
    unfold extend.

    prestep.
    safecancel.
    eassign F; cancel. auto.
    step.

    or_l. norm; [ cancel | intuition; pred_apply; norm ].
    eassign (PaddedLog.padded_log dummy ++ PaddedLog.padded_log new).
    cancel; auto.
    intuition.

    xcrash.
    or_l; cancel.
    or_r; cancel.
  Qed.
Hint Extern 1 ({{_}} Bind (avail _ _) _) => apply avail_ok : prog.
Hint Extern 1 ({{_}} Bind (read _ _) _) => apply read_ok : prog.
Hint Extern 1 ({{_}} Bind (trunc _ _) _) => apply trunc_ok : prog.
Hint Extern 1 ({{_}} Bind (extend _ _ _) _) => apply extend_ok : prog.
Definition recover xp cs :=
    cs <- PaddedLog.recover xp cs;
    Ret cs.
Definition recover_ok : forall xp cs,
    {< F nr l,
    PRE:hm
      exists d, BUFCACHE.rep cs d * (
          [[ (F * rep xp (Synced nr l) hm)%pred d ]] \/
          [[ (F * rep xp (Rollback l) hm)%pred d ]]) *
          [[ sync_invariant F ]]
    POST:hm' RET:cs' exists d',
          BUFCACHE.rep cs' d' *
          [[ (F * exists nr', rep xp (Synced nr' l) hm')%pred d' ]]
    XCRASH:hm' exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * rep xp (Recovering l) hm')%pred d' ]])
    >} recover xp cs.
(* hint proof tokens: 117 *)
Proof.
    unfold recover.
    prestep. norm. cancel.
    intuition simpl.
    pred_apply.
    eassign F; cancel.
    eauto.

    step.
    norm'l.
    unfold PaddedLog.would_recover in *.
    xcrash.
    xform.
    cancel.

    eassign (PaddedLog.Rollback dummy).
    intuition simpl.
    pred_apply; cancel.
    auto.

    step.
    norm'l.
    unfold PaddedLog.would_recover in *.
    xcrash.
  Qed.
Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.
Lemma xform_rep_synced : forall xp na l hm,
    crash_xform (rep xp (Synced na l) hm) =p=> rep xp (Synced na l) hm.
Proof.
(* skipped proof tokens: 38 *)
Admitted.
Lemma xform_rep_truncated : forall xp l hm,
    crash_xform (rep xp (Truncated l) hm) =p=> exists na,
      rep xp (Synced na l) hm \/ rep xp (Synced (LogLen xp) nil) hm.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma xform_rep_extended_unsync : forall xp l hm,
    crash_xform (rep xp (ExtendedUnsync l) hm) =p=> exists na, rep xp (Synced na l) hm.
(* hint proof tokens: 38 *)
Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    apply PaddedLog.xform_rep_synced.
    all: auto.
  Qed.
Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       (exists na, rep xp (Synced na old) hm) \/
       (exists na, rep xp (Synced na (old ++ new)) hm) \/
       (rep xp (Rollback old) hm).
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Lemma xform_rep_rollback : forall xp l hm,
    crash_xform (rep xp (Rollback l) hm) =p=>
      rep xp (Rollback l) hm.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma xform_rep_recovering : forall xp l hm,
    crash_xform (rep xp (Recovering l) hm) =p=>
      rep xp (Rollback l) hm \/
        exists na, rep xp (Synced na l) hm.
(* hint proof tokens: 35 *)
Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite PaddedLog.xform_would_recover'.
    cancel.
  Qed.
Lemma rep_synced_pimpl : forall xp nr l hm,
    rep xp (Synced nr l) hm =p=>
    rep xp (Recovering l) hm.
(* hint proof tokens: 37 *)
Proof.
    unfold rep, PaddedLog.would_recover'; intros.
    cancel.
    eassign padded; cancel.
    or_l; cancel.
  Qed.
Lemma rep_rollback_pimpl : forall xp l hm,
    rep xp (Rollback l) hm =p=>
      rep xp (Recovering l) hm.
(* hint proof tokens: 40 *)
Proof.
    unfold rep, PaddedLog.would_recover'; intros.
    cancel.
    eassign padded; cancel.
    or_r; or_l; cancel.
  Qed.
Lemma rep_hashmap_subset : forall xp hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st hm
        =p=> rep xp st hm'.
Proof.
(* skipped proof tokens: 59 *)
Admitted.
End DLog.
