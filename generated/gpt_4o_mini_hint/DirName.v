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
Require List.
Import PeanoNat.
Set Implicit Arguments.
Definition ifw {len} (b : bool) (bitpos : word len) : word len :=
  if b then wbit _ bitpos else $0.
Definition ascii2byte (a : ascii) : word 8 :=
  match a with
  | Ascii a1 a2 a3 a4 a5 a6 a7 a8 =>
    ifw a1 $0 ^|
    ifw a2 $1 ^|
    ifw a3 $2 ^|
    ifw a4 $3 ^|
    ifw a5 $4 ^|
    ifw a6 $5 ^|
    ifw a7 $6 ^|
    ifw a8 $7
  end.
Definition wbitset {len} (bitpos : word len) (w : word len) : bool :=
  if weq (wand w (wbit _ bitpos)) $0 then false else true.
Definition byte2ascii (b : word 8) : ascii :=
  Ascii (wbitset $0 b)
        (wbitset $1 b)
        (wbitset $2 b)
        (wbitset $3 b)
        (wbitset $4 b)
        (wbitset $5 b)
        (wbitset $6 b)
        (wbitset $7 b).
Theorem ascii2byte2ascii : forall a,
  byte2ascii (ascii2byte a) = a.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Theorem byte2ascii2byte : forall b,
  ascii2byte (byte2ascii b) = b.
(* hint proof tokens: 50 *)
Proof.
  intros.
  shatter_word b.
  destruct x; destruct x0; destruct x1; destruct x2;
  destruct x3; destruct x4; destruct x5; destruct x6; reflexivity.
Qed.
Fact ascii2byte_zero : ascii2byte zero = $0.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 18 *)

unfold ascii2byte, zero.
reflexivity.
Qed.

Fixpoint name2padstring (nbytes : nat) (name : word (nbytes * 8)) : string.
destruct nbytes.
refine EmptyString.
refine (String (byte2ascii (@split1 8 (nbytes * 8) name))
                 (name2padstring nbytes (@split2 8 (nbytes * 8) name))).
Defined.
Fixpoint padstring2name (nbytes : nat) (s : string) : word (nbytes * 8).
destruct nbytes.
refine ($0).
destruct s.
refine ($0).
refine (combine (ascii2byte a) (padstring2name nbytes s)).
Defined.
Opaque ascii2byte byte2ascii split1 split2.
Theorem name2padstring2name : forall nbytes (name : word (nbytes * 8)),
  padstring2name nbytes (name2padstring nbytes name) = name.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Theorem padstring2name2padstring : forall nbytes (s : string),
  length s = nbytes -> name2padstring nbytes (padstring2name nbytes s) = s.
(* hint proof tokens: 75 *)
Proof.
  induction nbytes; simpl; intros.
  destruct s; simpl in *; congruence.
  destruct s; simpl in *; try congruence.
  rewrite split1_combine.
  rewrite split2_combine.
  rewrite IHnbytes by congruence.
  rewrite ascii2byte2ascii.
  reflexivity.
Qed.
Theorem name2padstring_length : forall nbytes name,
  length (name2padstring nbytes name) = nbytes.
(* hint proof tokens: 15 *)
Proof.
  induction nbytes; simpl; eauto.
Qed.
Fixpoint string_pad nbytes (s : string) :=
  match nbytes with
  | O => EmptyString
  | S nbytes' =>
    match s with
    | EmptyString => String zero (string_pad nbytes' EmptyString)
    | String a s' => String a (string_pad nbytes' s')
    end
  end.
Fixpoint string_unpad (s : string) :=
  match s with
  | EmptyString => EmptyString
  | String a s' =>
    if ascii_dec a zero then EmptyString else String a (string_unpad s')
  end.
Theorem string_pad_length : forall nbytes s,
  length (string_pad nbytes s) = nbytes.
(* hint proof tokens: 25 *)
Proof.
  induction nbytes; simpl.
  reflexivity.
  destruct s; simpl; eauto.
Qed.
Inductive nozero : string -> Prop :=
  | NoZeroEmpty : nozero EmptyString
  | NoZeroCons : forall a s, a <> zero -> nozero s -> nozero (String a s).
Theorem string_pad_unpad : forall nbytes s,
  length s <= nbytes -> nozero s -> string_unpad (string_pad nbytes s) = s.
(* hint proof tokens: 72 *)
Proof.
  induction nbytes; simpl; intros.
  destruct s; simpl in *; try congruence; lia.
  destruct s; simpl in *; try congruence.
  inversion H0.
  destruct (ascii_dec a zero); try congruence.
  rewrite IHnbytes; eauto.
  lia.
Qed.
Inductive zerostring : string -> Prop :=
  | ZeroEmpty : zerostring EmptyString
  | ZeroCons : forall s, zerostring s -> zerostring (String zero s).
Inductive wellformedpadstring : string -> Prop :=
  | WFSzero : forall s, zerostring s -> wellformedpadstring s
  | WFScons : forall s c, wellformedpadstring s -> c <> zero
                       -> wellformedpadstring (String c s).
Theorem pad_zero_string : forall s, 
  wellformedpadstring (String zero s)
  -> s = string_pad (length s) EmptyString.
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Theorem string_unpad_pad : forall s nbytes,
  length s = nbytes
  -> wellformedpadstring s
  -> string_pad nbytes (string_unpad s) = s.
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Definition string2name nbytes s := padstring2name nbytes (string_pad nbytes s).
Definition name2string nbytes name := string_unpad (name2padstring nbytes name).
Fixpoint string2name' (nbytes : nat) (s : string) : word (nbytes * 8).
destruct nbytes.
refine ($0).
destruct s.
refine ($0).
refine (combine (ascii2byte a) (string2name' nbytes s)).
Defined.
Theorem string2name_string2name' : forall nbytes s, string2name nbytes s = string2name' nbytes s.
Proof.
(* original proof tokens: 129 *)

(* No more tactics to try *)
Admitted.

Theorem string2name2string : forall nbytes s,
  length s <= nbytes
  -> nozero s
  -> name2string nbytes (string2name nbytes s) = s.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Theorem name2string2name : forall nbytes name,
  wellformedpadstring (name2padstring nbytes name)
  -> string2name nbytes (name2string nbytes name) = name.
(* hint proof tokens: 46 *)
Proof.
  unfold string2name, name2string.
  intros.
  rewrite string_unpad_pad; auto.
  rewrite name2padstring2name; auto.
  apply name2padstring_length.
Qed.
Lemma zerostring_pad_empty : forall n,
  zerostring (string_pad n EmptyString).
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Lemma stringpad_wellformed : forall s nbytes,
  length s <= nbytes
  -> nozero s
  -> wellformedpadstring (string_pad nbytes s).
(* hint proof tokens: 68 *)
Proof.
  induction s; destruct nbytes eqn:Hn; simpl; intros.
  repeat constructor.
  repeat constructor.
  apply zerostring_pad_empty.
  repeat constructor.
  apply WFScons.
  apply IHs.
  lia.
  inversion H0; auto.
  inversion H0; auto.
Qed.
Lemma wellformedpadstring_inv : forall c s,
  wellformedpadstring (String c s)
  -> c <> zero
  -> wellformedpadstring s.
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Lemma wellformed_nozero : forall nbytes s,
  wellformedpadstring (name2padstring nbytes s)
  -> nozero (string_unpad (name2padstring nbytes s)).
(* hint proof tokens: 83 *)
Proof.
  induction nbytes; intros.
  constructor.
  simpl.
  destruct (ascii_dec (byte2ascii (split1 8 (nbytes * 8) s)) zero) eqn:Heq.
  constructor.
  apply NoZeroCons; auto.
  apply IHnbytes.
  simpl in H.
  eapply wellformedpadstring_inv; eauto.
Qed.
Lemma string_unpad_length : forall s,
  length (string_unpad s) <= length s.
Proof.
(* original proof tokens: 26 *)
unfold string_unpad; induction s; simpl; auto.
rewrite <- Nat.le_succ_diag_r.
apply Nat.le_trans with (length (string_unpad s) + 1).
apply Nat.le_trans with (length (string_unpad s) + 1).
apply Nat.le_trans with (length (string_unpad s) + 1).
apply Nat.le_trans with (length (string_unpad s) + 1).
rewrite Nat.le_succ_diag_r.
apply Nat.le_trans with (length (string_unpad s) + 1).
apply Nat.le_trans with (length (string_unpad s) + 1).
apply Nat.le_trans with (length (string_unpad s) + 1).
apply Nat.le_trans with (length s).
apply Nat.le_trans with (length s).
(* Reached max number of model calls *)
Admitted.

Lemma name2padstring_unpad_length : forall nbytes s,
  length (string_unpad (name2padstring nbytes s)) <= nbytes.
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Module SDIR.
Definition namelen := DIR.filename_len / 8.
Definition wname := DIR.filename.
Definition sname := string.
Inductive wname_valid : wname -> Prop :=
    | WNameValid : forall w, 
        wellformedpadstring (name2padstring namelen w) -> wname_valid w.
Inductive sname_valid : sname -> Prop :=
    | SNameValid : forall s, 
        length s <= namelen -> nozero s -> sname_valid s
    .
Definition sname2wname := string2name' namelen.
Definition wname2sname := name2string namelen.
Lemma wname_valid_sname_valid : forall x,
    wname_valid x -> sname_valid (wname2sname x).
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma sname_valid_wname_valid : forall x,
    sname_valid x -> wname_valid (sname2wname x).
(* hint proof tokens: 66 *)
Proof.
    intros; inversion H.
    constructor.
    unfold sname2wname.
    rewrite <- string2name_string2name'.
    unfold string2name.
    rewrite padstring2name2padstring.
    apply stringpad_wellformed; auto.
    apply string_pad_length.
  Qed.
Theorem dirname_cond_inverse :
    cond_inverse wname2sname wname_valid sname_valid sname2wname.
(* hint proof tokens: 100 *)
Proof.
    split; [split | split ].
    apply wname_valid_sname_valid; auto.
    unfold sname2wname; rewrite <- string2name_string2name'.
    apply name2string2name.
    inversion H; auto.
    apply sname_valid_wname_valid; auto.
    inversion H.
    unfold sname2wname; rewrite <- string2name_string2name'.
    apply string2name2string; auto.
  Qed.
Theorem dirname_cond_inverse' :
    cond_inverse sname2wname sname_valid wname_valid wname2sname.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Theorem wname2sname_bijective :
    cond_bijective wname2sname wname_valid sname_valid.
(* hint proof tokens: 21 *)
Proof.
    eapply cond_inv2bij.
    apply dirname_cond_inverse.
  Qed.
Theorem sname2wname_bijective :
    cond_bijective sname2wname sname_valid wname_valid.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma wname2sname_sname2wname: forall name,
    sname_valid name ->
    wname2sname (sname2wname name) = name.
(* hint proof tokens: 43 *)
Proof.
    intros.
    destruct (dirname_cond_inverse) as [_ H'].
    cbv [cond_right_inverse cond_inverse] in *.
    edestruct H'; eauto.
  Qed.
Lemma sname2wname_wname2sname: forall name,
    wname_valid name ->
    sname2wname (wname2sname name) = name.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve dirname_cond_inverse.
Local Hint Resolve dirname_cond_inverse'.
Local Hint Resolve wname2sname_bijective.
Local Hint Resolve sname2wname_bijective.
Fixpoint is_nozero (s : string) : bool :=
    match s with
    | EmptyString => true
    | String c s => if (ascii_dec c zero) then false else (is_nozero s)
    end.
Theorem is_nozero_nozero : forall s,
    is_nozero s = true <-> nozero s.
(* hint proof tokens: 69 *)
Proof.
    induction s.
    intuition; constructor.

    simpl.
    destruct (ascii_dec a zero); split; intros.
    inversion H.
    inversion H.
    exfalso; auto.
    constructor; auto.
    apply IHs; auto.
    inversion H.
    apply IHs; auto.
  Qed.
Definition is_valid_sname s : bool :=
    andb (is_nozero s) (if (Compare_dec.le_dec (String.length s) namelen) then true else false).
Theorem is_valid_sname_valid : forall s,
    is_valid_sname s = true <-> sname_valid s.
(* hint proof tokens: 105 *)
Proof.
    unfold is_valid_sname; intros.
    rewrite Bool.andb_true_iff.

    split; intros.
    destruct H.
    constructor.
    destruct (Compare_dec.le_dec (length s) namelen); simpl; try congruence.
    apply is_nozero_nozero; auto.

    inversion H; split.
    apply is_nozero_nozero; auto.
    destruct (Compare_dec.le_dec (length s) namelen); simpl; try congruence.
  Qed.
Fixpoint is_zerostring (s : string) : bool :=
    match s with
    | EmptyString => true
    | String a s' => if (ascii_dec a zero) then (is_zerostring s') else false
    end.
Fixpoint is_valid_wname (s : string) : bool :=
    match s with
    | EmptyString => true
    | String a s =>
        if (ascii_dec a zero) then is_zerostring s
        else is_valid_wname s
    end.
Lemma is_zerostring_zerostring : forall s,
    is_zerostring s = true <-> zerostring s.
(* hint proof tokens: 78 *)
Proof.
    induction s; simpl; intros; auto.
    split; try constructor; auto.
    destruct (ascii_dec a zero); subst; simpl; split; intros.
    constructor; apply IHs; auto.
    inversion H; apply IHs; auto.
    inversion H.
    inversion H; exfalso.
    apply n; auto.
  Qed.
Lemma is_valid_wname_valid' : forall w,
    is_valid_wname(name2padstring namelen w) = true
    <-> wellformedpadstring (name2padstring namelen w).
Proof.
(* original proof tokens: 148 *)

(* No more tactics to try *)
Admitted.

Lemma is_valid_wname_valid : forall w,
    is_valid_wname (name2padstring namelen w) = true
    <-> wname_valid w.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma wname_valid_dec : forall w,
    wname_valid w \/ ~ wname_valid w.
(* hint proof tokens: 67 *)
Proof.
    intros.
    destruct (is_valid_wname (name2padstring namelen w)) eqn:Heq.
    left; apply is_valid_wname_valid; auto.
    right; intro; contradict Heq.
    apply is_valid_wname_valid in H; congruence.
  Qed.
Lemma sname_valid_dec : forall s,
    sname_valid s \/ ~ sname_valid s.
(* hint proof tokens: 60 *)
Proof.
    intros.
    destruct (is_valid_sname s) eqn:Heq.
    left; apply is_valid_sname_valid; auto.
    right; intro; contradict Heq.
    apply is_valid_sname_valid in H; congruence.
  Qed.
Local Hint Resolve wname_valid_dec.
Local Hint Resolve sname_valid_dec.
Ltac resolve_valid_preds :=
    match goal with
    | [ H: is_valid_wname _ = true |- _ ] => apply is_valid_wname_valid in H
    | [ H: is_valid_sname _ = true |- _ ] => apply is_valid_sname_valid in H
    | [ H: is_valid_wname _ = true -> False |- _ ] =>
         rewrite is_valid_wname_valid in H
    | [ H: is_valid_sname _ = true -> False |- _ ] =>
         rewrite is_valid_sname_valid in H
    end.
Definition lookup lxp ixp dnum name ms :=
    If (Bool.bool_dec (is_valid_sname name) true) {
      let^ (ms, r) <- DIR.lookup lxp ixp dnum (sname2wname name) ms;
      Ret ^(ms, r)
    } else {
      Ret ^(ms, None)
    }.
Definition unlink lxp ixp dnum name ms :=
    If (Bool.bool_dec (is_valid_sname name) true) {
      let^ (ms, ix, r) <- DIR.unlink lxp ixp dnum (sname2wname name) ms;
      Ret ^(ms, ix, r)
    } else {
      Ret ^(ms, 0, Err ENAMETOOLONG)
    }.
Definition link lxp bxp ixp dnum name inum isdir ix0 ms :=
    If (Bool.bool_dec (is_valid_sname name) true) {
      let^ (ms, ix, r) <- DIR.link lxp bxp ixp dnum (sname2wname name) inum isdir ix0 ms;
      Ret ^(ms, ix, r)
    } else {
      Ret ^(ms, 0, Err ENAMETOOLONG)
    }.
Definition readdir_trans (di : DIR.readent) :=
    (wname2sname (fst di), snd di).
Definition readdir lxp ixp dnum ms :=
    let^ (ms, r) <- DIR.readdir lxp ixp dnum ms;
    Ret ^(ms, List.map readdir_trans r).
Definition rep f (dsmap : @mem string string_dec (addr * bool)) : Prop :=
    exists dmap, DIR.rep f dmap
    /\ (forall w, indomain w dmap -> wname_valid w)
    /\ (forall s, indomain s dsmap -> sname_valid s)
    /\ mem_atrans wname2sname dmap dsmap wname_valid.
Definition rep_macro Fi Fm m bxp ixp (inum : addr) dsmap ilist frees f ms sm : @pred _ addr_eq_dec valuset :=
    (exists flist,
     [[[ m ::: Fm * BFILE.rep bxp sm ixp flist ilist frees (BFILE.MSAllocC ms) (BFILE.MSCache ms) (BFILE.MSICache ms) (BFILE.MSDBlocks ms) ]]] *
     [[[ flist ::: Fi * inum |-> f ]]] *
     [[ rep f dsmap ]])%pred.
Lemma rep_mem_eq : forall f m1 m2,
    rep f m1 -> rep f m2 -> m1 = m2.
Proof.
(* original proof tokens: 214 *)

(* No more tactics to try *)
Admitted.

Local Hint Unfold rep rep_macro DIR.rep_macro: hoare_unfold.
Notation MSLL := BFILE.MSLL.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSCache := BFILE.MSCache.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSICache := BFILE.MSICache.
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
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Definition readent := (string * (addr * bool))%type.
Definition readmatch (de: readent) : @pred _ (string_dec) _ :=
    fst de |-> snd de.
Lemma readdir_trans_addr_ok : forall l m1 m2
    (LP : listpred DIR.readmatch l m1)
    (MT  : mem_atrans wname2sname m1 m2 wname_valid)
    (OK  : forall w, indomain w m1 -> wname_valid w)
    (OK2 : forall s, indomain s m2 -> sname_valid s),
    listpred readmatch (List.map readdir_trans l) m2.
(* hint proof tokens: 178 *)
Proof.
    induction l; simpl; intros.
    eapply mem_atrans_emp; eauto.

    unfold readmatch at 1, readdir_trans at 1; simpl.
    apply mem_except_ptsto; auto.
    eapply mem_atrans_indomain; eauto.
    eapply sep_star_ptsto_indomain; eauto.
    eapply ptsto_valid; eauto.

    apply sep_star_ptsto_indomain in LP as Hx.
    eapply ptsto_mem_except in LP.
    eapply IHl; eauto.
    apply OK in Hx.
    eapply mem_atrans_mem_except; eauto.

    intros; apply OK.
    eapply indomain_mem_except_indomain; eauto.
    intros; apply OK2.
    eapply indomain_mem_except_indomain; eauto.
  Qed.
Theorem readdir_ok : forall lxp bxp ixp dnum ms,
    {< F Fm Fi m0 sm m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', r)
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms' sm *
             [[ listpred readmatch r dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSCache ms' = MSCache ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
             [[ MSDBlocks ms' = MSDBlocks ms ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} readdir lxp ixp dnum ms.
(* hint proof tokens: 34 *)
Proof.
    unfold readdir.
    safestep. eauto.
    step.
    eapply readdir_trans_addr_ok; eauto.
  Qed.
Theorem unlink_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', hint, r) exists m' dmap' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist frees f' ms' sm *
             [[ dmap' = mem_except dmap name ]] *
             [[ notindomain name dmap' ]] *
             [[ r = OK tt -> indomain name dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} unlink lxp ixp dnum name ms.
(* hint proof tokens: 152 *)
Proof.
    unfold unlink.
    hoare; resolve_valid_preds.

    subst; eexists.
    split; [ eauto | split ]; [ intros ? Hx | split; [ intros ? Hx | ] ].
    apply indomain_mem_except_indomain in Hx; auto.
    apply indomain_mem_except_indomain in Hx; auto.
    eapply mem_ainv_mem_except; eauto.
    apply mem_except_notindomain.
    eapply mem_atrans_inv_indomain; eauto.

    rewrite <- notindomain_mem_eq.
    subst; eexists.
    apply notindomain_not_indomain; eauto.
    apply notindomain_not_indomain; eauto.
  Qed.
Lemma link_dir_rep_pimpl_notindomain: forall f dsmap dmap (name : string),
    is_valid_sname name = true ->
    notindomain name dsmap ->
    @mem_atrans _ _ _ _ string_dec wname2sname dmap dsmap wname_valid ->
    DIR.rep f dmap ->
    DIR.rep f =p=> notindomain (sname2wname name).
(* hint proof tokens: 94 *)
Proof.
    intros. intros m H'.
    replace m with dmap in * by eauto using DIR.rep_mem_eq.
    rewrite is_valid_sname_valid in *.
    eapply sname_valid_wname_valid in H as ?.
    eapply mem_atrans_inv_notindomain; eauto.
    eauto using mem_atrans_cond_inv.
  rewrite wname2sname_sname2wname; auto.
  Qed.
Theorem link_ok : forall lxp bxp ixp dnum name inum isdir ix0 ms,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm *
             [[ notindomain name dmap ]] *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:hm' RET:^(ms', ix0', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] *
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm')
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
    >} link lxp bxp ixp dnum name inum isdir ix0 ms.
Proof.
(* original proof tokens: 174 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (lookup _ _ _ _ _) _) => apply lookup_ok : prog.
Hint Extern 1 ({{_}} Bind (unlink _ _ _ _ _) _) => apply unlink_ok : prog.
Hint Extern 1 ({{_}} Bind (link _ _ _ _ _ _ _ _ _) _) => apply link_ok : prog.
Hint Extern 1 ({{_}} Bind (readdir _ _ _ _) _) => apply readdir_ok : prog.
Hint Extern 0 (okToUnify (rep ?f _) (rep ?f _)) => constructor : okToUnify.
Theorem bfile0_empty : rep BFILE.bfile0 empty_mem.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Theorem rep_no_0_inum: forall f m, rep f m ->
    forall name isdir, m name = Some (0, isdir) -> False.
(* hint proof tokens: 94 *)
Proof.
    unfold rep. intros. repeat deex.
    unfold indomain in *.
    assert (sname_valid name) by eauto.
    erewrite <- wname2sname_sname2wname with (name := name) in H0 by eauto.
    rewrite <- H4 in *.
    eauto using DIR.rep_no_0_inum.
    eauto using sname_valid_wname_valid.
  Qed.
Theorem crash_eq : forall f f' m1 m2,
    BFILE.file_crash f f' ->
    rep f m1 ->
    rep f' m2 ->
    m1 = m2.
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Theorem crash_rep : forall f f' m,
    BFILE.file_crash f f' ->
    rep f m ->
    rep f' m.
(* hint proof tokens: 37 *)
Proof.
    unfold rep; intros.
    repeat deex.
    eexists; intuition eauto.
    eapply DIR.crash_rep; eauto.
  Qed.
End SDIR.
