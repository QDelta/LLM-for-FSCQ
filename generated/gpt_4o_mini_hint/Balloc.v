Require Import Arith.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Lia.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Nomega.
Require Import Idempotent.
Require Import Psatz.
Require Import Rec.
Require Import NArith.
Require Import Log.
Require Import RecArrayUtils.
Require Import LogRecArray.
Require Import ListPred.
Require Import GenSepN.
Require Import WordAuto.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Cache.
Require Import Rec.
Import ListUtils.
Import ListNotations.
Set Implicit Arguments.
Module Type AllocSig.
Parameter xparams : Type.
Parameter BMPStart : xparams -> addr.
Parameter BMPLen   : xparams -> addr.
Parameter xparams_ok : xparams -> Prop.
End AllocSig.
Module Type WordBMapSig.
Parameter word_size : addr.
Parameter word_size_ok : Nat.divide word_size valulen.
Theorem word_size_nonzero : word_size <> 0.
(* hint proof tokens: 37 *)
Proof.
    intro H.
    apply valulen_nonzero.
    apply Nat.divide_0_l.
    rewrite <- H.
    apply word_size_ok.
  Qed.
End WordBMapSig.
Module BmpWordSig (Sig : AllocSig) (WBSig : WordBMapSig) <: RASig.
Import Sig.
Definition xparams := xparams.
Definition RAStart := BMPStart.
Definition RALen := BMPLen.
Definition xparams_ok := xparams_ok.
Definition itemtype := Rec.WordF WBSig.word_size.
Definition items_per_val := valulen / WBSig.word_size.
Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
(* hint proof tokens: 54 *)
Proof.
    unfold items_per_val. simpl.
    pose proof WBSig.word_size_nonzero.
    rewrite Rounding.mul_div; try lia.
    apply Nat.mod_divide; auto.
    apply WBSig.word_size_ok.
  Qed.
End BmpWordSig.
Module BmpWord (Sig : AllocSig) (WBSig : WordBMapSig).
Module BmpSig := BmpWordSig Sig WBSig.
Module Bmp := LogRecArray BmpSig.
Module Defs := Bmp.Defs.
Import Sig.
Definition state := word Defs.itemsz.
Definition full := wones Defs.itemsz.
Definition state_dec := weq full.
Definition bit := word 1.
Definition avail : bit := $0.
Definition inuse : bit := $1.
Definition Avail (b : bit) : Prop := b = avail.
Definition HasAvail (s : state) : Prop := s <> full.
Definition bits {sz} (s : word sz) : list bit.
apply (@Rec.of_word (Rec.ArrayF (Rec.WordF 1) sz)).
cbn.
rewrite Nat.mul_1_r.
exact s.
Defined.
Lemma bits_length : forall sz (w : word sz), length (bits w) = sz.
Proof.
(* original proof tokens: 46 *)
induction w; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma bits_cons : forall sz b (w : word sz),
    bits (WS b w) = (WS b WO) :: bits w.
(* hint proof tokens: 50 *)
Proof.
    unfold bits, Rec.of_word. simpl. intros.
      eq_rect_simpl; repeat f_equal;
      erewrite ?whd_eq_rect_mul, ?wtl_eq_rect_mul;
      reflexivity.
  Qed.
Definition has_avail (s : state) := if state_dec s then false else true.
Definition avail_nonzero s i := if (addr_eq_dec i 0) then (has_avail (s ^| wone _)) else has_avail s.
Definition ifind_byte (s : state) : option (addr * bit) :=
    ifind_list (fun (b : bit) (_ : addr) => if weq b avail then true else false) (bits s) 0.
Definition set_bit {sz} (s : word sz) (b : bit) (index : nat) : word sz.
set (f := @Rec.word_updN (Rec.WordF 1) sz index).
cbn in *.
refine (eq_rect (sz * 1) word _ sz (Nat.mul_1_r _)).
refine (f _ b).
rewrite Nat.mul_1_r.
exact s.
Defined.
Lemma bits_of_word : forall sz (w : word sz),
    w = eq_rect _ word (@Rec.to_word (Rec.ArrayF (Rec.WordF 1) sz) (bits w)) sz (Nat.mul_1_r sz).
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma bits_set_avail : forall sz (s : word sz) v n, n < sz ->
    bits (set_bit s v n) = updN (bits s) n v.
(* hint proof tokens: 166 *)
Proof.
    unfold set_bit, bits, bit.
    intros.
    rewrite (bits_of_word s).
    eq_rect_simpl.
    pose proof (Rec.word_updN_equiv (Rec.WordF 1)) as Ha.
    simpl in Ha.
    specialize (Ha sz n (@Rec.to_word (Rec.ArrayF (Rec.WordF 1) sz) (@bits sz s))).
    change v with (@Rec.to_word (Rec.WordF 1) v) at 1.
    rewrite Ha by auto.
    rewrite Rec.of_to_id; auto.
    unfold Rec.well_formed. split; auto.
    rewrite length_updN.
    rewrite Rec.of_to_id.
    auto using bits_length.
    apply Rec.of_word_well_formed.
  Qed.
Definition free lxp xp bn ms :=
    let index := (bn / Defs.itemsz) in
    let^ (ms, s) <- Bmp.get lxp xp index ms;
    let s' := set_bit s avail (bn mod Defs.itemsz) in
    ms <- Bmp.put lxp xp index s' ms;
    Ret ms.
Definition ifind_avail_nonzero lxp xp ms :=
    let^ (ms, r) <- Bmp.ifind lxp xp avail_nonzero ms;
    match r with
    | None => Ret ^(ms, None)
    | Some (bn, nonfull) =>
      match ifind_byte (if addr_eq_dec bn 0 then (nonfull ^| wone _) else nonfull) with
      | None =>
         Ret ^(ms, None)
      | Some (i, _) =>
        Ret ^(ms, Some (bn, i, nonfull))
      end
    end.
Definition alloc lxp xp ms :=
    let^ (ms, r) <- ifind_avail_nonzero lxp xp ms;
    match r with
    | None =>
        Ret ^(ms, None)
    | Some (bn, index, s) =>
      let s' := set_bit s inuse index in
        ms <- Bmp.put lxp xp bn s' ms;
        Ret ^(ms, Some (bn * Defs.itemsz + index))
    end.
Fixpoint bits_to_freelist (l : list bit) (start : addr) : list addr :=
    match l with
    | nil => nil
    | b :: l' =>
      let freelist' := bits_to_freelist l' (S start) in
      if (weq b inuse) then freelist' else
      if (addr_eq_dec start 0) then freelist' else start :: freelist'
    end.
Definition word_to_freelist {sz} (b : word sz) (start : addr) : list addr :=
    bits_to_freelist (bits b) start.
Fixpoint itemlist_to_freelist' {sz} (bs : list (word sz)) (start : addr) : list addr :=
    match bs with
    | nil => nil
    | b :: bs' => (word_to_freelist b start) ++ (itemlist_to_freelist' bs' (start + sz))
    end.
Definition itemlist_to_freelist {sz} bs := @itemlist_to_freelist' sz bs 0.
Definition get_free_blocks lxp xp ms :=
    let^ (ms, r) <- Bmp.read lxp xp (BMPLen xp) ms;
    Ret ^(ms, itemlist_to_freelist r).
Definition steal lxp xp bn ms :=
    let index := (bn / Defs.itemsz) in
    let^ (ms, s) <- Bmp.get lxp xp index ms;
    let s' := set_bit s inuse (bn mod Defs.itemsz) in
    ms <- Bmp.put lxp xp index s' ms;
    Ret ms.
Definition init lxp xp ms :=
    ms <- Bmp.init lxp xp ms;
    Ret ms.
Definition init_nofree lxp xp ms :=
    ms <- Bmp.init lxp xp ms;
    ms <- Bmp.write lxp xp (repeat full ((BMPLen xp) * BmpSig.items_per_val)) ms;
    Ret ms.
Definition to_bits {sz} (l : list (word sz)) : list bit :=
    concat (map (@bits sz) l).
Lemma to_bits_length : forall sz (l : list (word sz)),
    length (to_bits l) = length l * sz.
(* hint proof tokens: 56 *)
Proof.
    unfold to_bits. intros.
    erewrite concat_hom_length, map_length.
    reflexivity.
    apply Forall_forall; intros.
    rewrite in_map_iff in *.
    deex. auto using bits_length.
  Qed.
Opaque Nat.div Nat.modulo.
Local Hint Resolve WBSig.word_size_nonzero.
Local Hint Extern 1 (0 < _) => apply Nat.neq_0_lt_0.
Definition freelist_bmap_equiv freelist (bmap : list bit) :=
    Forall (fun a => a < length bmap) freelist /\
    forall a, (In a freelist <-> Avail (selN bmap a inuse)).
Definition rep V FP xp (freelist : list addr) (freepred : @pred _ addr_eq_dec V) :=
    (exists blist, Bmp.rep xp blist *
     [[ NoDup freelist ]] *
     [[ freelist_bmap_equiv freelist (to_bits blist) ]] *
     [[ freepred <=p=> listpred (fun a => exists v, a |-> v * [[ FP v ]]) freelist ]] )%pred.
Lemma freelist_bmap_equiv_remove_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
    a < length bmap ->
    freelist_bmap_equiv (remove addr_eq_dec a freelist) (updN bmap a inuse).
(* hint proof tokens: 186 *)
Proof.
    unfold freelist_bmap_equiv; split; intros.
    eapply Forall_remove; intuition eauto.
    eapply Forall_impl; try eassumption.
    simpl; intros.
    rewrite length_updN; eauto.

    split; intuition; intros.

    destruct (addr_eq_dec a a0); subst.
    rewrite selN_updN_eq by auto.
    exfalso; eapply remove_In; eauto.
    rewrite selN_updN_ne by auto.
    apply H3.
    eapply remove_still_In; eauto.

    destruct (addr_eq_dec a a0); subst.
    contradict H1.
    rewrite selN_updN_eq by auto.
    discriminate.
    apply remove_other_In; auto.
    apply H3.
    erewrite <- selN_updN_ne; eauto.
  Qed.
Lemma to_bits_updN_set_avail : forall (l : list state) bn v d,
    bn / Defs.itemsz < length l ->
    to_bits (updN l (bn / Defs.itemsz) (set_bit (selN l (bn / Defs.itemsz) d) v (bn mod Defs.itemsz))) =
    updN (to_bits l) bn v.
Proof.
(* original proof tokens: 136 *)

(* No more tactics to try *)
Admitted.

Lemma freelist_bmap_equiv_add_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
    a < length bmap ->
    freelist_bmap_equiv (a :: freelist) (updN bmap a avail).
(* hint proof tokens: 153 *)
Proof.
    unfold freelist_bmap_equiv; split; intuition; intros.

    constructor.
    rewrite length_updN; eauto.

    eapply Forall_impl; try eassumption.
    simpl; intros.
    rewrite length_updN; eauto.

    destruct (addr_eq_dec a a0); subst.
    rewrite selN_updN_eq by auto.
    unfold Avail; auto.
    rewrite selN_updN_ne by auto.
    apply H2.
    inversion H; congruence.

    destruct (addr_eq_dec a a0); subst; simpl; auto.
    right; apply H2.
    erewrite <- selN_updN_ne; eauto.
  Qed.
Lemma is_avail_in_freelist : forall a bmap freelist,
    freelist_bmap_equiv freelist bmap ->
    Avail (selN bmap a inuse) ->
    a < length bmap ->
    In a freelist.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma bits_len_rewrite : forall xp, BmpSig.RALen xp * BmpSig.items_per_val * Defs.itemsz = BMPLen xp * valulen.
(* hint proof tokens: 46 *)
Proof.
    intros.
    unfold BmpSig.RALen.
    rewrite BmpSig.blocksz_ok.
    cbn [Rec.len BmpSig.itemtype].
    auto using mult_assoc.
  Qed.
Lemma bmap_rep_length_ok1 : forall F xp blist d a,
    a < length (to_bits blist) ->
    (F * Bmp.rep xp blist)%pred d ->
    a < BMPLen xp * valulen.
(* hint proof tokens: 60 *)
Proof.
    unfold Bmp.rep, Bmp.items_valid; intros.
    destruct_lift H0.
    eapply lt_le_trans; eauto.
    rewrite to_bits_length.
    setoid_rewrite H6.
    rewrite bits_len_rewrite; auto.
  Qed.
Lemma bmap_rep_length_ok2 : forall F xp bmap d a,
    (F * Bmp.rep xp bmap)%pred d ->
    a < BMPLen xp * valulen ->
    a / Defs.itemsz < length bmap.
(* hint proof tokens: 59 *)
Proof.
    unfold Bmp.rep, Bmp.items_valid; intros.
    destruct_lift H.
    apply Nat.div_lt_upper_bound; auto.
    setoid_rewrite H6.
    rewrite mult_comm.
    rewrite bits_len_rewrite.
    auto.
  Qed.
Lemma bits_rep_bit : forall n x, bits (rep_bit n x) = repeat x n.
(* hint proof tokens: 38 *)
Proof.
    induction n; intros; simpl.
    reflexivity.
    rewrite bits_cons.
    shatter_word x.
    simpl.
    congruence.
  Qed.
Lemma to_bits_set_bit : forall sz i ii (bytes : list (word sz)) v d,
    i < length bytes ->
    ii < sz ->
    to_bits (updN bytes i (set_bit (selN bytes i d) v ii)) =
    updN (to_bits bytes) (i * sz + ii) v.
(* hint proof tokens: 87 *)
Proof.
    intros.
    unfold to_bits.
    rewrite plus_comm.
    rewrite updN_concat; auto.
    rewrite map_updN.
    erewrite selN_map by auto.
    rewrite bits_set_avail by auto.
    reflexivity.
    apply Forall_forall.
    intros.
    rewrite in_map_iff in *.
    deex; subst.
    apply bits_length.
  Qed.
Lemma bound_offset : forall a b c n,
    a < b -> c < n ->
    a * n + c < b * n.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Theorem selN_to_bits : forall sz n l d,
    sz <> 0 ->
    selN (to_bits l) n d = selN (bits (selN l (n / sz) (rep_bit sz d))) (n mod sz) d.
Proof.
(* original proof tokens: 152 *)

(* No more tactics to try *)
Admitted.

Lemma avail_nonzero_is_avail : forall bmap i ii b d d',
    i < length bmap ->
    ifind_byte (selN bmap i d') = Some (ii, b) ->
    Avail (selN (to_bits bmap) (i * Defs.itemsz + ii) d).
(* hint proof tokens: 185 *)
Proof.
    unfold avail_nonzero; intros.
    unfold Avail.
    apply ifind_list_ok_bound in H0 as H1; simpl in H1.
    rewrite bits_length in *.
    rewrite selN_to_bits by auto.
    rewrite Nat.div_add_l by auto.
    rewrite Nat.div_small by auto.
    rewrite Nat.add_0_r.
    rewrite plus_comm.
    rewrite Nat.mod_add by auto.
    rewrite Nat.mod_small by auto.
    apply ifind_list_ok_cond in H0 as H2.
    simpl in *.
    destruct weq; subst; try congruence.
    eapply ifind_list_ok_item in H0.
    simpl in *.
    rewrite Nat.sub_0_r in *.
    erewrite selN_inb with (d1 := d') in H0.
    apply H0.
    auto.
  Qed.
Lemma bits_wor_wone : forall sz (w : word (S sz)),
    bits (w ^| wone _) = inuse :: bits (wtl w).
(* hint proof tokens: 38 *)
Proof.
    intros.
    destruct (shatter_word_S w); repeat deex.
    rewrite wor_wone.
    rewrite bits_cons.
    reflexivity.
  Qed.
Lemma avail_nonzero_first_is_avail : forall bmap ii b d d',
    length bmap > 0 ->
    ifind_byte (selN bmap 0 d' ^| wone _) = Some (ii, b) ->
    Avail (selN (to_bits bmap) ii d).
Proof.
(* original proof tokens: 354 *)

(* No more tactics to try *)
Admitted.

Lemma ifind_byte_first_not_zero : forall (w : state) b,
    ifind_byte (w ^| wone _) = Some (0, b) -> False.
Proof.
(* original proof tokens: 131 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve avail_nonzero_is_avail avail_nonzero_first_is_avail ifind_byte_first_not_zero.
Lemma avail_item0 : forall n d, n < Defs.itemsz -> Avail (selN (bits Bmp.Defs.item0) n d).
Proof.
(* original proof tokens: 112 *)

(* No more tactics to try *)
Admitted.

Lemma freelist_bmap_equiv_init_ok : forall xp,
    freelist_bmap_equiv (seq 0 (BMPLen xp * valulen))
      (to_bits (repeat Bmp.Defs.item0 (BmpSig.RALen xp * BmpSig.items_per_val))).
(* hint proof tokens: 200 *)
Proof.
    unfold freelist_bmap_equiv; intuition; intros.
    - eapply Forall_forall.
      intros.
      eapply in_seq in H.
      rewrite to_bits_length.
      rewrite repeat_length.
      rewrite bits_len_rewrite. lia.
    - rewrite selN_to_bits by auto.
      rewrite repeat_selN; auto.
      rewrite avail_item0.
      unfold Avail; auto.
      apply Nat.mod_upper_bound; auto.
      eapply in_seq in H.
      apply Nat.div_lt_upper_bound; auto.
      rewrite mult_comm, bits_len_rewrite.
      intuition idtac.
    - apply in_seq; intuition.
      destruct (lt_dec a (BMPLen xp * valulen)); try lia.
      rewrite selN_oob in *.
      cbv in *; congruence.
      rewrite to_bits_length.
      rewrite repeat_length.
      rewrite bits_len_rewrite.
      lia.
  Qed.
Lemma bits_to_freelist_bound: forall l start,
    let freelist := bits_to_freelist l start in
    forall x, In x freelist -> start <= x < start + (length l).
(* hint proof tokens: 102 *)
Proof.
    split; generalize dependent start;
      induction l; cbn; intuition.
    all: repeat match goal with
    | _ => lia
    | [H: context [if ?x then _ else _] |- _ ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [H: In _ _ |- _] => apply IHl in H
    end.
  Qed.
Lemma bits_to_freelist_nodup : forall l start,
    NoDup (bits_to_freelist l start).
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma bits_to_freelist_no_zero : forall l start,
    let freelist := bits_to_freelist l start in
    ~In 0 freelist.
Proof.
(* original proof tokens: 92 *)

(* No more tactics to try *)
Admitted.

Lemma bits_to_freelist_spec : forall l start,
    let freelist := bits_to_freelist l start in
    forall i, (start + i <> 0) -> In (start + i) freelist <-> selN l i inuse = avail.
(* hint proof tokens: 315 *)
Proof.
    unfold bit in *.
    induction l; cbn; intuition.
    cbv in *; congruence.
    destruct i;
    repeat match goal with
    | _ => lia
    | _ => solve [auto]
    | [H: context [_ + S _] |- _] => rewrite <- plus_Snm_nSm in H
    | [H: context [if ?x then _ else _] |- _ ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [H: In _ _ |- _] => apply IHl in H
    end.
    apply bits_to_freelist_bound in H0. lia.
    shatter_word a. destruct x; cbv in *; congruence.
    shatter_word a. destruct x; cbv in *; congruence.
    destruct i;
    repeat match goal with
    | _ => lia
    | _ => solve [auto | cbv in *; congruence]
    | _ => rewrite <- plus_Snm_nSm
    | [|- context [if ?x then _ else _] ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [|- In _ _ ] => apply IHl
    end.
    autorewrite with core. intuition.
    right. rewrite IHl; auto. lia.
  Qed.
Lemma itemlist_to_freelist'_bound: forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    forall x, In x freelist -> start <= x < start + length (to_bits bs) /\ x > 0.
Proof.
(* original proof tokens: 158 *)

(* No more tactics to try *)
Admitted.

Lemma itemlist_to_freelist'_spec: forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    forall i, (start + i <> 0) -> In (start + i) freelist <-> selN (to_bits bs) i inuse = avail.
Proof.
(* original proof tokens: 306 *)

(* No more tactics to try *)
Admitted.

Lemma nodup_app: forall T (l1 l2 : list T),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> ~In x l2) ->
    (forall x, In x l2 -> ~In x l1) ->
    NoDup (l1 ++ l2).
(* hint proof tokens: 56 *)
Proof.
    induction l1; cbn; intros; auto.
    inversion H; subst.
    constructor.
    rewrite in_app_iff.
    specialize (H1 a) as ?. intuition.
    apply IHl1; intuition eauto.
  Qed.
Lemma itemlist_to_freelist'_nodup : forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    NoDup freelist.
Proof.
(* original proof tokens: 104 *)

(* No more tactics to try *)
Admitted.

Lemma itemlist_to_freelist'_no_zero : forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    ~In 0 freelist.
(* hint proof tokens: 42 *)
Proof.
    induction bs; cbn; intuition.
    apply in_app_or in H. intuition eauto.
    eapply bits_to_freelist_no_zero; eauto.
  Qed.
Lemma itemlist_to_freelist_bound: forall sz (bs : list (word sz)),
    let freelist := itemlist_to_freelist bs in
    forall x, In x freelist -> x < length (to_bits bs).
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma itemlist_to_freelist_spec: forall sz (bs : list (word sz)),
    let freelist := itemlist_to_freelist bs in
    forall i, i <> 0 -> In i freelist <-> selN (to_bits bs) i inuse = avail.
(* hint proof tokens: 47 *)
Proof.
    cbn; unfold itemlist_to_freelist; intros.
    replace i with (0 + i) in * by lia.
    auto using itemlist_to_freelist'_spec.
  Qed.
Lemma itemlist_to_freelist_nodup: forall sz bs,
    let freelist := @itemlist_to_freelist sz bs in
    NoDup freelist.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma itemlist_to_freelist_no_zero: forall sz bs,
    let freelist := @itemlist_to_freelist sz bs in
    ~In 0 freelist.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma freelist_bmap_equiv_itemlist_to_freelist_spec: forall sz (bs : list (word sz)) freelist,
    NoDup freelist ->
    freelist_bmap_equiv freelist (to_bits bs) ->
    permutation addr_eq_dec (itemlist_to_freelist bs) (remove addr_eq_dec 0 freelist).
(* hint proof tokens: 465 *)
Proof.
    cbv [permutation freelist_bmap_equiv Avail]; intuition.
    pose proof (itemlist_to_freelist_nodup bs).
    rewrite (NoDup_count_occ addr_eq_dec) in *.
    pose proof count_occ_In as Hc. unfold gt in Hc.
    repeat match goal with
    | H: context [count_occ] |- _ => specialize (H x)
    end.
    destruct (in_dec addr_eq_dec 0 freelist).
    - destruct (addr_eq_dec 0 x); subst.
      rewrite count_occ_remove_eq.
      apply count_occ_not_In.
      apply itemlist_to_freelist_no_zero.
      repeat rewrite count_occ_remove_ne by auto.
      destruct (zerop (count_occ addr_eq_dec freelist x)) as [Ha | Ha];
      destruct (zerop (count_occ addr_eq_dec (itemlist_to_freelist bs) x)) as [Hb | Hb]; try lia.
      all: rewrite <- count_occ_not_In, <- Hc in *.
      apply itemlist_to_freelist_spec in Hb.
      rewrite <- H2 in *. congruence.
      intro; subst.
      eapply itemlist_to_freelist_no_zero; eauto.
      destruct (addr_eq_dec x 0); subst; intuition.
      rewrite H2 in *.
      rewrite <- itemlist_to_freelist_spec in Ha by auto.
      intuition.
    - rewrite remove_not_In by auto.
      destruct (zerop (count_occ addr_eq_dec freelist x)) as [Ha | Ha];
      destruct (zerop (count_occ addr_eq_dec (itemlist_to_freelist bs) x)) as [Hb | Hb]; try lia.
      all: rewrite <- count_occ_not_In, <- Hc in *.
      apply itemlist_to_freelist_spec in Hb.
      rewrite <- H2 in *. congruence.
      intro; subst.
      eapply itemlist_to_freelist_no_zero; eauto.
      destruct (addr_eq_dec x 0); subst; intuition.
      rewrite H2 in *.
      rewrite <- itemlist_to_freelist_spec in Ha by auto.
      intuition.
  Qed.
Hint Extern 0 (okToUnify (listpred ?prd _ ) (listpred ?prd _)) => constructor : okToUnify.
Theorem init_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BMPStart xp) bl) ]]] *
          [[ xparams_ok xp /\ BMPStart xp <> 0 /\ length bl = BMPLen xp ]]
    POST:hm' RET:ms exists m' freelist freepred,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ forall bn, bn < (BMPLen xp) * valulen -> In bn freelist ]] *
          [[ forall dl, length dl = ((BMPLen xp) * valulen)%nat ->
               Forall FP dl ->
               arrayN (@ptsto _ _ _) 0 dl =p=> freepred ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.
(* hint proof tokens: 57 *)
Proof.
    unfold init, rep; intros.
    step.
    step.
    eapply seq_NoDup.
    apply freelist_bmap_equiv_init_ok.
    apply in_seq; intuition.
    apply arrayN_listpred_seq_fp; auto.
  Qed.
Lemma full_eq_repeat : full = rep_bit Defs.itemsz inuse.
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Lemma ifind_byte_inb : forall x n b,
    ifind_byte x = Some (n, b) ->
    n < Defs.itemsz.
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Theorem init_nofree_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BMPStart xp) bl) ]]] *
          [[ xparams_ok xp /\ BMPStart xp <> 0 /\ length bl = BMPLen xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp nil emp) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init_nofree lxp xp ms.
Proof.
(* original proof tokens: 153 *)

(* No more tactics to try *)
Admitted.

Theorem get_free_blocks_ok : forall V FP lxp xp ms,
    {<F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]]
    POST:hm' RET:^(ms, r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
          [[ ~In 0 r ]] * [[ NoDup r ]] *
          [[ permutation addr_eq_dec r (remove addr_eq_dec 0 freelist) ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} get_free_blocks lxp xp ms.
(* hint proof tokens: 105 *)
Proof.
    unfold get_free_blocks, rep.
    step.
    step.
    eapply itemlist_to_freelist_no_zero; eauto.
    rewrite firstn_oob by (erewrite Bmp.items_length_ok; eauto).
    apply itemlist_to_freelist_nodup.
    rewrite firstn_oob by (erewrite Bmp.items_length_ok; eauto).
    apply freelist_bmap_equiv_itemlist_to_freelist_spec; eauto.
  Qed.
Theorem steal_ok : forall V FP lxp xp bn ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ In bn freelist ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred') ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} steal lxp xp bn ms.
(* hint proof tokens: 367 *)
Proof.
    unfold steal, rep. intros.
    step.

    unfold freelist_bmap_equiv in *; intuition.
    denote! (Forall _ _) as Hf; eapply Forall_forall in Hf; eauto.
    denote (Bmp.rep _ dummy) as Hr; eapply Bmp.items_length_ok in Hr.
    rewrite to_bits_length in *.
    apply Nat.div_lt_upper_bound; auto.
    rewrite mult_comm; auto.

    assert (bn / Defs.itemsz < length dummy).
    unfold freelist_bmap_equiv in *; intuition.
    denote! (Forall _ _) as Hf; eapply Forall_forall in Hf; eauto.
    denote (Bmp.rep _ dummy) as Hr; eapply Bmp.items_length_ok in Hr.
    rewrite to_bits_length in *.
    apply Nat.div_lt_upper_bound; auto.
    rewrite mult_comm; auto.

    step.
    safestep.

    eapply NoDup_remove; eauto.
    rewrite to_bits_updN_set_avail by auto.
    eapply freelist_bmap_equiv_remove_ok; eauto.
    rewrite to_bits_length.
    apply Rounding.div_lt_mul_lt; auto.

    apply piff_refl.
    denote freepred as Hp; rewrite Hp, listpred_remove.
    eassign bn; cancel.

    intros.
    assert (~ (y |->? * y |->?)%pred m'0) as Hc by apply ptsto_conflict.
    contradict Hc; pred_apply; cancel.
    auto.

  Unshelve.
    all: try exact unit.
    all: eauto.
    all: try exact nil.
    all: intros; try exact True.
  Qed.
Theorem alloc_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]]
    POST:hm' RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm'
       \/ exists bn m' freepred',
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred') ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]] *
          [[ bn <> 0 /\ bn < (BMPLen xp) * valulen ]] *
          [[ In bn freelist ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} alloc lxp xp ms.
Proof.
(* original proof tokens: 355 *)

(* No more tactics to try *)
Admitted.

Theorem free_ok : forall V FP lxp xp bn ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ bn < (BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ exists mx Fx, (Fx * freepred * bn |->?)%pred mx ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (bn :: freelist) freepred') ]]] *
          [[ forall v, FP v -> bn |-> v * freepred =p=> freepred' ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} free lxp xp bn ms.
(* hint proof tokens: 225 *)
Proof.
    unfold free, rep.
    hoare.

    eapply bmap_rep_length_ok2; eauto.
    eapply bmap_rep_length_ok2; eauto.
    constructor; eauto.
    intro Hin.
    denote (freepred <=p=> _) as Hfp.
    denote (Fx) as Hx.
    rewrite Hfp in Hx.
    erewrite listpred_pick in Hx by eauto.
    destruct_lift Hx.
    eapply ptsto_conflict_F with (m := mx) (a := bn).
    pred_apply; cancel.

    rewrite to_bits_updN_set_avail; auto.
    apply freelist_bmap_equiv_add_ok; auto.
    rewrite to_bits_length.
    apply Rounding.div_lt_mul_lt; auto.
    eapply bmap_rep_length_ok2; eauto.
    eapply bmap_rep_length_ok2; eauto.
    denote (freepred <=p=> _) as Hfp. apply Hfp.
    Unshelve.
    all: eauto.
  Qed.
Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
Hint Extern 1 ({{_}} Bind (get_free_blocks _ _ _) _) => apply get_free_blocks_ok : prog.
Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.
Lemma rep_impl_bn_ok: forall F V FP xp freelist freepred m bn,
    (F * @rep V FP xp freelist freepred)%pred (list2nmem m) ->
    In bn freelist -> 
    bn < (Sig.BMPLen xp) * valulen.
(* hint proof tokens: 136 *)
Proof.
    intros.
    unfold rep in H.
    destruct_lift H.
    unfold freelist_bmap_equiv in *. intuition.
    eapply Forall_forall in H1; eauto.
    rewrite Bmp.items_length_ok_pimpl in H.
    rewrite BmpSig.blocksz_ok.
    simpl in *.
    destruct_lifts.
    rewrite to_bits_length in *.
    unfold state in *.
    cbn in *.
    denote (length _ = _) as Ha.
    rewrite Ha in *.
    rewrite mult_assoc.
    assumption.
    Unshelve.
    all : eauto; constructor.
  Qed.
Lemma rep_impl_NoDup: forall F V FP xp freelist freepred m,
    (F * @rep V FP xp freelist freepred)%pred (list2nmem m) ->
    NoDup freelist.
Proof.
(* original proof tokens: 36 *)
(* generated proof tokens: 32 *)

unfold rep in *; intros.
destruct_lifts.
unfold freelist_bmap_equiv in *; intuition.
Qed.

Lemma xform_rep : forall V FP xp l p,
    crash_xform (@rep V FP xp l p) <=p=> @rep V FP xp l p.
(* hint proof tokens: 49 *)
Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite Bmp.xform_rep; cancel.
    cancel.
    xform_normr.
    rewrite Bmp.xform_rep; cancel.
  Qed.
Lemma xform_rep_rawpred : forall xp FP l p,
    (forall a, crash_xform (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
    crash_xform (rep FP xp l p) =p=> rep FP xp l p * [[ crash_xform p =p=> p ]].
(* hint proof tokens: 45 *)
Proof.
    unfold rep; intros.
    xform_norm.
    rewrite Bmp.xform_rep; cancel.
    rewrite H2.
    rewrite xform_listpred_ptsto_fp; auto.
  Qed.
End BmpWord.
Module ByteBmap <: WordBMapSig.
Import Rec.
Definition word_size := 8.
Definition type := ArrayF (WordF 1) word_size.
Theorem word_size_ok : Nat.divide word_size valulen.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Theorem word_size_nonzero : word_size <> 0.
(* hint proof tokens: 14 *)
Proof.
    compute; congruence.
  Qed.
End ByteBmap.
Module BmapAlloc (Sig : AllocSig) := BmpWord Sig ByteBmap.
Module BmapAllocCache (Sig : AllocSig).
Module Alloc := BmapAlloc Sig.
Module Defs := Alloc.Defs.
Definition BmapCacheType := option (list addr).
Record memstate := mk_memstate {
    MSLog  : LOG.memstate;
    MSCache   : BmapCacheType; 
  }.
Definition freelist0 : BmapCacheType := None.
Definition init lxp xp fms : prog memstate :=
    fms <- Alloc.init lxp xp fms;
    Ret (mk_memstate fms freelist0 ).
Definition init_nofree lxp xp ms :=
    fms <- Alloc.init_nofree lxp xp ms;
    Ret (mk_memstate fms freelist0).
Definition get_free_blocks lxp xp ms :=
    match (MSCache ms) with
    | Some x => Ret ^(ms, x)
    | None =>
      let^ (fms, freelist) <- Alloc.get_free_blocks lxp xp (MSLog ms);
      Ret ^((mk_memstate fms (Some freelist)), freelist)
    end.
Definition cache_free_block a ms :=
    match (MSCache ms) with
    | Some x => Some (a :: x)
    | None => None
    end.
Definition alloc lxp xp (ms : memstate) :=
    let^ (ms, freelist) <- get_free_blocks lxp xp ms;
    match freelist with
    | nil =>
      Ret ^(ms, None)
    | bn :: freelist' =>
      fms <- Alloc.steal lxp xp bn (MSLog ms);
      Ret ^((mk_memstate fms (Some freelist')), Some bn)
    end.
Definition free lxp xp bn ms :=
    fms <- Alloc.free lxp xp bn (MSLog ms);
    let cache := cache_free_block bn ms in
    Ret (mk_memstate fms cache).
Definition steal lxp xp bn (ms:memstate) :=
    fms <- Alloc.steal lxp xp bn (MSLog ms) ;
    Ret (mk_memstate fms freelist0).
Definition cache_rep (freelist : list addr) cache :=
    forall cfreelist, cache = Some cfreelist ->
    ~In 0 cfreelist /\ NoDup cfreelist /\
    permutation addr_eq_dec (remove addr_eq_dec 0 freelist) cfreelist.
Definition rep V FP xp freelist (freepred : @pred _ addr_eq_dec V) ms :=
    (Alloc.rep FP xp freelist freepred *
    [[ cache_rep freelist (MSCache ms) ]])%pred.
Fact cache_rep_freelist0: forall freelist, cache_rep freelist freelist0.
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Hint Resolve cache_rep_freelist0.
Lemma cache_rep_remove_cons: forall freelist n cache',
    cache_rep freelist (Some (n :: cache')) ->
    cache_rep (remove addr_eq_dec n freelist) (Some cache').
Proof.
(* original proof tokens: 112 *)

(* No more tactics to try *)
Admitted.

Lemma cache_rep_add_cons: forall freelist x cache,
    cache_rep freelist (Some cache) ->
    x <> 0 -> ~In x cache ->
    cache_rep (x :: freelist) (Some (x :: cache)).
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Lemma cache_rep_in: forall bn freelist cache,
    cache_rep freelist (Some cache) ->
    bn <> 0 ->
    In bn freelist <-> In bn cache.
(* hint proof tokens: 87 *)
Proof.
    unfold cache_rep. intros.
    specialize (H _ eq_refl). intuition.
    rewrite count_occ_In.
    rewrite <- H3.
    rewrite count_occ_remove_ne by auto.
    rewrite <- count_occ_In. auto.
    rewrite count_occ_In.
    erewrite <- count_occ_remove_ne by eauto.
    rewrite H3.
    rewrite <- count_occ_In. auto.
  Qed.
Lemma cache_rep_none: forall freelist,
    cache_rep freelist None.
Proof.
(* original proof tokens: 20 *)
(* generated proof tokens: 14 *)

apply cache_rep_freelist0.
Qed.

Hint Resolve cache_rep_none.
Ltac apply_cache_rep := match goal with
    | Hm: MSCache _ = _, H: cache_rep _ _ |- _ =>
      rewrite ?Hm in *; pose proof (H _ eq_refl) as ?; intuition
    end.
Theorem init_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (Sig.BMPStart xp) bl) ]]] *
          [[ Sig.xparams_ok xp /\ Sig.BMPStart xp <> 0 /\ length bl = Sig.BMPLen xp ]]
    POST:hm' RET:ms exists m' freepred freelist,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp freelist freepred ms) ]]] *
          [[ forall bn, bn < (Sig.BMPLen xp) * valulen -> In bn freelist ]] *
          [[ forall dl, length dl = ((Sig.BMPLen xp) * valulen)%nat ->
               Forall FP dl ->
               arrayN (@ptsto _ _ _) 0 dl =p=> freepred ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.
(* hint proof tokens: 21 *)
Proof.
    unfold init, rep; intros.
    step.
    step.
  Qed.
Theorem init_nofree_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (Sig.BMPStart xp) bl) ]]] *
          [[ Sig.xparams_ok xp /\ Sig.BMPStart xp <> 0 /\ length bl = Sig.BMPLen xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp nil emp ms) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init_nofree lxp xp ms.
(* hint proof tokens: 24 *)
Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
  Qed.
Theorem get_free_blocks_ok : forall V FP lxp xp (ms:memstate),
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    POST:hm' RET:^(ms, r)
          [[ MSCache ms = Some r ]] *
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm' *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} get_free_blocks lxp xp ms.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Hint Extern 0 ({{ _ }} Bind (get_free_blocks _ _ _) _) => apply get_free_blocks_ok : prog.
Theorem alloc_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    POST:hm' RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm'
       \/ exists bn m' freepred',
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred' ms) ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]] *
          [[ bn <> 0 /\ bn < (Sig.BMPLen xp) * valulen ]] *
          [[ In bn freelist ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} alloc lxp xp ms.
Proof.
(* original proof tokens: 165 *)
unfold Alloc.alloc.
(* No more tactics to try *)
Admitted.

Theorem free_ok : forall V FP lxp xp bn ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[ bn <> 0 ]] *
          [[ bn < (Sig.BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]] *
          [[ exists mx Fx, (Fx * freepred * bn |->?)%pred mx ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (bn :: freelist) freepred' ms) ]]] *
          [[ forall v, FP v -> bn |-> v * freepred =p=> freepred' ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} free lxp xp bn ms.
(* hint proof tokens: 96 *)
Proof.
    unfold free, rep; intros.
    safestep.
    eauto.
    step.
    unfold cache_free_block.
    destruct MSCache eqn:?; auto.
    eapply cache_rep_add_cons; eauto.
    assert (NoDup (bn :: freelist)) as Hd by (eauto using Alloc.rep_impl_NoDup).
    inversion Hd; subst.
    erewrite <- cache_rep_in by eauto. auto.
  Qed.
Theorem steal_ok : forall V FP lxp xp bn (ms:memstate),
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms)]]] *
          [[ In bn freelist /\ bn < (Sig.BMPLen xp) * valulen ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred' ms) ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} steal lxp xp bn ms.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
Hint Extern 0 (okToUnify (rep _ _ _ _ _) (rep _ _ _ _ _)) => constructor : okToUnify.
Lemma xform_rep : forall V FP xp l ms p,
    crash_xform (@rep V FP xp l ms p) <=p=> @rep V FP xp l ms p.
Proof.
(* original proof tokens: 63 *)
unfold rep; intros.
split; xform_norm; auto.
(* No more tactics to try *)
Admitted.

Lemma xform_rep_rawpred : forall xp FP l ms p,
    (forall a, crash_xform (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
    crash_xform (rep FP xp l p ms) =p=> (rep FP xp l p ms) * [[ crash_xform p =p=> p ]].
(* hint proof tokens: 74 *)
Proof.
    unfold rep, Alloc.rep; intros.
    xform_norm.
    cancel.
    rewrite Alloc.Bmp.xform_rep; cancel.
    assumption.
    denote (_ <=p=> _) as Hp. rewrite Hp.
    rewrite xform_listpred_ptsto_fp; auto.
  Unshelve.
    all: eauto.
  Qed.
Lemma rep_clear_mscache_ok : forall V FP bxps frees freepred lms cm,
    @rep V FP bxps frees freepred (mk_memstate lms cm) =p=>
    @rep V FP bxps frees freepred (mk_memstate lms freelist0).
Proof.
(* original proof tokens: 16 *)
unfold rep; simpl.
unfold rep, cache_rep in *.
(* No more tactics to try *)
Admitted.

Lemma rep_ignore_mslog_ok: forall V (FP : V -> _) xp freelist freepred log log' cache,
    rep FP xp freelist freepred (mk_memstate log cache) =
    rep FP xp freelist freepred (mk_memstate log' cache).
Proof.
(* original proof tokens: 13 *)

(* No more tactics to try *)
Admitted.

Lemma rep_clear_cache: forall V FP xp freelist freepred ms mslog,
    @rep V FP xp freelist freepred ms =p=>
    rep FP xp freelist freepred (mk_memstate mslog freelist0).
(* hint proof tokens: 17 *)
Proof.
    unfold rep, Alloc.rep.
    cancel.
  Qed.
Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) (rep _ ?xp _ _ _)) => apply rep_ignore_mslog_ok : okToUnify.
End BmapAllocCache.
Module BALLOC.
Module Sig <: AllocSig.
Definition xparams := balloc_xparams.
Definition BMPStart := BmapStart.
Definition BMPLen := BmapNBlocks.
Definition xparams_ok xp := (BmapNBlocks xp) <= valulen * valulen.
End Sig.
Module Alloc := BmapAlloc Sig.
Module Defs := Alloc.Defs.
Definition alloc lxp xp ms :=
    r <- Alloc.alloc lxp xp ms;
    Ret r.
Definition free lxp xp bn ms :=
    r <- Alloc.free lxp xp bn ms;
    Ret r.
Definition steal lxp xp bn ms :=
    r <- Alloc.steal lxp xp bn ms;
    Ret r.
Definition init lxp xp ms :=
    r <- Alloc.init lxp xp ms;
    Ret r.
Definition init_nofree lxp xp ms :=
    r <- Alloc.init_nofree lxp xp ms;
    Ret r.
Definition bn_valid xp bn := bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.
Definition FP (x : valuset) := True.
Definition rep xp (freeblocks : list addr) :=
    ( exists freepred, freepred * Alloc.rep FP xp freeblocks freepred)%pred.
Definition smrep (freeblocks : list addr) : @pred _ addr_eq_dec bool :=
    (listpred (fun a => a |->?) freeblocks)%pred.
Lemma listpred_seq_smrep: forall F xp fp m l freelist,
    (F * Alloc.rep FP xp freelist fp)%pred m ->
    (LOG.arrayP 0 l =p=> fp) ->
    listpred (fun a => a |->?) (seq 0 (length l)) =p=> smrep freelist.
Proof.
(* original proof tokens: 64 *)

(* No more tactics to try *)
Admitted.

Theorem init_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m bl dl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 dl
                        * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ (Fs * listpred (fun a => a |->?) (seq 0 (length dl)))%pred sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp /\ length dl = ((BmapNBlocks xp) * valulen)%nat ]]
    POST:hm' RET:ms exists m' freeblocks,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * rep xp freeblocks) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ forall bn, bn < (BmapNBlocks xp) * valulen -> In bn freeblocks ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.
(* hint proof tokens: 33 *)
Proof.
    unfold init, rep; intros.
    step.
    step.
    eapply listpred_seq_smrep; eauto.
  Qed.
Theorem init_nofree_ok : forall lxp xp ms,
    {< F Fs Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ Fs sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * rep xp nil) ]]] *
          [[ (Fs * smrep nil)%pred sm ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init_nofree lxp xp ms.
(* hint proof tokens: 24 *)
Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
  Qed.
Theorem steal_ok : forall lxp xp bn ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * rep xp freeblocks) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ bn_valid xp bn /\ In bn freeblocks ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * bn |->? * rep xp (remove addr_eq_dec bn freeblocks)) ]]] *
          [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} steal lxp xp bn ms.
(* hint proof tokens: 101 *)
Proof.
    unfold steal, rep, bn_valid.
    step.
    prestep. norm. cancel.
    intuition simpl.
    pred_apply.
    denote pimpl as Hx; rewrite Hx.
    cancel; cancel.
    unfold smrep in *.
    rewrite listpred_remove in *|- by eauto using ptsto_conflict.
    pred_apply; cancel.
    eauto.
    Unshelve. all: try exact addr_eq_dec; auto.
  Qed.
Theorem alloc_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * rep xp freeblocks) ]]] *
           [[ (Fs * smrep freeblocks)%pred sm ]]
    POST:hm' RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm'
        \/ exists bn m',
           [[ r = Some bn ]] * [[ bn_valid xp bn ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * bn |->? * rep xp (remove addr_eq_dec bn freeblocks)) ]]] *
           [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]] *
           [[ In bn freeblocks ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} alloc lxp xp ms.
Proof.
(* original proof tokens: 113 *)

(* No more tactics to try *)
Admitted.

Theorem free_ok : forall lxp xp bn ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ bn_valid xp bn ]] *
           [[[ m ::: (Fm * rep xp freeblocks * bn |->?) ]]] *
           [[ (Fs * bn |->? * smrep freeblocks)%pred sm ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * rep xp (bn :: freeblocks)) ]]] *
           [[ (Fs * smrep (bn :: freeblocks))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} free lxp xp bn ms.
(* hint proof tokens: 43 *)
Proof.
    unfold free, rep, bn_valid.
    hoare.
    exists (list2nmem m); pred_apply; cancel.
    unfold FP in *; eauto.
  Qed.
Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
Hint Extern 0 (okToUnify (rep ?xp _) (rep ?xp _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (smrep ?l) (smrep ?l)) => constructor : okToUnify.
Lemma sep_star_reorder_helper : forall a b c d : (@pred _ addr_eq_dec valuset),
    ((a * b) * (c * d)) =p=> d * (a * b * c).
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 8 *)

cancel.
Qed.

Lemma smrep_cons: forall l a b,
    smrep l * a |-> b =p=> smrep (a :: l).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Definition freevec lxp xp l ms :=
    let^ (ms) <- ForN i < length l
    Hashmap hm
    Ghost [ F Fm Fs crash m0 freeblocks sm ]
    Loopvar [ ms ]
    Invariant
      exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm *
      [[[ m' ::: (Fm * rep xp (rev (firstn i l) ++ freeblocks)) *
                       listpred (fun a => a |->?) (skipn i l) ]]] *
      [[ (Fs * smrep (rev (firstn i l) ++ freeblocks) *
                       listpred (fun a => a |->?) (skipn i l))%pred sm ]]
    OnCrash crash
    Begin
      ms <- free lxp xp (selN l i 0) ms;
      Ret ^(ms)
    Rof ^(ms);
    Ret ms.
Theorem freevec_ok : forall lxp xp l ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ Forall (bn_valid xp) l ]] *
           [[[ m ::: (Fm * rep xp freeblocks * listpred (fun a => a |->?) l ) ]]] *
           [[ (Fs * listpred (fun a => a |->?) l * smrep freeblocks)%pred sm ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * rep xp (rev l ++ freeblocks)) ]]] *
           [[ (Fs * smrep (rev l ++ freeblocks))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} freevec lxp xp l ms.
(* hint proof tokens: 351 *)
Proof.
    unfold freevec.
    step.

    prestep; norml.
    denote Fm as Hx.
    denote smrep as Hs.

    destruct l.
    denote (_ < _) as Hy; simpl in Hy; inversion Hy.
    rewrite listpred_isolate with (i := 0) in Hx, Hs by (rewrite skipn_length; lia).
    rewrite skipn_selN, Nat.add_0_r in Hx, Hs.

    
    apply sep_star_reorder_helper in Hx.
    apply pimpl_exists_r_star_r in Hx; destruct Hx as [ [? ?] ?].
    destruct_lift Hs.
    safecancel.
    rewrite selN_cons_fold; apply Forall_selN; auto.
    eauto.
    rewrite sep_star_assoc_1, sep_star_comm.
    eauto.

    step.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    replace ([n]) with (rev [n]) by auto.
    rewrite <- rev_app_distr.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    rewrite smrep_cons.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.

    step.
    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    step.
    erewrite <- LOG.intact_hashmap_subset; eauto.
    Unshelve. all: eauto; exact tt.
  Qed.
Hint Extern 1 ({{_}} Bind (freevec _ _ _ _) _) => apply freevec_ok : prog.
Lemma xparams_ok_goodSize : forall xp a,
    Sig.xparams_ok xp ->
    a < (BmapNBlocks xp) * valulen ->
    goodSize addrlen a.
(* hint proof tokens: 115 *)
Proof.
    unfold Sig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.
Lemma bn_valid_goodSize : forall F l m xp a,
    (F * rep xp l)%pred m ->
    bn_valid xp a ->
    goodSize addrlen a.
Proof.
(* original proof tokens: 59 *)

(* No more tactics to try *)
Admitted.

Lemma bn_valid_goodSize_pimpl : forall l xp,
    rep xp l <=p=> [[ forall a, bn_valid xp a -> goodSize addrlen a ]] * rep xp l.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma bn_valid_facts : forall xp bn,
    bn_valid xp bn -> bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.
(* hint proof tokens: 14 *)
Proof.
    unfold bn_valid; auto.
  Qed.
Theorem bn_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
(* hint proof tokens: 70 *)
Proof.
    unfold bn_valid; intuition.
    rewrite wordToNat_natToWord_idempotent' in H0; auto.
    eapply xparams_ok_goodSize; eauto.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.
Theorem bn_valid_roundtrip : forall xp a F l m,
    (F * rep xp l)%pred m ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma bn_valid_switch : forall xp1 xp2,
    BmapNBlocks xp1 = BmapNBlocks xp2 ->
    bn_valid xp1 = bn_valid xp2.
(* hint proof tokens: 22 *)
Proof.
    unfold bn_valid; intuition; auto.
    rewrite H; auto.
  Qed.
Definition items_per_val := Alloc.BmpSig.items_per_val.
Theorem xform_rep : forall xp l,
    crash_xform (rep xp l) =p=> rep xp l.
(* hint proof tokens: 55 *)
Proof.
    unfold rep; intros.
    xform_norm.
    rewrite Alloc.xform_rep_rawpred.
    cancel.
    auto.
    unfold FP; intros.
    xform_norm.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.
End BALLOC.
Module BALLOCC.
Module Sig <: AllocSig.
Definition xparams := balloc_xparams.
Definition BMPStart := BmapStart.
Definition BMPLen := BmapNBlocks.
Definition xparams_ok xp := (BmapNBlocks xp) <= valulen * valulen.
End Sig.
Module Alloc := BmapAllocCache Sig.
Module Defs := Alloc.Defs.
Definition BmapCacheType := Alloc.BmapCacheType.
Definition MSLog := Alloc.MSLog.
Definition MSCache := Alloc.MSCache.
Definition upd_memstate lms ms := Alloc.mk_memstate lms (Alloc.MSCache ms).
Definition mk_memstate lms cms := Alloc.mk_memstate lms cms.
Definition alloc lxp xp ms :=
    r <- Alloc.alloc lxp xp ms;
    Ret r.
Definition free lxp xp bn ms :=
    r <- Alloc.free lxp xp bn ms;
    Ret r.
Definition steal lxp xp bn ms :=
    r <- Alloc.steal lxp xp bn ms;
    Ret r.
Definition init lxp xp ms :=
    r <- Alloc.init lxp xp ms;
    Ret r.
Definition init_nofree lxp xp ms :=
    r <- Alloc.init_nofree lxp xp ms;
    Ret r.
Definition bn_valid xp bn := bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.
Definition FP (x : valuset) := True.
Definition rep xp (freeblocks : list addr) ms :=
    ( exists freepred, freepred * Alloc.rep FP xp freeblocks freepred ms)%pred.
Definition smrep (freeblocks : list addr) : @pred _ addr_eq_dec bool :=
    (listpred (fun a => a |->?) freeblocks)%pred.
Lemma listpred_seq_smrep: forall F xp fp ms m l freelist,
    (F * Alloc.rep FP xp freelist fp ms)%pred m ->
    (LOG.arrayP 0 l =p=> fp) ->
    listpred (fun a => a |->?) (seq 0 (length l)) =p=> smrep freelist.
Proof.
(* original proof tokens: 90 *)

(* No more tactics to try *)
Admitted.

Lemma rep_ignore_mslog_ok: forall bxps frees lms lms' cm,
    rep bxps frees (mk_memstate lms cm) =p=>
    rep bxps frees (mk_memstate lms' cm).
(* hint proof tokens: 21 *)
Proof.
    intros.
    unfold mk_memstate, rep.
    cancel.
  Qed.
Lemma rep_clear_mscache_ok : forall bxps frees lms cm,
    rep bxps frees (mk_memstate lms cm) =p=>
    rep bxps frees (mk_memstate lms Alloc.freelist0).
Proof.
(* original proof tokens: 34 *)
unfold rep. cancel.
(* No more tactics to try *)
Admitted.

Theorem init_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m bl dl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 dl
                        * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ (Fs * listpred (fun a => a |->?) (seq 0 (length dl)))%pred sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp /\ length dl = ((BmapNBlocks xp) * valulen)%nat ]]
    POST:hm' RET:ms exists m' freeblocks,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * rep xp freeblocks ms) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ forall bn, bn < (BmapNBlocks xp) * valulen -> In bn freeblocks ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.
(* hint proof tokens: 36 *)
Proof.
    unfold init, rep, MSLog; intros.
    step.
    step.
    eapply listpred_seq_smrep; eauto.
  Qed.
Theorem init_nofree_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ Fs sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[ (Fs * smrep nil)%pred sm ]] *
          [[[ m' ::: (Fm * rep xp nil ms) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init_nofree lxp xp ms.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Theorem steal_ok : forall lxp xp bn ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[[ m ::: (Fm * rep xp freeblocks ms) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ bn_valid xp bn /\ In bn freeblocks ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * bn |->? * 
           rep xp (remove addr_eq_dec bn freeblocks) ms) ]]] *
          [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} steal lxp xp bn ms.
Proof.
(* original proof tokens: 99 *)

(* No more tactics to try *)
Admitted.

Theorem alloc_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
           [[[ m ::: (Fm * rep xp freeblocks ms) ]]] *
           [[ (Fs * smrep freeblocks)%pred sm ]]
    POST:hm' RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm'
        \/ exists bn m',
           [[ r = Some bn ]] * [[ bn_valid xp bn ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
           [[[ m' ::: (Fm * bn |->? * 
            rep xp (remove addr_eq_dec bn freeblocks) ms) ]]] *
           [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]] *
           [[ In bn freeblocks ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} alloc lxp xp ms.
Proof.
(* original proof tokens: 96 *)

(* No more tactics to try *)
Admitted.

Theorem free_ok : forall lxp xp bn ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
           [[ bn_valid xp bn ]] *
           [[[ m ::: (Fm * rep xp freeblocks ms* bn |->?) ]]] *
           [[ (Fs * bn |->? * smrep freeblocks)%pred sm ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep xp (bn :: freeblocks) ms) ]]] *
           [[ (Fs * smrep (bn :: freeblocks))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} free lxp xp bn ms.
Proof.
(* original proof tokens: 46 *)
(* Let's start with the first tactic to structure the proof and set up the context. *)
intros lxp xp bn ms T rx.
(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
Hint Extern 0 (okToUnify (rep ?xp _ _) (rep ?xp _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (smrep ?l) (smrep ?l)) => constructor : okToUnify.
Lemma sep_star_reorder_helper : forall a b c d : (@pred _ addr_eq_dec valuset),
    ((a * b) * (c * d)) =p=> d * (a * b * c).
(* hint proof tokens: 12 *)
Proof.
    intros; cancel.
  Qed.
Lemma smrep_cons: forall l a b,
    smrep l * a |-> b =p=> smrep (a :: l).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Definition freevec lxp xp l ms :=
    let^ (ms) <- ForN i < length l
    Hashmap hm
    Ghost [ F Fm Fs crash m0 sm freeblocks ]
    Loopvar [ ms ]
    Invariant
      exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm *
      [[[ m' ::: (Fm * rep xp (rev (firstn i l) ++ freeblocks) ms) *
                       listpred (fun a => a |->?) (skipn i l) ]]] *
      [[ (Fs * smrep (rev (firstn i l) ++ freeblocks) *
                       listpred (fun a => a |->?) (skipn i l))%pred sm ]]
    OnCrash crash
    Begin
      ms <- free lxp xp (selN l i 0) ms;
      Ret ^(ms)
    Rof ^(ms);
    Ret ms.
Theorem freevec_ok : forall lxp xp l ms,
    {< F Fs Fm m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
           [[ Forall (bn_valid xp) l ]] *
           [[[ m ::: (Fm * rep xp freeblocks ms * listpred (fun a => a |->?) l ) ]]] *
           [[ (Fs * listpred (fun a => a |->?) l * smrep freeblocks)%pred sm ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep xp (rev l ++ freeblocks) ms) ]]] *
           [[ (Fs * smrep (rev l ++ freeblocks))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} freevec lxp xp l ms.
(* hint proof tokens: 380 *)
Proof.
    unfold freevec.
    safestep.
    eauto.
    eauto.

    prestep; norml.
    denote Fm as Hx.
    denote smrep as Hs.

    destruct l.
    denote (_ < _) as Hy; simpl in Hy; inversion Hy.
    rewrite listpred_isolate with (i := 0) in Hx, Hs by (rewrite skipn_length; lia).
    rewrite skipn_selN, Nat.add_0_r in Hx, Hs.

    
    apply sep_star_reorder_helper in Hx.
    apply pimpl_exists_r_star_r in Hx; destruct Hx as [ [? ?] ?].
    destruct_lift Hs.
    safecancel.
    rewrite selN_cons_fold; apply Forall_selN; auto.
    eauto.
    rewrite sep_star_assoc_1, sep_star_comm.
    eauto.

    step.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    replace ([n]) with (rev [n]) by auto.
    rewrite <- rev_app_distr.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    rewrite smrep_cons.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.

    step.
    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    step.
    cancel.
    erewrite <- LOG.intact_hashmap_subset; eauto.
    Unshelve. all: eauto; try exact tt. exact (LOG.mk_memstate0 (BUFCACHE.cache0 0)).
  Qed.
Hint Extern 1 ({{_}} Bind (freevec _ _ _ _) _) => apply freevec_ok : prog.
Lemma xparams_ok_goodSize : forall xp a,
    Sig.xparams_ok xp ->
    a < (BmapNBlocks xp) * valulen ->
    goodSize addrlen a.
Proof.
(* original proof tokens: 115 *)

(* No more tactics to try *)
Admitted.

Lemma bn_valid_goodSize : forall F l m ms xp a,
    (F * rep xp l ms)%pred m ->
    bn_valid xp a ->
    goodSize addrlen a.
Proof.
(* original proof tokens: 70 *)
rewrite ?bn_valid_facts.
intuition.
(* No more tactics to try *)
Admitted.

Lemma bn_valid_goodSize_pimpl : forall l xp ms,
    rep xp l ms <=p=> [[ forall a, bn_valid xp a -> goodSize addrlen a ]] * rep xp l ms.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma bn_valid_facts : forall xp bn,
    bn_valid xp bn -> bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.
(* hint proof tokens: 14 *)
Proof.
    unfold bn_valid; auto.
  Qed.
Theorem bn_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
(* hint proof tokens: 70 *)
Proof.
    unfold bn_valid; intuition.
    rewrite wordToNat_natToWord_idempotent' in H0; auto.
    eapply xparams_ok_goodSize; eauto.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.
Theorem bn_valid_roundtrip : forall xp a F l ms m,
    (F * rep xp l ms)%pred m ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma bn_valid_switch : forall xp1 xp2,
    BmapNBlocks xp1 = BmapNBlocks xp2 ->
    bn_valid xp1 = bn_valid xp2.
(* hint proof tokens: 22 *)
Proof.
    unfold bn_valid; intuition; auto.
    rewrite H; auto.
  Qed.
Definition items_per_val := Alloc.Alloc.BmpSig.items_per_val.
Theorem xform_rep : forall xp l ms,
    crash_xform (rep xp l ms) =p=> rep xp l ms.
Proof.
(* original proof tokens: 58 *)
unfold rep; intros.
xform_norm.
(* No more tactics to try *)
Admitted.

End BALLOCC.
Module IAlloc.
Module Sig <: AllocSig.
Definition xparams     := fs_xparams.
Definition BMPStart xp := BmapStart (FSXPInodeAlloc xp).
Definition BMPLen   xp := BmapNBlocks (FSXPInodeAlloc xp).
Definition xparams_ok xp := (BMPLen xp) <= valulen * valulen.
End Sig.
Module Alloc := BmapAllocCache Sig.
Module Defs := Alloc.Defs.
Definition BmapCacheType := Alloc.BmapCacheType.
Definition MSLog := Alloc.MSLog.
Definition MSCache := Alloc.MSCache.
Definition mk_memstate := Alloc.mk_memstate.
Definition init := Alloc.init.
Definition alloc := Alloc.alloc.
Definition free := Alloc.free.
Definition rep := Alloc.rep.
Definition ino_valid xp ino := ino < (Sig.BMPLen xp) * valulen.
Definition init_ok := Alloc.init_ok.
Definition alloc_ok := Alloc.alloc_ok.
Definition free_ok := Alloc.free_ok.
Definition items_per_val := Alloc.Alloc.BmpSig.items_per_val.
Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) (rep _ ?xp _ _ _)) => constructor : okToUnify.
Definition xform_rep := Alloc.xform_rep.
Lemma xparams_ok_goodSize : forall xp ino,
    Sig.xparams_ok xp ->
    ino_valid xp ino ->
    goodSize addrlen ino.
(* hint proof tokens: 118 *)
Proof.
    unfold Sig.xparams_ok, ino_valid; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.
Lemma ino_valid_goodSize : forall V FP F l m xp a prd allocc,
    (F * @rep V FP xp l prd allocc)%pred m ->
    ino_valid xp a ->
    goodSize addrlen a.
(* hint proof tokens: 70 *)
Proof.
    unfold rep, ino_valid.
    unfold Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.
Lemma ino_valid_goodSize_pimpl : forall V FP l xp p allocc,
    @rep V FP xp l p allocc <=p=> [[ forall a, ino_valid xp a -> goodSize addrlen a ]] * rep FP xp l p allocc.
(* hint proof tokens: 46 *)
Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply ino_valid_goodSize; eauto.
    cancel.
  Qed.
Theorem ino_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    ino_valid xp a ->
    ino_valid xp (# (natToWord addrlen a)).
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem ino_valid_roundtrip : forall V FP xp a F l m p allocc,
    (F * @rep V FP xp l p allocc)%pred m ->
    ino_valid xp a ->
    ino_valid xp (# (natToWord addrlen a)).
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma rep_clear_cache: forall V FP xp freelist freepred ms mslog,
    @rep V FP xp freelist freepred ms =p=>
    rep FP xp freelist freepred (mk_memstate mslog Alloc.freelist0).
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 15 *)

unfold rep, Alloc.rep.
cancel.
Qed.

Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) _) => unfold rep; trivial with okToUnify : okToUnify.
Hint Extern 0 (okToUnify _ (rep _ ?xp _ _ _)) => unfold rep; trivial with okToUnify : okToUnify.
End IAlloc.
