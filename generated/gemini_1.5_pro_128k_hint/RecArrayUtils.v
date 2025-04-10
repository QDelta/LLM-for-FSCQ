Require Import Arith Rounding Psatz Lia Eqdep_dec List ListUtils Word Prog.
Require Import AsyncDisk Rec Array.
Import ListNotations.
Module Type RASig.
Parameter xparams : Type.
Parameter RAStart : xparams -> addr.
Parameter RALen   : xparams -> addr.
Parameter xparams_ok : xparams -> Prop.
Parameter itemtype : Rec.type.
Parameter items_per_val : nat.
Parameter blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
End RASig.
Module RADefs (RA : RASig).
Import RA.
Definition item := Rec.data itemtype.
Definition itemsz := Rec.len itemtype.
Definition item0 := @Rec.of_word itemtype $0.
Definition blocktype : Rec.type := Rec.ArrayF itemtype items_per_val.
Definition blocksz := Rec.len blocktype.
Definition block := Rec.data blocktype.
Definition val2word (v : valu) : word (blocksz).
rewrite blocksz_ok in v; trivial.
Defined.
Definition word2val (w : word blocksz) : valu.
rewrite blocksz_ok; trivial.
Defined.
Definition block2val (b : block) := word2val (Rec.to_word b).
Definition val2block (v : valu) := Rec.of_word (val2word v).
Definition block0 := val2block $0.
Definition itemlist := list item.
Definition nils n := @repeat (list valu) nil n.
Local Hint Resolve eq_nat_dec : core.
Theorem val2word2val_id : forall w, val2word (word2val w) = w.
(* hint proof tokens: 45 *)
Proof.
    unfold val2word, word2val, eq_rec_r, eq_rec; simpl; intros.
    rewrite eq_rect_nat_double.
    erewrite eq_rect_eq_dec; auto.
  Qed.
Theorem word2val2word_id : forall v, word2val (val2word v) = v.
Proof.
(* original proof tokens: 45 *)
(* generated proof tokens: 48 *)

Proof.
    unfold val2word, word2val, eq_rec_r, eq_rec; simpl; intros.
    rewrite eq_rect_nat_double.
    erewrite eq_rect_eq_dec; auto.
  Qed.

Local Hint Resolve Rec.of_to_id Rec.to_of_id val2word2val_id word2val2word_id.
Hint Rewrite val2word2val_id word2val2word_id Rec.of_to_id Rec.to_of_id : core.
Ltac small_t' := intros; autorewrite with core; autorewrite with core in *;
             eauto; simpl in *; intuition; eauto.
Ltac small_t := repeat small_t'; subst; simpl; eauto.
Theorem val2block2val_id : forall b, 
    Rec.well_formed b -> val2block (block2val b) = b.
Proof.
(* skipped proof tokens: 20 *)
Admitted.
Theorem block2val2block_id : forall v,
    block2val (val2block v) = v.
Proof.
(* skipped proof tokens: 20 *)
Admitted.
Local Hint Resolve val2block2val_id block2val2block_id Forall_forall: core.
Local Hint Resolve divup_mono firstn_nil.
Hint Rewrite val2block2val_id block2val2block_id: core.
Hint Rewrite combine_length : core.
Theorem val2block2val_selN_id : forall bl i,
    Forall Rec.well_formed bl
    -> val2block (selN (map block2val bl) i $0) = selN bl i block0.
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Hint Rewrite val2block2val_selN_id.
Lemma items_per_val_not_0 : items_per_val <> 0.
(* hint proof tokens: 35 *)
Proof.
    generalize blocksz_ok.
    rewrite valulen_is.
    intros; intro.
    rewrite H0 in H.
    discriminate.
  Qed.
Lemma items_per_val_gt_0 : items_per_val > 0.
(* hint proof tokens: 19 *)
Proof.
    pose proof items_per_val_not_0; lia.
  Qed.
Lemma items_per_val_gt_0' : 0 < items_per_val.
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Local Hint Resolve items_per_val_not_0 items_per_val_gt_0 items_per_val_gt_0'.
Hint Rewrite firstn_nil : core.
Hint Rewrite setlen_nil : core.
Theorem block0_repeat : block0 = repeat item0 items_per_val.
Proof.
(* skipped proof tokens: 113 *)
Admitted.
Hint Resolve block0_repeat.
Hint Resolve divup_ge.
Local Hint Resolve Rec.of_word_well_formed.
Lemma item0_wellformed : Rec.well_formed item0.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Lemma block0_wellformed : Rec.well_formed block0.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Local Hint Resolve item0_wellformed block0_wellformed.
Hint Rewrite setlen_length : core.
Lemma setlen_wellformed : forall l n,
    Forall Rec.well_formed l
    -> Forall (@Rec.well_formed itemtype) (setlen l n item0).
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Local Hint Resolve setlen_wellformed : core.
Local Hint Resolve forall_skipn.
Fixpoint list_chunk' {A} (l : list A) (sz : nat) (def : A) (nr : nat) : list (list A) :=
    match nr with
    | S n => setlen l sz def :: (list_chunk' (skipn sz l) sz def n)
    | O => []
    end.
Fixpoint nopad_list_chunk' {A} (l : list A) (sz : nat) (nr : nat) : list (list A) :=
    match nr with
    | S n => firstn sz l :: (nopad_list_chunk' (skipn sz l) sz n)
    | O => []
    end.
Definition list_chunk {A} l sz def : list (list A) :=
    list_chunk' l sz def (divup (length l) sz).
Definition nopad_list_chunk {A} l sz : list (list A) :=
    nopad_list_chunk' l sz (divup (length l) sz).
Lemma list_chunk'_length: forall A nr l sz (def : A),
      length (list_chunk' l sz def nr) = nr.
(* hint proof tokens: 15 *)
Proof.
    induction nr; simpl; auto.
  Qed.
Hint Rewrite list_chunk'_length : core.
Lemma list_chunk_length: forall A l sz (def : A),
      length (list_chunk l sz def) = divup (length l) sz.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 23 *)

unfold list_chunk; intros.
rewrite list_chunk'_length.
reflexivity.
Qed.

Hint Rewrite list_chunk_length : core.
Lemma nopad_list_chunk'_length: forall A nr (l : list A) sz,
    length (nopad_list_chunk' l sz nr) = nr.
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Lemma nopad_list_chunk_length : forall A (l : list A) sz,
    length (nopad_list_chunk l sz) = divup (length l) sz.
(* hint proof tokens: 25 *)
Proof.
    unfold nopad_list_chunk; intros.
    apply nopad_list_chunk'_length.
  Qed.
Hint Rewrite nopad_list_chunk_length : core.
Theorem list_chunk'_wellformed : forall nr items,
    Forall Rec.well_formed items
    -> Forall (@Rec.well_formed blocktype) (list_chunk' items items_per_val item0 nr).
Proof.
(* skipped proof tokens: 23 *)
Admitted.
Theorem list_chunk_wellformed : forall items,
    Forall Rec.well_formed items
    -> Forall (@Rec.well_formed blocktype) (list_chunk items items_per_val item0).
(* hint proof tokens: 21 *)
Proof.
    intros; eapply list_chunk'_wellformed; eauto.
  Qed.
Local Hint Resolve list_chunk_wellformed.
Lemma block_chunk_length: forall l sz,
      @length block (@list_chunk item l sz item0) = divup (length l) sz.
(* hint proof tokens: 15 *)
Proof.
    intros; apply list_chunk_length.
  Qed.
Hint Rewrite block_chunk_length : core.
Lemma list_chunk_nil : forall  A sz (def : A),
    list_chunk nil sz def = nil.
(* hint proof tokens: 25 *)
Proof.
    unfold list_chunk; small_t.
    rewrite divup_0; small_t.
  Qed.
Lemma list_chunk'_Forall_length : forall A nr l sz (i0 : A),
    Forall (fun b => length b = sz) (list_chunk' l sz i0 nr).
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 29 *)

induction nr; intros; simpl; auto.
constructor.
rewrite setlen_length; auto.
apply IHnr.
Qed.

Lemma list_chunk_In_length : forall A l sz (i0 : A) x,
    In x (list_chunk l sz i0) -> length x = sz.
(* hint proof tokens: 33 *)
Proof.
    intros until i0; apply Forall_forall.
    unfold list_chunk.
    apply list_chunk'_Forall_length.
  Qed.
Local Hint Resolve in_selN.
Hint Rewrite skipn_length.
Lemma list_chunk_selN_length : forall l i,
    length (selN (list_chunk l items_per_val item0) i block0) = items_per_val.
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Hint Rewrite list_chunk_selN_length.
Lemma list_chunk'_spec : forall A nr i l sz (i0 : A) b0,
    i < nr ->
    selN (list_chunk' l sz i0 nr) i b0 = setlen (skipn (i * sz) l) sz i0.
(* hint proof tokens: 51 *)
Proof.
    induction nr; small_t. inversion H.
    destruct i. small_t.
    erewrite IHnr by small_t.
    rewrite skipn_skipn; simpl.
    f_equal; f_equal; lia.
  Qed.
Lemma list_chunk_spec' : forall A l i n (e0 : A) b0,
    n <> 0 -> b0 = repeat e0 n ->
    selN (list_chunk l n e0) i b0 
    = setlen (skipn (i * n) l) n e0.
(* hint proof tokens: 58 *)
Proof.
    unfold list_chunk; intros.
    destruct (lt_dec i (divup (length l) n)).
    apply list_chunk'_spec; auto.
    rewrite selN_oob by small_t.
    rewrite skipn_oob; small_t.
  Qed.
Lemma list_chunk_spec : forall l i,
    selN (list_chunk l items_per_val item0) i block0 
    = setlen (skipn (i * items_per_val) l) items_per_val item0.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Lemma nopad_list_chunk'_spec: forall A nr i (l : list A) sz (b0 : list A),
    i < nr ->
    selN (nopad_list_chunk' l sz nr) i b0 = firstn sz (skipn (i * sz) l).
(* hint proof tokens: 51 *)
Proof.
    induction nr; cbn; intros.
    lia.
    destruct i; cbn; auto.
    rewrite IHnr by lia.
    rewrite plus_comm.
    rewrite skipn_skipn.
    reflexivity.
  Qed.
Lemma nopad_list_chunk_spec: forall l i,
    i < divup (length l) items_per_val ->
    selN (nopad_list_chunk l items_per_val) i block0 =
    firstn items_per_val (skipn (i * items_per_val) l).
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma list_chunk'_skipn_1: forall A n l k (e0 : A),
    list_chunk' (skipn n l) n e0 (k - 1) = skipn 1 (list_chunk' l n e0 k).
(* hint proof tokens: 26 *)
Proof.
    induction k; intros; simpl; auto; rewrite Nat.sub_0_r; auto.
  Qed.
Lemma list_chunk_skipn_1 : forall A n l (e0 : A),
    list_chunk (skipn n l) n e0 = skipn 1 (list_chunk l n e0).
(* hint proof tokens: 171 *)
Proof.
    unfold list_chunk; intros.
    rewrite skipn_length.
    destruct (Nat.eq_dec n 0).
    subst; simpl; auto.
    destruct (lt_dec (length l) n).
    replace (length l - n) with 0 by lia.
    rewrite divup_0.
    apply Nat.lt_le_incl in l0; apply divup_le_1 in l0.
    destruct (Nat.eq_dec (divup (length l) n) 1).
    rewrite e.
    setoid_rewrite skipn_oob at 2; simpl; auto.
    replace (divup (length l) n) with 0 by lia.
    simpl; auto.
    rewrite divup_sub_1 by lia.
    apply list_chunk'_skipn_1.
  Qed.
Lemma skipn_list_chunk_skipn_eq : forall A i l n (e0 : A),
    skipn i (list_chunk l n e0) = list_chunk (skipn (i * n) l) n e0.
(* hint proof tokens: 76 *)
Proof.
    induction i; intros.
    simpl; auto.
    simpl (S i * n).
    rewrite <- skipn_skipn'.
    rewrite <- IHi; auto.
    rewrite list_chunk_skipn_1.
    rewrite skipn_skipn.
    replace (S i) with (i + 1) by lia; auto.
  Qed.
Local Hint Resolve divup_le divup_mul_ge.
Lemma skipn_repeat_list_chunk : forall A i l n (e0 : A) B (x : B),
    skipn i (repeat x (length (list_chunk l n e0)))
    = repeat x (length (list_chunk (skipn (i * n) l) n e0)).
Proof.
(* skipped proof tokens: 120 *)
Admitted.
Local Hint Resolve skipn_list_chunk_skipn_eq list_chunk_skipn_1 skipn_repeat_list_chunk.
Hint Rewrite app_nil_l app_nil_r firstn_length Nat.sub_diag Nat.sub_0_r: core.
Lemma list_chunk'_firstn' : forall A i n l (e0 : A),
    length l >= i * n ->
    list_chunk' (firstn (i * n) l) n e0 i = list_chunk' l n e0 i.
Proof.
(* skipped proof tokens: 84 *)
Admitted.
Lemma list_chunk'_firstn : forall A i n l (e0 : A),
    list_chunk' (firstn (i * n) l) n e0 i = list_chunk' l n e0 i.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_list_chunk' : forall A m n i l (e0 : A),
    n <= m ->
    firstn n (list_chunk' l i e0 m) = list_chunk' l i e0 n.
(* hint proof tokens: 29 *)
Proof.
    induction m; destruct n; small_t.
    inversion H.
    rewrite IHm; small_t.
  Qed.
Hint Rewrite divup_mul Nat.mul_0_r Nat.mul_0_l.
Lemma list_chunk_firstn' : forall A i n l (e0 : A),
    n <> 0 -> length l >= i * n ->
    list_chunk (firstn (i * n) l) n e0 = firstn i (list_chunk l n e0).
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma list_chunk_firstn : forall A i n l (e0 : A),
    list_chunk (firstn (i * n) l) n e0 = firstn i (list_chunk l n e0).
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Lemma firstn_list_chunk_app : forall l i pre,
    items_per_val + i * items_per_val <= length l
    -> pre = firstn (i * items_per_val) l
    -> firstn (i * items_per_val + items_per_val) l 
       = pre ++ (selN (list_chunk l items_per_val item0) i block0).
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma firstn_setlen_firstn : forall A l m n (def : A),
    n <= m -> n <= length l -> firstn n (setlen l m def) = firstn n l.
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma list_chunk'_app : forall A na sz a b (def : A),
    sz <> 0 ->
    length a = sz * na ->
    list_chunk' (a ++ b) sz def (na + divup (length b) sz) =
    list_chunk' a sz def na ++ list_chunk' b sz def (divup (length b) sz).
(* hint proof tokens: 93 *)
Proof.
    induction na; small_t.
    replace (a ++ b) with b; auto.
    rewrite length_nil with (l := a); auto; lia.
    repeat rewrite setlen_inbound by (autorewrite with lists; nia).
    rewrite firstn_app_l by nia.
    f_equal.
    rewrite skipn_app_l by nia.
    rewrite IHna; auto.
    autorewrite with core; nia.
  Qed.
Lemma list_chunk_app: forall A na sz a b (def : A),
    sz <> 0 ->
    length a = sz * na ->
    list_chunk (a ++ b) sz def = list_chunk a sz def ++ list_chunk b sz def.
(* hint proof tokens: 90 *)
Proof.
    unfold list_chunk; intros.
    rewrite app_length; autorewrite with core lists.
    repeat (rewrite H0; rewrite Nat.mul_comm; rewrite divup_mul by auto).
    rewrite <- list_chunk'_app; auto.
    f_equal.
    replace (na * sz + length b) with (length b + sz * na) by lia.
    rewrite divup_add by auto; lia.
  Qed.
Definition ipack items := map block2val (list_chunk items items_per_val item0).
Definition nopad_ipack items := map block2val (nopad_list_chunk items items_per_val).
Definition iunpack (r : itemlist) (v : valu) : itemlist :=
    r ++ (val2block v).
Lemma well_formed_app_iff : forall A (a b : list (Rec.data A)) ,
     Forall Rec.well_formed (a ++ b)
     <-> Forall Rec.well_formed a /\ Forall Rec.well_formed b.
(* hint proof tokens: 39 *)
Proof.
    intros; repeat (try split; rewrite Forall_forall in *; small_t).
    destruct (in_app_or a b x); small_t.
  Qed.
Lemma nils_length : forall n,
    length (nils n) = n.
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma ipack_length : forall items,
    length (ipack items) = divup (length items) items_per_val.
(* hint proof tokens: 30 *)
Proof.
    unfold ipack; intros.
    rewrite map_length.
    setoid_rewrite list_chunk_length; auto.
  Qed.
Lemma nopad_ipack_length : forall (l : itemlist),
    length (nopad_ipack l) = divup (length l) items_per_val.
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma ipack_app: forall na a b,
    length a = na * items_per_val ->
    ipack (a ++ b) = ipack a ++ ipack b.
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Lemma ipack_nil : ipack nil = nil.
Proof.
(* skipped proof tokens: 20 *)
Admitted.
Lemma ipack_one : forall l,
    length l = items_per_val ->
    ipack l = block2val l :: nil.
(* hint proof tokens: 51 *)
Proof.
    unfold ipack, list_chunk; intros.
    rewrite H.
    rewrite divup_same by auto; simpl.
    rewrite setlen_inbound by lia.
    rewrite firstn_oob by lia; auto.
  Qed.
Lemma iunpack_ipack_one : forall l init,
    Forall Rec.well_formed l ->
    length l = items_per_val ->
    fold_left iunpack (ipack l) init = init ++ l.
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma list_chunk'_app_def : forall A n z l k (def : A),
    list_chunk' (l ++ repeat def z) k def n = list_chunk' l k def n.
Proof.
(* skipped proof tokens: 181 *)
Admitted.
Lemma ipack_app_item0 : forall l n,
    n <= (roundup (length l) items_per_val - length l) ->
    ipack (l ++ repeat item0 n) = ipack l.
Proof.
(* skipped proof tokens: 48 *)
Admitted.
Lemma well_formed_firstn : forall A n (a : list (Rec.data A)), 
    Forall Rec.well_formed a
    -> Forall Rec.well_formed (firstn n a).
(* hint proof tokens: 35 *)
Proof.
    intros.
    rewrite Forall_forall in *; intros.
    apply H; eapply in_firstn_in; eauto.
  Qed.
Lemma well_formed_skipn : forall A n (a : list (Rec.data A)), 
    Forall Rec.well_formed a
    -> Forall Rec.well_formed (skipn n a).
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma to_word_setlen: forall n (l : Rec.data (Rec.ArrayF itemtype n)),
    length l < n ->
    @Rec.to_word (Rec.ArrayF itemtype n) (setlen l n (Rec.of_word $0)) = Rec.to_word l.
Proof.
(* skipped proof tokens: 142 *)
Admitted.
Local Hint Resolve Forall_append well_formed_firstn well_formed_skipn.
Lemma iunpack_ipack' : forall nr init items ,
    Forall Rec.well_formed items ->
    length items = nr * items_per_val ->
    fold_left iunpack (ipack items) init = init ++ items.
Proof.
(* skipped proof tokens: 128 *)
Admitted.
Lemma iunpack_ipack : forall nr items,
    Forall Rec.well_formed items ->
    length items = nr * items_per_val ->
    fold_left iunpack (ipack items) nil = items.
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma iunpack_ipack_firstn : forall n nr items,
    Forall Rec.well_formed items ->
    length items = nr * items_per_val ->
    fold_left iunpack (firstn n (ipack items)) nil = 
    firstn (n * items_per_val) items.
(* hint proof tokens: 271 *)
Proof.
    induction n; intros.
    simpl; auto.

    destruct (lt_dec n (length (ipack items))).
    rewrite firstn_S_selN with (def := $0) by auto.
    rewrite fold_left_app.
    erewrite IHn; simpl; eauto.

    rewrite ipack_length in l.
    unfold iunpack, ipack; rewrite Nat.add_comm.
    erewrite firstn_list_chunk_app; [ f_equal | | apply eq_refl ].
    erewrite selN_map, val2block2val_id; eauto.
    apply Forall_selN.
    apply list_chunk_wellformed; auto.
    setoid_rewrite list_chunk_length; auto.
    setoid_rewrite list_chunk_length; auto.

    rewrite H0 in *.
    rewrite divup_mul in l by auto.
    apply lt_le_S in l; eapply mult_le_compat_r in l; eauto.

    repeat rewrite firstn_oob; try lia.
    eapply iunpack_ipack; eauto.
    rewrite ipack_length in n0.
    rewrite H0 in *.
    rewrite divup_mul in n0 by auto.
    apply Nat.nlt_ge in n0.
    apply mult_le_compat; lia.
  Qed.
Lemma ipack_iunpack_one : forall (a : valu),
    [ a ] = ipack (iunpack [] a).
(* hint proof tokens: 57 *)
Proof.
    intros.
    unfold iunpack.
    rewrite app_nil_l.
    rewrite ipack_one, block2val2block_id; auto.
    unfold val2block, blocktype.
    rewrite Rec.array_of_word_length.
    auto.
  Qed.
Lemma iunpack_length : forall init nr a,
    length init = nr ->
    length (iunpack init a) = nr + items_per_val.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma fold_left_iunpack_length' : forall l init nr,
    length init = nr ->
    length (fold_left iunpack l init) = nr + (length l) * items_per_val.
(* hint proof tokens: 46 *)
Proof.
    induction l; simpl; intros.
    lia.

    erewrite IHl.
    instantiate (1 := nr + items_per_val). lia.
    apply iunpack_length; auto.
  Qed.
Lemma fold_left_iunpack_length : forall l,
    length (fold_left iunpack l []) = (length l) * items_per_val.
(* hint proof tokens: 34 *)
Proof.
    intros.
    erewrite fold_left_iunpack_length'; eauto.
    lia.

    Unshelve.
    constructor.
  Qed.
Lemma ipack_iunpack : forall l,
    (forall l', Forall (@Rec.well_formed itemtype) l') ->
    l = ipack (fold_left iunpack l []).
(* hint proof tokens: 131 *)
Proof.
    induction l; intros; simpl.
    rewrite <- ipack_nil.
    auto.

    rewrite IHl at 2.
    erewrite iunpack_ipack'.
    erewrite ipack_app.
    rewrite <- ipack_iunpack_one.
    rewrite cons_app.
    f_equal; auto.
    unfold iunpack.
    rewrite app_nil_l.
    unfold val2block, blocktype.
    rewrite Rec.array_of_word_length.
    instantiate (1:=1); lia.
    auto.
    instantiate (1:=length l).
    apply fold_left_iunpack_length.
    auto.
  Qed.
Lemma ipack_nopad_ipack_eq : forall x,
    ipack x = nopad_ipack x.
(* hint proof tokens: 186 *)
Proof.
    unfold ipack, nopad_ipack.
    intros.
    eapply selN_map_eq; cbn; intros.
    destruct (lt_dec i (divup (length x) items_per_val)).
    - rewrite list_chunk_spec.
      rewrite nopad_list_chunk_spec by auto.
      unfold block2val, blocktype in *.
      destruct (lt_dec (length x - i * items_per_val) items_per_val).
      rewrite to_word_setlen.
      rewrite firstn_oob; auto.
      all: rewrite ?skipn_length; auto.
      cbv in *; lia.
      rewrite setlen_inbound; auto.
      rewrite skipn_length; lia.
    - repeat rewrite selN_oob by (autorewrite with core; apply Nat.le_ngt; eauto).
      reflexivity.
    - autorewrite with core. auto.
  Qed.
Lemma mod_lt_length_firstn_skipn : forall A ix (l : list A),
    ix < length l ->
    ix mod items_per_val < length (firstn items_per_val (skipn (ix / items_per_val * items_per_val) l)).
(* hint proof tokens: 82 *)
Proof.
    intros.
    rewrite firstn_length, skipn_length.
    apply Nat.min_glb_lt.
    apply Nat.mod_upper_bound; auto.
    rewrite Nat.mod_eq, Nat.mul_comm by auto.
    enough (ix >= ix / items_per_val * items_per_val).
    lia.
    rewrite Nat.mul_comm.
    apply Nat.mul_div_le; auto.
  Qed.
Lemma ipack_selN_divmod : forall items ix,
    (@Forall block) Rec.well_formed (list_chunk items items_per_val item0) ->
    ix < length items ->
    selN (val2block (selN (ipack items) (ix / items_per_val) $0)) (ix mod items_per_val) item0
    = selN items ix item0.
(* hint proof tokens: 94 *)
Proof.
    unfold ipack; intros.
    rewrite val2block2val_selN_id by auto.
    rewrite list_chunk_spec.
    setoid_rewrite selN_app1.
    rewrite selN_firstn.
    rewrite skipn_selN.
    rewrite Nat.mul_comm.
    rewrite <- Nat.div_mod; auto.
    apply Nat.mod_upper_bound; auto.
    eapply mod_lt_length_firstn_skipn; auto.
  Qed.
Lemma list_chunk_updN_divmod : forall items ix e,
    ix < length items ->
    updN (list_chunk items items_per_val item0) (ix / items_per_val)
      (updN (selN (list_chunk items items_per_val item0) (ix / items_per_val) block0)
        (ix mod items_per_val) e) =
    list_chunk (updN items ix e) items_per_val item0.
(* hint proof tokens: 254 *)
Proof.
    intros.
    eapply list_selN_ext; intros.
    rewrite length_updN.
    setoid_rewrite list_chunk_length; rewrite length_updN; auto.
    repeat rewrite list_chunk_spec.

    destruct (Nat.eq_dec pos (ix / items_per_val)); subst.
    rewrite selN_updN_eq; unfold setlen.
    setoid_rewrite skipn_length; rewrite length_updN.
    repeat rewrite updN_app1; [ f_equal | ].
    rewrite <- updN_firstn_comm.
    rewrite updN_skipn; repeat f_equal.
    rewrite Nat.mul_comm, Nat.add_comm, <- Nat.div_mod; auto.
    apply mod_lt_length_firstn_skipn; auto.
    setoid_rewrite list_chunk_length.
    apply div_lt_divup; auto.

    rewrite length_updN, list_chunk_length in H0.
    rewrite selN_updN_ne by auto.
    rewrite list_chunk_spec.
    rewrite setlen_skipn_updN_absorb; auto.
    apply not_eq in n; destruct n.
    right; apply lt_div_mul_add_le; auto.
    left; apply div_lt_mul_lt; auto.
  Qed.
Lemma ipack_updN_divmod : forall items ix e,
    (@Forall block) Rec.well_formed (list_chunk items items_per_val item0) ->
    ix < length items ->
    updN (ipack items) (ix / items_per_val) (block2val
      (updN (val2block (selN (ipack items) (ix / items_per_val) $0)) (ix mod items_per_val) e)) =
    ipack (updN items ix e).
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma block2val_repeat_item0 :
    block2val (repeat item0 items_per_val) = $0.
(* hint proof tokens: 65 *)
Proof.
    unfold block2val, item0.
    rewrite <- Rec.of_word_zero_list.
    rewrite Rec.to_of_id.
    unfold word2val, eq_rec_r, eq_rect, eq_rec, eq_rect.
    case_eq (eq_sym blocksz_ok); intros; auto.
  Qed.
Lemma repeat_ipack_item0 : forall n,
    repeat $0 n = ipack (repeat item0 (n * items_per_val)).
(* hint proof tokens: 88 *)
Proof.
    induction n; simpl; intros.
    rewrite ipack_nil; auto.
    rewrite <- repeat_app.
    erewrite ipack_app with (na := 1) by (rewrite repeat_length; lia).
    rewrite cons_app, IHn; f_equal.
    rewrite ipack_one by (rewrite repeat_length; auto); f_equal.
    rewrite block2val_repeat_item0; auto.
  Qed.
Lemma Forall_wellformed_updN : forall (items : list item) a v,
    Forall Rec.well_formed items ->
    Rec.well_formed v ->
    Forall Rec.well_formed (updN items a v).
(* hint proof tokens: 40 *)
Proof.
    intros.
    rewrite Forall_forall in *; intuition.
    apply in_updN in H1; destruct H1; subst; eauto.
  Qed.
Lemma synced_list_ipack_length_ok : forall len i items,
    i < len ->
    length items = len * items_per_val ->
    i < length (synced_list (ipack items)).
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma ipack_length_eq : forall len a b,
    length a = len * items_per_val ->
    length b = len * items_per_val ->
    length (ipack a) = length (ipack b).
(* hint proof tokens: 33 *)
Proof.
    intros.
    repeat rewrite ipack_length.
    setoid_rewrite H; setoid_rewrite H0; auto.
  Qed.
Definition ifind_block (cond : item -> addr -> bool) (vs : block) start : option (addr * item ) :=
    ifind_list cond vs start.
Lemma ifind_result_inbound :  forall len bn items cond r,
    Forall Rec.well_formed items ->
    bn < len ->
    ifind_block cond (val2block (fst (selN (synced_list (ipack items)) bn ($0, nil))))
      (bn * items_per_val) = Some r ->
    length items = len * items_per_val ->
    fst r < length items.
(* hint proof tokens: 148 *)
Proof.
    intros.
    apply ifind_list_ok_facts with (d := item0) in H1 as [Hm [ Hb [ Hc Hi ] ] ].
    apply list_chunk_wellformed in H.
    rewrite synced_list_selN in Hb; simpl in Hb.
    unfold ipack in *; rewrite val2block2val_selN_id in * by auto.
    rewrite list_chunk_spec, setlen_length in *.

    rewrite H2.
    eapply lt_le_trans; eauto.
    setoid_rewrite <- Nat.mul_1_l at 5.
    rewrite <- Nat.mul_add_distr_r.
    apply Nat.mul_le_mono_r; lia.
  Qed.
Lemma ifind_result_item_ok : forall len bn items cond r,
    Forall Rec.well_formed items ->
    bn < len ->
    ifind_block cond (val2block (fst (selN (synced_list (ipack items)) bn ($0, nil))))
      (bn * items_per_val) = Some r ->
    length items = len * items_per_val ->
    (snd r) = selN items (fst r) item0.
Proof.
(* skipped proof tokens: 224 *)
Admitted.
Lemma ifind_block_none_progress : forall i ix items v cond len,
    (forall ix, ix < i * items_per_val ->
         cond (selN items ix item0) ix = false) ->
    ifind_block cond (val2block v) (i * items_per_val) = None ->
    v = fst (selN (synced_list (ipack items)) i ($0, nil)) ->
    ix < items_per_val + i * items_per_val ->
    i < len ->
    length items = len * items_per_val ->
    Forall Rec.well_formed items ->
    cond (selN items ix item0) ix = false.
Proof.
(* skipped proof tokens: 304 *)
Admitted.
Definition selN_val2block v idx :=
    Rec.of_word (@Rec.word_selN' itemtype items_per_val idx (val2word v)).
Definition block2val_updN_val2block v idx item :=
    word2val (@Rec.word_updN' itemtype items_per_val idx (val2word v) (Rec.to_word item)).
Theorem selN_val2block_equiv : forall v idx item0,
    idx < items_per_val ->
    selN_val2block v idx = selN (val2block v) idx item0.
(* hint proof tokens: 34 *)
Proof.
    unfold selN_val2block; intros.
    erewrite Rec.word_selN'_equiv by auto.
    reflexivity.
  Qed.
Theorem block2val_updN_val2block_equiv : forall v idx item,
    idx < items_per_val ->
    block2val_updN_val2block v idx item =
    block2val (updN (val2block v) idx item).
(* hint proof tokens: 39 *)
Proof.
    unfold block2val_updN_val2block; intros.
    erewrite Rec.word_updN'_equiv by auto.
    reflexivity.
  Qed.
End RADefs.
