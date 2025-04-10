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
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Theorem word2val2word_id : forall v, word2val (val2word v) = v.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma items_per_val_gt_0 : items_per_val > 0.
Proof.
(* skipped proof tokens: 19 *)
Admitted.
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
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Hint Rewrite list_chunk'_length : core.
Lemma list_chunk_length: forall A l sz (def : A),
      length (list_chunk l sz def) = divup (length l) sz.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 24 *)

intros.
unfold list_chunk.
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
Proof.
(* skipped proof tokens: 25 *)
Admitted.
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
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Local Hint Resolve list_chunk_wellformed.
Lemma block_chunk_length: forall l sz,
      @length block (@list_chunk item l sz item0) = divup (length l) sz.
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Hint Rewrite block_chunk_length : core.
Lemma list_chunk_nil : forall  A sz (def : A),
    list_chunk nil sz def = nil.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma list_chunk'_Forall_length : forall A nr l sz (i0 : A),
    Forall (fun b => length b = sz) (list_chunk' l sz i0 nr).
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 37 *)

induction nr; intros.
- simpl. constructor.
- simpl. constructor.
  + rewrite setlen_length. trivial.
  + apply IHnr.
Qed.

Lemma list_chunk_In_length : forall A l sz (i0 : A) x,
    In x (list_chunk l sz i0) -> length x = sz.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
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
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma list_chunk_spec' : forall A l i n (e0 : A) b0,
    n <> 0 -> b0 = repeat e0 n ->
    selN (list_chunk l n e0) i b0 
    = setlen (skipn (i * n) l) n e0.
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma list_chunk_spec : forall l i,
    selN (list_chunk l items_per_val item0) i block0 
    = setlen (skipn (i * items_per_val) l) items_per_val item0.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Lemma nopad_list_chunk'_spec: forall A nr i (l : list A) sz (b0 : list A),
    i < nr ->
    selN (nopad_list_chunk' l sz nr) i b0 = firstn sz (skipn (i * sz) l).
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma nopad_list_chunk_spec: forall l i,
    i < divup (length l) items_per_val ->
    selN (nopad_list_chunk l items_per_val) i block0 =
    firstn items_per_val (skipn (i * items_per_val) l).
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma list_chunk'_skipn_1: forall A n l k (e0 : A),
    list_chunk' (skipn n l) n e0 (k - 1) = skipn 1 (list_chunk' l n e0 k).
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma list_chunk_skipn_1 : forall A n l (e0 : A),
    list_chunk (skipn n l) n e0 = skipn 1 (list_chunk l n e0).
Proof.
(* skipped proof tokens: 171 *)
Admitted.
Lemma skipn_list_chunk_skipn_eq : forall A i l n (e0 : A),
    skipn i (list_chunk l n e0) = list_chunk (skipn (i * n) l) n e0.
Proof.
(* skipped proof tokens: 76 *)
Admitted.
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
Proof.
(* skipped proof tokens: 29 *)
Admitted.
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
Proof.
(* skipped proof tokens: 93 *)
Admitted.
Lemma list_chunk_app: forall A na sz a b (def : A),
    sz <> 0 ->
    length a = sz * na ->
    list_chunk (a ++ b) sz def = list_chunk a sz def ++ list_chunk b sz def.
Proof.
(* skipped proof tokens: 90 *)
Admitted.
Definition ipack items := map block2val (list_chunk items items_per_val item0).
Definition nopad_ipack items := map block2val (nopad_list_chunk items items_per_val).
Definition iunpack (r : itemlist) (v : valu) : itemlist :=
    r ++ (val2block v).
Lemma well_formed_app_iff : forall A (a b : list (Rec.data A)) ,
     Forall Rec.well_formed (a ++ b)
     <-> Forall Rec.well_formed a /\ Forall Rec.well_formed b.
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma nils_length : forall n,
    length (nils n) = n.
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma ipack_length : forall items,
    length (ipack items) = divup (length items) items_per_val.
Proof.
(* skipped proof tokens: 30 *)
Admitted.
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
Proof.
(* skipped proof tokens: 51 *)
Admitted.
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
Proof.
(* skipped proof tokens: 35 *)
Admitted.
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
Proof.
(* skipped proof tokens: 271 *)
Admitted.
Lemma ipack_iunpack_one : forall (a : valu),
    [ a ] = ipack (iunpack [] a).
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Lemma iunpack_length : forall init nr a,
    length init = nr ->
    length (iunpack init a) = nr + items_per_val.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma fold_left_iunpack_length' : forall l init nr,
    length init = nr ->
    length (fold_left iunpack l init) = nr + (length l) * items_per_val.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma fold_left_iunpack_length : forall l,
    length (fold_left iunpack l []) = (length l) * items_per_val.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma ipack_iunpack : forall l,
    (forall l', Forall (@Rec.well_formed itemtype) l') ->
    l = ipack (fold_left iunpack l []).
Proof.
(* skipped proof tokens: 131 *)
Admitted.
Lemma ipack_nopad_ipack_eq : forall x,
    ipack x = nopad_ipack x.
Proof.
(* skipped proof tokens: 186 *)
Admitted.
Lemma mod_lt_length_firstn_skipn : forall A ix (l : list A),
    ix < length l ->
    ix mod items_per_val < length (firstn items_per_val (skipn (ix / items_per_val * items_per_val) l)).
Proof.
(* skipped proof tokens: 82 *)
Admitted.
Lemma ipack_selN_divmod : forall items ix,
    (@Forall block) Rec.well_formed (list_chunk items items_per_val item0) ->
    ix < length items ->
    selN (val2block (selN (ipack items) (ix / items_per_val) $0)) (ix mod items_per_val) item0
    = selN items ix item0.
Proof.
(* skipped proof tokens: 94 *)
Admitted.
Lemma list_chunk_updN_divmod : forall items ix e,
    ix < length items ->
    updN (list_chunk items items_per_val item0) (ix / items_per_val)
      (updN (selN (list_chunk items items_per_val item0) (ix / items_per_val) block0)
        (ix mod items_per_val) e) =
    list_chunk (updN items ix e) items_per_val item0.
Proof.
(* skipped proof tokens: 254 *)
Admitted.
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
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Lemma repeat_ipack_item0 : forall n,
    repeat $0 n = ipack (repeat item0 (n * items_per_val)).
Proof.
(* skipped proof tokens: 88 *)
Admitted.
Lemma Forall_wellformed_updN : forall (items : list item) a v,
    Forall Rec.well_formed items ->
    Rec.well_formed v ->
    Forall Rec.well_formed (updN items a v).
Proof.
(* skipped proof tokens: 40 *)
Admitted.
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
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Definition ifind_block (cond : item -> addr -> bool) (vs : block) start : option (addr * item ) :=
    ifind_list cond vs start.
Lemma ifind_result_inbound :  forall len bn items cond r,
    Forall Rec.well_formed items ->
    bn < len ->
    ifind_block cond (val2block (fst (selN (synced_list (ipack items)) bn ($0, nil))))
      (bn * items_per_val) = Some r ->
    length items = len * items_per_val ->
    fst r < length items.
Proof.
(* skipped proof tokens: 148 *)
Admitted.
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
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Theorem block2val_updN_val2block_equiv : forall v idx item,
    idx < items_per_val ->
    block2val_updN_val2block v idx item =
    block2val (updN (val2block v) idx item).
Proof.
(* skipped proof tokens: 39 *)
Admitted.
End RADefs.
