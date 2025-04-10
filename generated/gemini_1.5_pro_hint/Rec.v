Require Import Arith List String Lia Bool.
Require Import Word.
Require Import Eqdep_dec.
Require Import Array.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import ListUtils.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.
Module Rec.
Inductive type :=
    | WordF : nat -> type
    | ArrayF : type -> nat -> type
    | RecF : list (string * type) -> type.
Definition rectype := list (string * type).
Fixpoint type_rect_nest
      (P : type -> Type)
      (Q : rectype -> Type)
      (wordc : forall n, P (WordF n))
      (arrayc : forall t, P t -> forall n, P (ArrayF t n))
      (recc : forall rt : rectype, Q rt -> P (RecF rt))
      (nilc : Q nil)
      (consc : forall n t rt, P t -> Q rt -> Q ((n,t)::rt))
      (t : type) : P t :=
    match t as t0 return (P t0) with
    | WordF n => wordc n
    | ArrayF t' n => arrayc t' (type_rect_nest P Q wordc arrayc recc nilc consc t') n
    | RecF rt => recc rt (list_rect Q nilc (fun p r =>
        let (n, t') as p return (Q r -> Q (p :: r)) := p
        in consc n t' r (type_rect_nest P Q wordc arrayc recc nilc consc t')) rt)
    end.
Fixpoint data (t : type) : Type :=
    match t with
    | WordF l => word l
    | ArrayF t' _ => list (data t')
    | RecF rt =>
      (fix recdata (t : list (string * type)) : Type :=
        match t with
        | [] => unit
        | (_, ft) :: t' => data ft * recdata t'
        end%type) rt
    end.
Definition recdata ft := data (RecF ft).
Fixpoint len (t : type) : nat :=
    match t with
    | WordF l => l
    | ArrayF t' l => l * len t'
    | RecF rt =>
      (fix reclen (t : rectype) : nat :=
        match t with
        | [] => 0
        | (_, ft) :: t' => len ft + reclen t'
        end) rt
    end.
Fixpoint well_formed {t : type} : data t -> Prop :=
    match t as t return (data t -> Prop) with
    | WordF _ => fun _ => True
    | ArrayF _ l => fun v => Datatypes.length v = l /\ Forall well_formed v
    | RecF rt =>
      (fix well_formed' {rt : rectype} : data (RecF rt) -> Prop :=
        match rt as rt return (data (RecF rt) -> Prop) with
        | [] => fun _ => True
        | (_, ft) :: t' => fun r =>
          let (r0, r') := r in well_formed r0 /\ well_formed' r'
        end) rt
    end.
Theorem firstn_well_formed : forall (ft:type) n1 n2 w,
    @well_formed (ArrayF ft (n1+n2)) w ->
    @well_formed (ArrayF ft n1) (firstn n1 w).
(* hint proof tokens: 71 *)
Proof.
    intros.
    unfold well_formed in *.
    inversion H.
    split.
    rewrite firstn_length_l; lia.
    rewrite Forall_forall; intros.
    apply in_firstn_in in H2.
    rewrite Forall_forall in H1.
    apply H1.
    assumption.
  Qed.
Theorem firstn_l_well_formed : forall (ft:type) n n' w,
    n <= n' ->
    @well_formed (ArrayF ft n') w ->
    @well_formed (ArrayF ft n) (firstn n w).
(* hint proof tokens: 63 *)
Proof.
    intros.
    unfold well_formed in *.
    inversion H0.
    split.
    rewrite firstn_length_l; lia.
    rewrite Forall_forall in *; intros.
    eapply H2.
    eapply in_firstn_in; eauto.
  Qed.
Theorem skipn_well_formed : forall (ft:type) n1 n2 w,
    @well_formed (ArrayF ft (n1+n2)) w ->
    @well_formed (ArrayF ft n2) (skipn n1 w).
(* hint proof tokens: 70 *)
Proof.
    intros.
    unfold well_formed in *.
    inversion H.
    split.
    rewrite skipn_length; lia.
    rewrite Forall_forall; intros.
    apply in_skipn_in in H2.
    rewrite Forall_forall in H1.
    apply H1.
    assumption.
  Qed.
Theorem tl_well_formed : forall (ft:type) n d w,
    @well_formed (ArrayF ft (S n)) (d::w) ->
    @well_formed (ArrayF ft n) w.
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Theorem empty_well_formed : forall (ft:type) w,
    List.length w = 0 ->
    @well_formed (ArrayF ft 0) w.
(* hint proof tokens: 34 *)
Proof.
    intros.
    unfold well_formed.
    split; auto.
    apply length_nil in H.
    subst.
    auto.
  Qed.
Inductive field_in : rectype -> string -> Prop :=
  | FE : forall t n ft, field_in ((n, ft) :: t) n
  | FS : forall t n n' ft, field_in t n -> field_in ((n', ft) :: t) n.
Lemma empty_field_in : forall n, ~(field_in nil n).
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 14 *)

intros n H; inversion H.
Qed.

Lemma field_in_next : forall t n n' ft, n' <> n -> field_in ((n',ft) :: t) n -> field_in t n.
(* hint proof tokens: 34 *)
Proof.
    intros t n n' ft ne f. inversion f; subst.
    contradiction ne. reflexivity.
    apply H3.
  Qed.
Fixpoint field_type (t : rectype) (n : string) (f : field_in t n) : type :=
    match t as t return (field_in t n -> type) with
    | nil => fun f => match (empty_field_in f) with end
    | (n0, ft0)::_ => fun f =>
      match (string_dec n0 n) with
      | left _ => ft0
      | right ne => field_type (field_in_next ne f)
      end
    end f.
Fixpoint recget {t : rectype} {n : string} (p : field_in t n) (r : recdata t) : data (field_type p) :=
    match t as t return (recdata t -> forall f : field_in t n, data (field_type f)) with
    | [] => fun _ f => match (empty_field_in f) with end
    | (n0, ft0) :: t' =>
      fun r f =>
      match (string_dec n0 n) as s
        return (data
            match s with
            | left _ => ft0
            | right ne => field_type (field_in_next ne f)
            end)
      with
      | left _ => (fst r)
      | right ne => recget (field_in_next ne f) (snd r)
      end
    end r p.
Fixpoint recset {t : rectype} {n : string} (p : field_in t n) (r : recdata t) (v : data (field_type p)) {struct t} : recdata t.
destruct t.
contradiction (empty_field_in p).
destruct p0 as [n0 ft0].
simpl in v.
destruct (string_dec n0 n) as [eq|neq]; constructor.
apply v.
apply (snd r).
apply (fst r).
apply (recset t n (field_in_next neq p) (snd r) v).
Defined.
Theorem set_get_same : forall t n p r v, @recget t n p (recset p r v) = v.
(* hint proof tokens: 62 *)
Proof.
    induction t; intros.
    contradiction (empty_field_in p).
    destruct a as [n0 ft0]. destruct r as [v0 r'].
    simpl in v. simpl. destruct (string_dec n0 n).
    trivial. apply IHt.
  Qed.
Theorem set_get_other : forall t n1 p1 n2 p2 r v, n1 <> n2 ->
    recget p1 r = @recget t n1 p1 (@recset t n2 p2 r v).
(* hint proof tokens: 96 *)
Proof.
    induction t; intros n1 p1 n2 p2 r v neq.
    contradiction (empty_field_in p1).
    destruct a as [n0 ft0]. destruct r as [v0 r'].
    simpl in v. simpl.
    destruct (string_dec n0 n2); destruct (string_dec n0 n1);
      subst; trivial.
    contradiction neq. auto.
    apply IHt. assumption.
  Qed.
Fixpoint fieldp (t : rectype) (n : string) : option (field_in t n) :=
    match t as t return (option (field_in t n)) with
    | [] => None
    | (n0, l0) :: t' =>
      match (string_dec n0 n) with
      | left e =>
          eq_rec_r
            (fun n1 => option (field_in ((n1, l0) :: t') n))
            (Some (FE t' n l0)) e
      | right _ =>
        match (fieldp t' n) with
        | Some f => Some (FS n0 l0 f)
        | None => None
        end
      end
    end.
Definition recget' {t : rectype} (n : string) (r : recdata t) :=
    match fieldp t n as fp
          return (match fp with 
                    | Some p => data (field_type p)
                    | None => True
                  end) with
      | Some p => recget p r
      | None => I
    end.
Definition recset' {t : rectype} (n : string) (r : recdata t) :=
    match fieldp t n as fp
          return (recdata t -> match fp with
                    | Some p => data (field_type p) -> recdata t
                    | None => True
                  end) with
      | Some p => fun r v => recset p r v
      | None => fun _ => I
    end r.
Fixpoint to_word {ft : type} : data ft -> word (len ft) :=
    match ft as ft return (data ft -> word (len ft)) with
    | WordF n => fun v => v
    | ArrayF ft0 n as ft =>
      (fix arrayf2word n v :=
        match n as n0 return (data (ArrayF ft0 n0) -> word (len (ArrayF ft0 n0))) with
        | 0 => fun _ => $0
        | S n0 => fun v =>
          match v with
          | nil => $0
          | v0 :: v' => combine (to_word v0) (arrayf2word n0 v')
          end
        end v) n
    | RecF t =>
      (fix rec2word {t : rectype} (r : recdata t) : word (len (RecF t)) :=
        match t as t return recdata t -> word (len (RecF t)) with
        | nil => fun _ => $0
        | (_, _) :: _ => fun r =>
          let (v, r') := r in combine (to_word v) (rec2word r')
        end r) t
    end.
Fixpoint of_word {ft : type} : word (len ft) -> data ft :=
    match ft as ft return (word (len ft) -> data ft) with
    | WordF n => fun w => w
    | ArrayF ft0 n as ft =>
      (fix word2arrayf n w :=
        match n as n return (word (len (ArrayF ft0 n)) -> data (ArrayF ft0 n)) with
        | 0 => fun _ => []
        | S n' => fun w0 =>
          (of_word (split1 (len ft0) _ w0)) ::
          (word2arrayf n' (split2 (len ft0) _ w0))
        end w) n
    | RecF t =>
      (fix word2rec (t : rectype) (w : word (len (RecF t))) : recdata t :=
        match t as t return word (len (RecF t)) -> recdata t with
        | nil => fun _ => tt
        | (_, ft) :: t' => fun w =>
          (of_word (split1 (len ft) (len (RecF t')) w), 
           word2rec t' (split2 (len ft) (len (RecF t')) w))
        end w) t
  end.
Theorem to_of_id : forall ft w, to_word (@of_word ft w) = w.
Proof.
(* skipped proof tokens: 84 *)
Admitted.
Hint Rewrite to_of_id.
Theorem of_to_id : forall ft v, well_formed v -> of_word (@to_word ft v) = v.
Proof.
(* skipped proof tokens: 479 *)
Admitted.
Theorem to_eq : forall ft a b,
    @to_word ft a = @to_word ft b ->
    well_formed a ->
    well_formed b ->
    a = b.
Proof.
(* skipped proof tokens: 47 *)
Admitted.
Theorem of_eq : forall ft a b,
    @of_word ft a = @of_word ft b ->
    a = b.
Proof.
(* skipped proof tokens: 41 *)
Admitted.
Lemma of_word_empty : forall t n w,
    n = 0 ->
    @of_word (ArrayF t n) w = nil.
(* hint proof tokens: 37 *)
Proof.
    intros.
    generalize w.
    rewrite H.
    intros.
    simpl in w0.
    apply length_nil.
    reflexivity.
  Qed.
Theorem of_word_length : forall ft w, well_formed (@of_word ft w).
(* hint proof tokens: 92 *)
Proof.
    einduction ft using type_rect_nest.
    simpl. trivial.
    simpl. induction n.
    split; trivial.
    intro w.
    edestruct IHn.
    split. simpl. rewrite H. trivial.
    simpl. constructor. apply IHt. assumption.
    apply IHt.
    simpl. trivial.
    simpl. intro w. split.
    apply IHt. apply IHt0.
  Qed.
Theorem of_word_well_formed : forall (ft:type) w,
    well_formed (@of_word ft w).
Proof.
(* skipped proof tokens: 13 *)
Admitted.
Theorem array_of_word_length : forall ft n w,
    List.length (@of_word (ArrayF ft n) w) = n.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Theorem to_word_append_any: forall sz l n l2,
    Datatypes.length l > n -> @to_word (ArrayF (WordF sz) n) (app l l2) = @to_word (ArrayF (WordF sz) n) l.
Proof.
(* skipped proof tokens: 38 *)
Admitted.
Theorem to_word_append_zeroes: forall sz l n m,
    @to_word (ArrayF (WordF sz) n) (app l (repeat $0 m)) = @to_word (ArrayF (WordF sz) n) l.
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Arguments of_word : simpl never.
Arguments to_word : simpl never.
Definition middle (low mid high : nat) (w : word (low + (mid + high))) : word mid :=
    split1 mid high (split2 low (mid+high) w).
Lemma word_selN_helper : forall idx l lenft, idx < l ->
    l * lenft = idx * lenft + (lenft + (l * lenft - lenft - idx * lenft)).
(* hint proof tokens: 163 *)
Proof.
    intros.
    rewrite plus_assoc.
    rewrite Nat.add_sub_assoc.
    rewrite <- plus_assoc.
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by lia.
    rewrite Nat.sub_diag; rewrite <- plus_n_O.
    rewrite Nat.add_sub_assoc.
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by lia.
    rewrite Nat.sub_diag; rewrite <- plus_n_O.
    reflexivity.
    replace (lenft) with (1 * lenft) at 1 by lia.
    apply Nat.mul_le_mono_r; lia.
    replace (lenft) with (1 * lenft) at 3 by lia.
    rewrite <- Nat.mul_sub_distr_r.
    apply Nat.mul_le_mono_r; lia.
  Qed.
Definition word_selN {ft : type} {l : nat} (idx : nat) (w : word (len (ArrayF ft l))) : word (len ft).
refine (if lt_dec idx l then _ else $0).
refine (middle (idx * len ft) (len ft) (l * len ft - len ft - idx * len ft) _).
replace (idx * len ft + (len ft + (l * len ft - len ft - idx * len ft))) with (l * len ft).
exact w.
apply word_selN_helper.
apply l0.
Defined.
Theorem word_selN_equiv : forall ft l idx w def, idx < l ->
    of_word (@word_selN ft l idx w) = selN (of_word w) idx def.
Proof.
(* skipped proof tokens: 537 *)
Admitted.
Lemma word_updN_helper1 : forall idx l lenft, idx < l ->
    lenft + (l * lenft - idx * lenft - lenft) = l * lenft - idx * lenft.
Proof.
(* skipped proof tokens: 77 *)
Admitted.
Lemma word_updN_helper2 : forall idx l lenft, idx < l ->
    idx * lenft + (l * lenft - idx * lenft) = l * lenft.
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Definition word_updN {ft : type} {l : nat} (idx : nat) (w : word (len (ArrayF ft l)))
                                             (v : word (len ft)) : word (len (ArrayF ft l)).
refine (if lt_dec idx l then _ else w); simpl in *.
replace (l * len ft) with (idx * len ft + (l * len ft - idx * len ft))
      in * by (apply word_updN_helper2; assumption).
remember (split1 (idx * len ft) (l * len ft - idx * len ft) w) as low; clear Heqlow.
refine (combine low _).
replace (l * len ft - idx * len ft) with (len ft + (l * len ft - idx * len ft - len ft))
      in * by (apply word_updN_helper1; assumption).
rewrite plus_assoc in *.
remember (split2 (idx * len ft + len ft) (l * len ft - idx * len ft - len ft) w) as hi; clear Heqhi.
refine (combine v hi).
Defined.
Theorem word_updN_oob : forall ft l idx w v, idx >= l ->
    @word_updN ft l idx w (to_word v) = w.
(* hint proof tokens: 35 *)
Proof.
    unfold word_updN; simpl; intros.
    destruct (lt_dec idx l); auto.
    exfalso; lia.
  Qed.
Theorem word_updN_equiv : forall ft l idx w v, idx < l ->
    @word_updN ft l idx w (to_word v) = @to_word (ArrayF ft l) (updN (of_word w) idx v).
Proof.
(* skipped proof tokens: 1637 *)
Admitted.
Definition word_mask (l n : nat) (idx : nat) : word (l * n).
destruct l eqn:H.
exact (wzero 0).
exact (wlshift (combine (wones n) (wzero (n0 * n))) (idx * n)).
Defined.
Definition word_selN_shift (l n : nat) (idx : nat) (w : word (l * n)) : word n.
destruct l eqn:H.
exact (wzero n).
exact (split1 n (n0 * n) (wrshift w (idx * n))).
Defined.
Definition word_updN_shift (l n : nat) (idx : nat) (w : word (l * n))
                                             (v : word n) : word (l * n).
destruct l eqn:H.
exact w.
set (v' := zext v (n0 * n)).
set (mask := word_mask (S n0) n idx).
set (shift := n * idx).
set (newmask := wlshift v' shift).
exact ((w ^& (wnot mask)) ^| newmask).
Defined.
Fact word_shift_helper1 : forall n idx off, n + (idx + off) * n = (idx + 1 + off) * n.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Fact word_shift_helper2 : forall n l, l > 0 -> n + (l - 1) * n = l * n.
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Fact word_shift_helper3 : forall a b c, a * c + (c + b * c) = (a + 1 + b) * c.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Fact word_shift_helper4 : forall a b c, (a + 1 + b) * c = a * c + c + b * c.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Theorem word_selN_shift_gt_0 : forall idx off n w,
    word_selN_shift (idx + 1 + off) n idx w = split1 n ((idx + off) * n)
      (eq_rect _ word (wrshift w (idx * n)) _ (eq_sym (word_shift_helper1 n idx off))).
(* hint proof tokens: 57 *)
Proof.
    intros idx off n.
    assert (idx + 1 + off = S (idx + off)) as H by lia.
    generalize_proof.
    rewrite H.
    intros.
    eq_rect_simpl.
    reflexivity.
  Qed.
Theorem eq_rect_combine_dist3 : forall a b c (w : word ((a + 1 + b) * c)),
    let H := word_shift_helper3 a b c in
    let H1 := word_shift_helper4 a b c in
    let w' := eq_rect ((a + 1 + b) * c) word w _ (eq_sym H) in
    let w'' := eq_rect ((a + 1 + b) * c) word w _ H1 in
    w = eq_rect _ word (combine
      (split1 (a * c) _ w')
      (combine
        (middle (a * c) c (b * c) w')
        (split2 (a * c + c) (b * c) w''))) _ H.
(* hint proof tokens: 98 *)
Proof.
    intros.
    generalize dependent H1.
    generalize dependent w.
    generalize dependent H.
    intros H.
    rewrite <- H.
    intros.
    subst w' w''.
    eq_rect_simpl.
    unfold middle.
    rewrite <- combine_split with (w := w).
    repeat f_equal; rewrite combine_split; auto.
    erewrite <- eq_rect_word_match.
    rewrite combine_end.
    reflexivity.
  Qed.
Fact eq_rect_both_helper : forall T (x y z : T), x = y -> z = y -> z = x.
(* hint proof tokens: 13 *)
Proof. intros. subst. reflexivity. Qed.
Theorem eq_rect_both : forall x y z (H1 : x = z) (H2 : y = z) wa wb,
    wa = eq_rect y word wb x (eq_rect_both_helper H1 H2) -> eq_rect x word wa z H1 = eq_rect y word wb z H2.
(* hint proof tokens: 22 *)
Proof.
    intros. subst.
    eq_rect_simpl.
    reflexivity.
   Qed.
Fact split1_eq_rect_combine_partial_helper : forall a b c d (H : a + c = a + b + d), c = b + d.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Theorem split1_eq_rect_combine_partial : forall a b c d H (wa : word a) (wc : word c),
    split1 (a + b) d
      (eq_rect (a + c) word (combine wa wc) (a + b + d) H) =
        combine wa (split1 b d (eq_rect _ word wc _ (split1_eq_rect_combine_partial_helper a b c d H))).
(* hint proof tokens: 73 *)
Proof.
    intros a b c d H.
    assert (c = b + d) by lia; subst c.
    intros.
    erewrite <- split1_combine; f_equal.
    eq_rect_simpl.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    rewrite combine_split.
    reflexivity.
  Qed.
Fact combine_eq_rect_combine_helper : forall a b c d, a + b = c -> a + (b + d) = c + d.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Fact combine_eq_rect_combine : forall a b c d H (wa : word a) (wb : word b) (wa' : word d),
    combine (eq_rect (a + b) word (combine wa wb) c H) wa' =
    eq_rect _ word (combine wa (combine wb wa')) _ (combine_eq_rect_combine_helper a b d H).
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Fact split2_eq_rect_combine : forall a b c H (wa : word a) (wc : word c),
    split2 a b (eq_rect (a + c) word (combine wa wc) (a + b) H) =
    eq_rect c word wc b (plus_reg_l c b a H).
Proof.
(* skipped proof tokens: 42 *)
Admitted.
Theorem word_selN_shift_eq_middle : forall idx off n w,
    @word_selN_shift (idx + 1 + off) n idx w = middle (idx * n) n (off * n)
      (eq_rec _ word w _ (eq_sym (word_shift_helper3 idx off n))).
(* hint proof tokens: 186 *)
Proof.
    intros.
    eq_rect_simpl.
    rewrite word_selN_shift_gt_0.
    generalize_proof.
    replace ((idx + off) * n) with (idx * n + off * n) by lia.
    intros HH.
    unfold wrshift.
    eq_rect_simpl.
    erewrite combine_eq_rect2.
    rewrite eq_rect_combine_dist3 with (w := w); eq_rect_simpl.
    erewrite combine_eq_rect_combine; eq_rect_simpl.
    erewrite split2_eq_rect_combine; eq_rect_simpl.
    repeat erewrite combine_assoc, eq_rect_word_match; eq_rect_simpl.
    unfold middle.
    repeat progress (rewrite eq_rect_combine ||
                     rewrite split1_combine  ||
                     rewrite split2_combine).
    reflexivity.
    Unshelve.
    all : lia.
  Qed.
Theorem word_selN_shift_equiv : forall ft l idx w, idx < l ->
    @word_selN ft l idx w = @word_selN_shift l (len ft) idx w.
(* hint proof tokens: 148 *)
Proof.
    intros.
    generalize dependent w.
    remember (l - idx - 1) as off.
    assert (l = (idx + 1+ off)) by lia.
    subst l.
    intros w.
    unfold word_selN.
    destruct lt_dec; try lia.
    erewrite word_selN_shift_eq_middle.
    generalize dependent (word_selN_helper (len ft) l).
    replace ((idx + 1 + off) * len ft - len ft - idx * len ft) with (off * len ft) by lia.
    intros HH.
    f_equal.
    apply eq_rect_both; eq_rect_simpl.
    reflexivity.
  Qed.
Definition word_selN' {ft : type} {l : nat} (idx : nat) (w : word (len (ArrayF ft l)))
    : word (len ft) := @word_selN_shift l (len ft) idx w.
Theorem word_selN'_equiv : forall ft l idx w def, idx < l ->
    of_word (@word_selN' ft l idx w) = selN (of_word w) idx def.
(* hint proof tokens: 38 *)
Proof.
    intros.
    unfold word_selN'.
    rewrite <- word_selN_shift_equiv; auto.
    apply word_selN_equiv; auto.
  Qed.
Theorem word_updN_shift_l_gt_0 : forall idx off n w v,
    @word_updN_shift (idx + 1 + off) n idx w v = w ^& wnot (word_mask (idx + 1 + off) n idx) ^| wlshift (
      eq_rect _ word (zext v ((idx + off) * n)) _ (word_shift_helper1 n idx off)) (idx * n).
(* hint proof tokens: 77 *)
Proof.
    unfold word_updN_shift.
    intros idx off n.
    generalize dependent (word_shift_helper1 n idx off).
    replace (idx + 1 + off) with (S (idx + off)) by lia.
    intros.
    eq_rect_simpl.
    f_equal.
    f_equal.
    apply mult_comm.
  Qed.
Theorem word_mask_l_gt_0 : forall l n idx (H : l > 0),
    @word_mask l n idx = wlshift (eq_rect _ word (combine (wones n) (wzero ((l - 1) * n))) _
      (word_shift_helper2 n H))
      (idx * n).
Proof.
(* skipped proof tokens: 65 *)
Admitted.
Theorem wnot_word_mask_l_gt_0 : forall off n idx,
    wnot (@word_mask (idx + 1 + off) n idx) = eq_rec _ word (
    combine (wones (idx * n)) (combine (wzero n) (wones (off * n)))) ((idx + 1 + off) * n)
      (word_shift_helper3 idx off n).
Proof.
(* skipped proof tokens: 185 *)
Admitted.
Lemma wand_wnot_word_mask_w : forall idx off n w,
    let H := word_shift_helper3 idx off n in
    let w' := eq_rect _ word w (idx * n + (n + off * n)) (eq_sym H) in
    let w'' := eq_rect _ word w (idx * n + n + off * n) (word_shift_helper4 idx off n) in
    w ^& wnot (word_mask (idx + 1 + off) n idx) = eq_rec _ word (
      combine (split1 (idx * n) _ w') (combine (wzero n) (split2 (idx * n + n) _ w''))) _ H.
Proof.
(* skipped proof tokens: 109 *)
Admitted.
Theorem word_updN_shift_abs : forall off idx n w v,
    let H := word_shift_helper3 idx off n in
    let H1 := word_shift_helper4 idx off n in
    let w' := eq_rec _ word w _ (eq_sym H) in
    let w'' := eq_rec _ word w _ H1 in
    @word_updN_shift (idx + 1 + off) n idx w v = eq_rec _ word (
      combine (split1 (idx * n) (n + off * n) w')
      (combine v (split2 (idx * n + n) (off * n) w''))) _ H.
Proof.
(* skipped proof tokens: 290 *)
Admitted.
Fact word_updN_abs_helper : forall idx off, idx < idx + 1 + off.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Theorem word_updN_abs : forall idx off ft w v,
    let H := word_shift_helper3 idx off (len ft) in
    let H1 := word_shift_helper4 idx off (len ft) in
    let w' := eq_rec _ word w _ (eq_sym H) in
    let w'' := eq_rec _ word w _ H1 in
    @word_updN ft (idx + 1 + off) idx w v = eq_rec _ word (
      combine (split1 (idx * len ft) (len ft + off * len ft) w')
        (combine v (split2 (idx * len ft + len ft) (off * len ft) w''))) _ H.
(* hint proof tokens: 164 *)
Proof.
    unfold word_updN; simpl.
    intros.
    destruct lt_dec; try lia.
    repeat eexists.
    eq_rect_simpl; apply eq_rect_both.
    rewrite eq_rect_word_offset; eq_rect_simpl.
    rewrite eq_rect_combine; f_equal.
    + erewrite eq_rect_split1_eq2.
      eq_rect_simpl; f_equal.
      apply eq_rect_both.
      eq_rect_simpl; reflexivity.
    + apply eq_rect_both.
      rewrite eq_rect_combine.
      rewrite eq_rect_split2.
      eq_rect_simpl.
      repeat (try reflexivity; f_equal; eq_rect_simpl; try apply eq_rect_both).
    Unshelve.
    all : simpl; lia.
  Qed.
Theorem word_updN_shift_equiv : forall l idx ft w v, idx < l ->
    @word_updN_shift l (len ft) idx w v = @word_updN ft l idx w v.
Proof.
(* skipped proof tokens: 74 *)
Admitted.
Definition word_updN' {ft : type} {l : nat} (idx : nat) (w : word (len (ArrayF ft l)))
            (v : word (len ft)) : word (len (ArrayF ft l)) := @word_updN_shift l (len ft) idx w v.
Theorem word_updN'_equiv : forall ft l idx w v, idx < l ->
    @word_updN' ft l idx w (to_word v) = @to_word (ArrayF ft l) (updN (of_word w) idx v).
(* hint proof tokens: 40 *)
Proof.
    intros.
    unfold word_updN'.
    rewrite word_updN_shift_equiv; auto.
    apply word_updN_equiv; auto.
  Qed.
Program Fixpoint word_concat {ft : type} (items : list (word (len ft)))
    : word ((len ft) * (List.length items)) :=
    match items with
    | nil => $0
    | m :: rest => combine m (@word_concat ft rest)
    end.
Next Obligation.
abstract nia.
Defined.
Fixpoint reczero (ft : type) : (data ft).
Proof.
    destruct ft.
    - exact ($ 0).
    - apply repeat.
      apply reczero.
      exact n.
    - induction l; cbn.
      exact tt.
      destruct a.
      constructor; eauto.
  Qed.
Theorem of_word_zero_list : forall ft n,
    @Rec.of_word (ArrayF ft n) $0 = repeat (Rec.of_word $0) n.
Proof.
(* original proof tokens: 51 *)
simpl. induction n; intros; auto. simpl. f_equal; auto.
(* No more tactics to try *)
Admitted.

Theorem of_word_zero_rec : forall ft,
    @Rec.of_word (RecF ft) $0 = (fix reczero (l : list (string * type)) :
      ((fix recdata (t : list (string * type)) : Type :=
                match t with
                | [] => unit
                | (_, ft1) :: t' => (data ft1 * recdata t')%type
                end) l)
      :=
      match l with
      | nil => tt
      | x :: l => let '(_, x) := x in (@Rec.of_word x $0, (reczero l))
      end) ft.
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Theorem of_word_zero_reczero: forall ft,
    Rec.of_word $0 = reczero ft.
(* hint proof tokens: 66 *)
Proof.
    intros.
    einduction ft using type_rect_nest.
    auto.
    rewrite of_word_zero_list.
    rewrite IHt.
    eauto.
    rewrite of_word_zero_rec.
    apply IHt.
    cbn; auto.
    cbn. f_equal; auto.
  Qed.
Lemma len_add' : forall t n m,
    len (ArrayF t n) + len (ArrayF t m) = len (ArrayF t (n+m)).
(* hint proof tokens: 16 *)
Proof.
    intros.
    simpl.
    nia.
  Qed.
Lemma combine_0 : forall (v: word 0) n (w: word n),
    combine v w = w.
(* hint proof tokens: 15 *)
Proof.
    intros.
    shatterer.
  Qed.
Definition len_add {t n m}
    (v:word (len (ArrayF t n) + len (ArrayF t m))) : word (len (ArrayF t (n+m))).
rewrite len_add' in v.
exact v.
Defined.
Definition len_split {t n m}
    (v:word (len (ArrayF t (n+m)))) : word (len (ArrayF t n) + len (ArrayF t m)).
rewrite <- len_add' in v.
exact v.
Defined.
Lemma of_word_cons : forall t n (w: word (len (ArrayF t (S n)))),
    of_word w = (of_word (split1 (len t) (n * len t) w)) ::
      (@of_word (ArrayF t n) (split2 (len t) (n * len t) w)).
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Theorem combine_app' : forall (t:type) (n m:nat) H
    (v : word (len (ArrayF t n))) (w : word (len (ArrayF t m))),
    app (of_word v) (of_word w) = of_word (eq_rect (len (ArrayF t n) + len (ArrayF t m))
      (fun n => word n)
      (combine v w)
      (len (ArrayF t (n+m))) H).
(* hint proof tokens: 206 *)
Proof.
    intros.
    induction n.
    simpl.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    rewrite combine_0; reflexivity.
    simpl len in *.
    rewrite of_word_cons.
    simpl.
    erewrite IHn.
    rewrite of_word_cons.

    rewrite <- combine_split with (sz1:=len t) (sz2:=n * len t) (w := v).
    f_equal.
    rewrite split1_combine.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    unfold eq_rec.
    rewrite eq_rect_nat_double.
    rewrite eq_rect_combine.
    rewrite split1_combine.
    reflexivity.

    rewrite split2_combine.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    unfold eq_rec.
    rewrite eq_rect_nat_double.
    rewrite eq_rect_combine.
    rewrite split2_combine.
    f_equal.

    Unshelve.
    all: lia.
  Qed.
Theorem combine_app : forall (t:type) (n m:nat)
    (v : word (len (ArrayF t n))) (w : word (len (ArrayF t m))),
    app (of_word v) (of_word w) = of_word (len_add (combine v w)).
Proof.
(* skipped proof tokens: 20 *)
Admitted.
Theorem cons_to_word : forall (t:type) (n:nat)
    d v,
    @to_word (ArrayF t (S n)) (d :: v) =
      combine (to_word d) (@to_word (ArrayF t n) v).
(* hint proof tokens: 16 *)
Proof.
    intros.
    inversion t; auto.
  Qed.
Theorem split1_firstn : forall t n m
    (w: word (len (ArrayF t (n+m)))) Heq,
    firstn n (of_word w) =
      of_word (split1 (len (ArrayF t n)) (len (ArrayF t m))
        (eq_rect _ word w _ Heq)).
(* hint proof tokens: 171 *)
Proof.
    intros.
    induction n.
    simpl.
    reflexivity.

    simpl plus in *.
    rewrite of_word_cons.
    simpl.
    rewrite of_word_cons.
    unfold eq_rec_r in *.
    f_equal.
    erewrite split1_iter.
    rewrite eq_rect_word_match.
    rewrite eq_rect_nat_double.
    simpl in *.
    f_equal.
    erewrite eq_rect_split1_eq2.
    f_equal.
    erewrite IHn.
    rewrite eq_rect_split2.
    erewrite split1_split2.
    repeat f_equal.
    rewrite eq_rect_word_match.
    rewrite eq_rect_nat_double.
    unfold eq_rec.
    f_equal.
    apply proof_irrelevance.

    Unshelve.
    all: try lia.
    simpl.
    nia.
  Qed.
Theorem split2_skipn : forall t n m
    (w: word (len (ArrayF t (n+m)))) Heq,
    skipn n (of_word w) =
      of_word (split2 (len (ArrayF t n)) (len (ArrayF t m))
       (eq_rect _ word w _ Heq)).
Proof.
(* skipped proof tokens: 126 *)
Admitted.
End Rec.
Notation "r :-> n" := (Rec.recget' n r) (at level 20).
Notation "r :=> n := v" := (Rec.recset' n r v) (at level 80).
Notation "r .⟦ n ⟧" := (Rec.recget' n r) (at level 8).
Notation "r .⟦ n := v ⟧" := (Rec.recset' n r v) (at level 8).
Declare Reduction compute_rec :=
  cbv [Rec.recget' Rec.recget Rec.recset' Rec.recset Rec.fieldp
       String.string_dec String.string_rec String.string_rect
       Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
       sumbool_rec sumbool_rect
       bool_dec bool_rec bool_rect
       eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind].
Tactic Notation "rec_cbv" "in" hyp(H) :=
  cbv [Rec.recget' Rec.recget Rec.recset' Rec.recset Rec.fieldp
       String.string_dec String.string_rec String.string_rect
       Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
       sumbool_rec sumbool_rect
       bool_dec bool_rec bool_rect
       eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind] in H;
  cbn [fst snd] in H.
Tactic Notation "rec_cbv" :=
  cbv [Rec.recget' Rec.recget Rec.recset' Rec.recset Rec.fieldp
       String.string_dec String.string_rec String.string_rect
       Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
       sumbool_rec sumbool_rect
       bool_dec bool_rec bool_rect
       eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind];
  cbn [fst snd].
Ltac rec_simpl :=
  repeat match goal with
  | [ H: context [ Rec.recget' ] |- _ ] => rec_cbv in H
  | [ H: context [ Rec.recset' ] |- _ ] => rec_cbv in H
  | [ |- context [ Rec.recget' ] ] => rec_cbv
  | [ |- context [ Rec.recset' ] ] => rec_cbv
  end.
