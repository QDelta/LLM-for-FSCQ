Require Import Arith.
Require Import Word.
Require Import Lia.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import AsyncDisk.
Require Import Bytes.
Require Import DiskSet.
Require Import Pred.
Import EqNotations.
Set Implicit Arguments.
Notation "'byteset'" := (byte * list byte)%type.
Definition list2byteset {A} def (l: list A) : (A * list A) :=
  match l with
  | nil => (def, nil)
  | h::t => (h,t)
  end.
Definition byteset2list {A} (nel: A * list A) : list A := (fst nel)::(snd nel).
Definition byteset0 := (byte0, nil: list byte).
Definition valu0 := bytes2valu  (natToWord (valubytes*8) 0).
Definition valuset0 := (valu0, nil: list valu).
Definition bytes_eq: forall sz, sz <= valubytes -> sz + (valubytes - sz) = valubytes.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Definition bytes2valubytes sz (b: bytes sz): bytes valubytes:=
    let c:= le_dec sz valubytes in
    match c with
    | left l => eq_rect (sz + (valubytes - sz)) bytes 
                  (bcombine b (word2bytes (valubytes-sz) eq_refl $0)) valubytes (bytes_eq l)
    | right _ => $0
    end.
Definition byte2valu b : valu :=  bytes2valu (bytes2valubytes (byte2bytes b)).
Definition list2valu l: valu :=  bytes2valu (bytes2valubytes (bcombine_list l)).
Definition valu2list v : list byte :=  bsplit_list (valu2bytes v).
Definition selN' {A: Type} i def (l: list A): A := selN l i def.
Definition cons' {A} (a: list A) b:= cons b a.
Definition get_sublist {A:Type}(l: list A) (off len: nat) : list A := firstn len (skipn off l).
Fixpoint valuset2bytesets_rec (vs: list (list byte)) i : list (list byte):=
match i with
| O => nil
| S i' => match vs with
    | nil => nil
    | _ =>  (map (selN' 0 byte0) vs)::(valuset2bytesets_rec (map (skipn 1) vs) i')
    end
end.
Definition valuset2bytesets (vs: valuset): list byteset:=
  map (list2byteset byte0) (valuset2bytesets_rec (map valu2list (byteset2list vs)) valubytes).
Fixpoint bytesets2valuset_rec (bs: list (list byte)) i : list (list  byte):=
match i with
| O => nil
| S i' => match bs with
          | nil => nil
          | _ =>  (map (selN' 0 byte0) bs)::(bytesets2valuset_rec (map (skipn 1) bs) i')
          end
end.
Definition bytesets2valuset (bs: list byteset) : valuset :=
	list2byteset valu0 (map (list2valu) (bytesets2valuset_rec (map (@byteset2list byte) bs)
                             (length(byteset2list(selN bs 0 byteset0))))).
Fixpoint merge_bs (lb: list byte) (lbs: list byteset): list byteset :=
match lb with
| nil => nil
| hb :: tb => match lbs with
              | nil => (hb, nil)::(merge_bs tb nil)
              | hbs::tbs => (hb, (fst hbs)::(snd hbs)):: (merge_bs tb tbs)
              end
end.
Definition updN_list (l: list byteset) off (l1: list byte): list byteset :=
(firstn off l)++ (merge_bs l1 (get_sublist l off (length l1))) ++(skipn (off + length l1) l).
Definition ds2llb (ds: diskset) : nelist (list (list byteset)):= 
d_map (map valuset2bytesets) ds.
Definition llb2ds (llb : nelist (list (list byteset))) : diskset :=
d_map (map bytesets2valuset) llb.
Definition dsbupd (ds : diskset) (a : addr) (b : byteset): diskset :=
  llb2ds (d_map (map (fun x : list byteset => x ⟦ a := b ⟧)) (ds2llb ds)).
Fixpoint dsblistupd (ds : diskset) (a : addr) (lb : list byteset): diskset :=
  match lb with
  | nil => ds
  | h::t => dsblistupd (dsbupd ds a h) (a+1) t
  end.
Definition mem_except_range AEQ V (m: @Mem.mem _ AEQ V) a n :=
(fun a' =>
    if (le_dec a a')
      then if (lt_dec a' (a + n))
            then None 
           else m a'
    else m a').
Fixpoint list_split_chunk A k cs (l: list A): list (list A) :=
match k with
  | O => nil
  | S k' => (firstn cs l)::(list_split_chunk k' cs (skipn cs l))
end.
Fixpoint list_zero_pad l a :=
match a with
| O => l
| S a' => list_zero_pad (l ++ (byte0 :: nil)) a'
end.
Definition mod_minus_curb a b: nat:=
match a mod b with
| O => 0
| _ => (b - a mod b)
end.
Fixpoint valu0_pad n: list valu :=
match n with
| O => nil
| S n' => valu0::(valu0_pad n')
end.
Lemma byteset2list2byteset: forall A (l: A * list A) def, 
  list2byteset def (byteset2list l) = l.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma list2byteset2list: forall A (l: list A) def, 
  l<>nil -> byteset2list (list2byteset def l) = l.
(* hint proof tokens: 36 *)
Proof.
  intros.
  unfold list2byteset, byteset2list. 
  destruct l.
  destruct H; reflexivity.
  reflexivity.
Qed.
Lemma valu2list_len : forall v,
 length(valu2list v) = valubytes.
(* hint proof tokens: 32 *)
Proof.
  intros.
  unfold valu2list.
  rewrite bsplit_list_len.
  rewrite valubytes_is.
  reflexivity.
Qed.
Lemma valuset2bytesets_rec_expand: forall i a l,
   i > 0 ->
  valuset2bytesets_rec (a::l) i = 
	(map (selN' 0 byte0) (a::l)):: (valuset2bytesets_rec (map (skipn 1) (a::l)) (i-1)).
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma valuset2bytesets_rec_len: forall i l,  
  l <> nil -> length(valuset2bytesets_rec l i) = i.
(* hint proof tokens: 79 *)
Proof.
  induction i.
  reflexivity.
  destruct l.
  intros.
  destruct H; reflexivity.
  intros.
  rewrite valuset2bytesets_rec_expand.
  replace (S i - 1) with i by lia.
  simpl.
  rewrite IHi.
  reflexivity.
  unfold not; intros; inversion H0.
  lia.
Qed.
Lemma valuset2bytesets_len: forall vs, 
  length(valuset2bytesets vs) = valubytes.
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma le_trans: forall n m k, n <= m -> m <= k -> n <= k.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Fact lt_le_trans: forall n m p, n < m -> m <= p -> n < p.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Lemma le_weaken_l: forall n m k, n + m <= k -> n <= k.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma le_weaken_r: forall n m k, n + m <= k -> m <= k.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Lemma lt_weaken_l: forall n m k, n + m < k -> n < k.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma lt_weaken_r: forall n m k, n + m < k -> m < k.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 11 *)

intros.
lia.
Qed.

Lemma le2lt_l: forall n m k, n + m <= k -> m > 0 -> n < k.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma le2lt_r: forall n m k, n + m <= k -> n > 0 -> m < k.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Lemma mult_ne_O_l: forall n m p, p * n < p * m -> p > 0.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma mult_ne_O_r: forall n m p, n * p < m * p -> p > 0.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma plus_lt_compat_rev: forall n m p, p + n < p + m -> n < m.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Lemma lt_mult_weaken: forall p n m, n * p < m * p  -> n < m.
Proof.
(* original proof tokens: 91 *)
(* generated proof tokens: 29 *)

intros p n m H.
apply Nat.mul_lt_mono_pos_r with (p := p); lia.
Qed.

Lemma le_le_weaken: forall n m p k,
n + m <= p -> k <= m -> n + k <= p.
(* hint proof tokens: 9 *)
Proof. intros.
lia.
Qed.
Lemma le_lt_weaken: forall n m p k,
n + m <= p -> k < m -> n + k < p.
(* hint proof tokens: 9 *)
Proof. intros.
lia.
Qed.
Lemma div_eq: forall m n k, k < m -> (n * m + k)/m = n.
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Lemma some_eq: forall A (x y: A), Some x = Some y <-> x = y.
(* hint proof tokens: 24 *)
Proof.
  split; intros.
  inversion H; reflexivity.
  rewrite H; reflexivity.
Qed.
Lemma concat_hom_selN: forall A (lists: list(list A)) i n k def, 
  Forall (fun sublist => length sublist = k) lists ->
  i < k ->
  selN (concat lists) (n * k + i) def = selN (selN lists n nil) i def.
(* hint proof tokens: 244 *)
Proof.
  induction lists.
  reflexivity.
  intros.
  rewrite Forall_forall in H.
  destruct n.
  simpl.
  apply selN_app1.
  destruct H with (x:= a).
  apply in_eq.
  apply H0.
  destruct H with (x:=a).
  apply in_eq.
  simpl.
  rewrite selN_app2.
  replace (length a + n * length a + i - length a) with (n * length a + i).
  apply IHlists.
  rewrite Forall_forall.
  intros.
  eapply in_cons in H1.
  apply H in H1.
  apply H1.
  apply H0.
  remember (n * length a + i) as x.
  replace (length a + n * length a + i - length a) with (length a + x - length a).
  lia.
  rewrite Heqx.
  lia.
  unfold ge.
  remember (n * length a + i) as x.
  replace (length a + n * length a + i) with (length a + x).
  apply le_plus_l.
  lia.
Qed.
Lemma fst_list2byteset: forall A (l:list A) def, fst(list2byteset def l) =  selN l 0 def.
(* hint proof tokens: 14 *)
Proof. induction l; intros; reflexivity. Qed.
Lemma flat_map_len: forall vs, length(flat_map valuset2bytesets vs) = length(vs) * valubytes.
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma valuset2bytesets_rec_nil: forall i, valuset2bytesets_rec nil i = nil.
(* hint proof tokens: 14 *)
Proof. intros; destruct i; reflexivity. Qed.
Lemma firstn1 : forall A (l:list(list A)), concat(firstn 1 l) = selN l 0 nil.
(* hint proof tokens: 31 *)
Proof.
  intros.
  induction l.
  rewrite firstn_nil.
  reflexivity.
  simpl.
  apply app_nil_r.
Qed.
Lemma cons_eq_destruct: forall A (l1 l2: list A) b1 b2,
  b1 = b2 -> l1 = l2 -> b1::l1 = b2::l2.
Proof.
(* skipped proof tokens: 13 *)
Admitted.
Lemma concat_hom_O: forall A (l: list(list A)) i k,
  Forall (fun sublist : list A => length sublist = k) l ->
  i<= k -> 
  firstn i (concat l) = firstn i (selN l 0 nil).
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma mapfst_maplist2byteset: forall A (l: list (list A)) def,
  map fst (map (list2byteset def) l) = map (selN' 0 def) l.
(* hint proof tokens: 76 *)
Proof.
  intros.
  rewrite map_map.
  unfold selN'.
  replace (fun x : list A => fst (list2byteset def x)) with
    (fun x : list A => selN x 0 def).
  reflexivity.
  apply functional_extensionality.
  intros; symmetry; apply fst_list2byteset.
Qed.
Lemma bcombine_list_contr: forall a l, 
  bcombine (byte2bytes a) (bcombine_list l) = bcombine_list (a::l).
Proof.
(* skipped proof tokens: 11 *)
Admitted.
Lemma word2bytes_preserve: forall sz (b: bytes sz),
  word2bytes sz eq_refl $ (# b) = b.
Proof.
(* skipped proof tokens: 20 *)
Admitted.
Lemma bytes_eq_to_word_eq : forall n m,
    n = m ->
    n * 8 = m * 8.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Lemma eq_rect_bytes_to_word : forall sz sz' (H: sz = sz') b,
    rew [fun n => word (n * 8)] H in b = rew [fun n => word n] (bytes_eq_to_word_eq H) in b.
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Theorem bcombine_0 : forall sz (b: bytes sz) (b': bytes 0) H,
    eq_rect _ bytes (bcombine b b') _ H = b.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma list2valu2list: forall l, length l = valubytes -> valu2list (list2valu l) = l.
(* hint proof tokens: 90 *)
Proof.
  intros.
  unfold valu2list, list2valu.
  rewrite bytes2valu2bytes.

  unfold bytes2valubytes.
  destruct (le_dec (length l) valubytes); try lia.
  simpl.

  generalize_proof.
  rewrite <- H.
  rewrite Nat.sub_diag.
  intros.

  rewrite bcombine_0.
  rewrite list2bytes2list; auto.
Qed.
Lemma valu2list2valu: forall v, list2valu (valu2list v) = v.
(* hint proof tokens: 264 *)
Proof.
  unfold list2valu, valu2list; intros.

  assert (length (bsplit_list (valu2bytes v)) = valubytes).
  rewrite bsplit_list_len; auto.

  unfold bytes2valu.
  eq_rect_simpl.
  rewrite eq_rect_bytes_to_word; eq_rect_simpl.
  unshelve erewrite bytes2list2bytes; auto.

  unfold bytes2valubytes.
  match goal with
  | [ |- context[match ?d with _ => _ end] ] =>
    destruct d
  end; try lia.

  unfold bytes.
  unfold bcombine.
  repeat rewrite eq_rect_bytes_to_word; eq_rect_simpl.
  repeat generalize_proof; intros.
  destruct e.
  simpl.
  generalize_proof.
  rewrite H, Nat.sub_diag; simpl.
  rewrite combine_n_0.
  intros.
  eq_rect_simpl.
  rewrite <- valu2bytes2valu.
  unfold bytes2valu.
  eq_rect_simpl.
  rewrite eq_rect_bytes_to_word; eq_rect_simpl.
  repeat generalize_proof; intros.
  assert (e = e2) by (apply ProofIrrelevance.proof_irrelevance).
  congruence.
Qed.
Lemma cons_simpl: forall A a (l l': list A), l = l' -> (a::l) = (a::l').
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Lemma v2b_rec_nil: forall l i,
  i = length l  ->
  valuset2bytesets_rec (l::nil) i = map (cons' nil) l.
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Lemma length_skip1: forall l i, 
  length l = S i -> 
  length ((fun l : list byte => match l with
                               | nil => nil
                               | _ :: l0 => l0
                               end) l) = i.
(* hint proof tokens: 23 *)
Proof.
  intros.
  destruct l.
  inversion H.
  simpl in H; lia.
Qed.
Lemma mapfst_valuset2bytesets_single: forall w,
map fst (valuset2bytesets (w,nil)) = valu2list w.
(* hint proof tokens: 67 *)
Proof.
	intros.
	unfold valuset2bytesets.
	simpl.
	rewrite v2b_rec_nil.
	rewrite map_map.
	rewrite map_map.
	unfold cons', list2byteset; simpl.
	rewrite map_id.
	reflexivity.
	symmetry; apply valu2list_len.
Qed.
Lemma mapfst_valuset2bytesets_rec: forall i a l,
length a = i ->
  Forall (fun sublist => length sublist = i) l ->
  map fst (map (list2byteset byte0)
     (valuset2bytesets_rec (a::l) i)) = a.
Proof.
(* skipped proof tokens: 149 *)
Admitted.
Lemma mapfst_valuset2bytesets: forall vs,
map fst (valuset2bytesets vs) = valu2list (fst vs).
(* hint proof tokens: 83 *)
Proof.
		intros.
		unfold valuset2bytesets.
		unfold byteset2list; simpl.
		apply mapfst_valuset2bytesets_rec.
		apply valu2list_len.
		rewrite Forall_forall; intros.
		apply in_map_iff in H.
		repeat destruct H.
		apply valu2list_len.
	Qed.
Lemma bsplit1_bsplit_list: forall sz (b: bytes (1 + (sz - 1))),
  (bsplit1 1 (sz - 1) b :: bsplit_list (bsplit2 1 (sz - 1) b)) = bsplit_list b.
(* hint proof tokens: 27 *)
Proof.
  intros.
  simpl.
  unfold bsplit1_dep, bsplit2_dep.
  reflexivity.
Qed.
Lemma merge_bs_nil: forall l,
merge_bs l nil = map (fun x => (x, nil)) l.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma l2b_cons_x_nil: forall l,
map (list2byteset byte0) (map (cons' nil) l)
		= map (fun x => (x, nil)) l.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma valuset2bytesets_rec_cons_merge_bs: forall k a l,
  Forall (fun sublist => length sublist = k) (a::l) ->
 map (list2byteset byte0) (valuset2bytesets_rec (a::l) k) 
 		= merge_bs a (map (list2byteset byte0) (valuset2bytesets_rec l k)).
(* hint proof tokens: 482 *)
Proof.
		induction k; intros.
		simpl.
		rewrite Forall_forall in H.
		assert (In a (a::l)).
		apply in_eq.
		apply H in H0.
		apply length_zero_iff_nil in H0.
		rewrite H0; reflexivity.
		destruct a.
		assert (In nil (nil::l)).
		apply in_eq.
		rewrite Forall_forall in H.
		apply H in H0.
		simpl in H0; inversion H0.
		simpl.
		destruct l.
		simpl.
		rewrite v2b_rec_nil.
		rewrite merge_bs_nil.
		rewrite l2b_cons_x_nil.
		reflexivity.
		assert (In (b::a) ((b::a)::nil)).
		apply in_eq.
		rewrite Forall_forall in H.
		apply H in H0.
		simpl in H0; inversion H0.
		reflexivity.
		simpl.
		rewrite IHk.
		reflexivity.
		rewrite Forall_forall; intros.
		repeat destruct H0.
		assert (In (b::a) ((b::a)::l::l0)).
		apply in_eq.
		rewrite Forall_forall in H.
		apply H in H0.
		simpl in H0; inversion H0.
		reflexivity.
		assert (In l ((b::a)::l::l0)).
		apply in_cons.
		apply in_eq.
		rewrite Forall_forall in H.
		apply H in H0.
		destruct l.
		simpl in H0; inversion H0.
		simpl in H0; inversion H0.
		reflexivity.
		apply in_map_iff in H0.
		repeat destruct H0.
		rewrite Forall_forall in H.
		eapply in_cons in H1.
		eapply in_cons in H1.
		apply H in H1.
		destruct x0.
		simpl in H1; inversion H1.
		simpl in H1; inversion H1.
		reflexivity.
	Qed.
Definition valuset2byteset (vs : list (list byte)) :=
  map (fun i => selN_each vs i byte0) (seq 0 valubytes).
Definition valuset2bytesets' (vs: valuset): list byteset :=
  combine (valu2list (fst vs)) (valuset2byteset (map valu2list (snd vs))).
Definition bytesets2valuset' (l : list byteset) i :=
  let sets := split l in
  (list2valu (fst sets), map (fun i => list2valu (selN_each (snd sets) i byte0)) (seq 0 i)).
Lemma valuset2bytesets_rec_eq_valuset2bytesets: forall vs,
  length vs > 0 ->
  valuset2bytesets_rec vs valubytes = valuset2byteset vs.
(* hint proof tokens: 99 *)
Proof.
  unfold valuset2byteset.
  generalize valubytes.
  induction n; intros; subst; auto.
  destruct vs; cbn [length] in *.
  lia.
  cbn -[skipn selN_each].
  f_equal.
  rewrite <- seq_shift.
  rewrite map_map.
  rewrite IHn by (cbn; lia).
  apply map_ext. intros.
  rewrite selN_each_S. reflexivity.
Qed.
Lemma valuset2bytesets_eq_valuset2bytesets': forall vs,
  valuset2bytesets vs = valuset2bytesets' vs.
Proof.
(* skipped proof tokens: 109 *)
Admitted.
Lemma bytesets2valuset_rec_eq_map: forall n bs,
  length bs > 0 ->
  bytesets2valuset_rec bs n = map (fun i => selN_each bs i byte0) (seq 0 n).
(* hint proof tokens: 89 *)
Proof.
  unfold bytesets2valuset.
  induction n; intros; subst; auto.
  cbn -[skipn].
  destruct bs; cbn [length] in *.
  lia.
  f_equal.
  rewrite <- seq_shift.
  rewrite map_map.
  rewrite IHn by (cbn; lia).
  apply map_ext. intros.
  rewrite selN_each_S. reflexivity.
Qed.
Lemma selN_each_fst_list2byteset: forall T (l : list (T * _)) def,
  selN_each (map byteset2list l) 0 def = fst (split l).
(* hint proof tokens: 50 *)
Proof.
  unfold selN_each.
  induction l; cbn; intros; auto.
  rewrite surjective_pairing with (p := split l).
  destruct a; cbn.
  f_equal.
  eauto.
Qed.
Lemma selN_each_snd_list2byteset: forall T (l : list (T * _)) a def,
  selN_each (map byteset2list l) (S a) def = selN_each (snd (split l)) a def.
(* hint proof tokens: 50 *)
Proof.
  unfold selN_each.
  induction l; cbn; intros; auto.
  rewrite surjective_pairing with (p := split l).
  destruct a; cbn.
  f_equal.
  eauto.
Qed.
Lemma bytesets2valuset_eq_bytesets2valuset': forall bs n,
  Forall (fun b => length (snd b) = n) bs ->
  length bs = valubytes ->
  bytesets2valuset bs = bytesets2valuset' bs n.
Proof.
(* skipped proof tokens: 140 *)
Admitted.
Lemma valuset2bytesets2valuset: forall vs,
  bytesets2valuset (valuset2bytesets vs) = vs.
(* hint proof tokens: 327 *)
Proof.
  intros.
  rewrite valuset2bytesets_eq_valuset2bytesets'.
  destruct vs; cbn.
  erewrite bytesets2valuset_eq_bytesets2valuset' with (n := length l).
  cbv [bytesets2valuset' valuset2bytesets'].
  rewrite combine_split. cbn.
  rewrite valu2list2valu.
  f_equal.
  induction l; cbn; auto.
  f_equal.
  unfold valuset2byteset.
  rewrite map_map. cbn.
  rewrite map_selN_seq.
  apply valu2list2valu.
  rewrite valu2list_len. auto.
  rewrite <- seq_shift.
  rewrite map_map.
  cbn.
  rewrite <- IHl at 2.
  apply map_ext. intros.
  f_equal.
  unfold valuset2byteset, selN_each.
  repeat rewrite map_map.
  reflexivity.
  rewrite valu2list_len.
  unfold valuset2byteset.
  autorewrite with list. auto.
  unfold valuset2bytesets', valuset2byteset. cbn.
  apply Forall_forall. intros x H.
  destruct x; cbn in *.
  apply in_combine_r in H.
  rewrite in_map_iff in *. deex.
  autorewrite with lists. auto.
  unfold valuset2bytesets', valuset2byteset. cbn.
  autorewrite with lists.
  rewrite seq_length.
  rewrite valu2list_len.
  apply Nat.min_id.
Qed.
Fact updN_list_nil: forall l2 l1 a,
  l1 <> nil -> updN_list l1 a l2 = nil -> l2 = nil.
Proof.
(* skipped proof tokens: 76 *)
Admitted.
Fact skipn_not_nil: forall A (l: list A) n,
  n < length l -> skipn n l <> nil.
Proof.
(* skipped proof tokens: 48 *)
Admitted.
Fact b2v_rec_nil: forall i bn,
  bytesets2valuset_rec bn i = nil -> i = 0 \/ bn = nil.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Fact d_map_d_map: forall A B C (a: A) (l: list A) (f: A -> B) (g: B -> C),
d_map g (d_map f (a,l)) = d_map (fun x => g(f x)) (a, l).
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma mod_Sn_n_1: forall a, a >1 -> (a + 1) mod a = 1.
(* hint proof tokens: 39 *)
Proof.
intros.
rewrite <- Nat.add_mod_idemp_l; try lia.
rewrite Nat.mod_same; simpl; try lia.
apply Nat.mod_1_l; auto.
Qed.
Lemma le_mult_weaken: forall p n m, p > 0 -> n * p <= m * p  -> n <= m.
(* hint proof tokens: 91 *)
Proof.
  assert(A: forall x, 0 * x = 0). intros. lia.
  induction n. intros.
  destruct m.
  lia.
  lia. intros.
  destruct m.
  inversion H0.
  apply plus_is_O in H2.
  destruct H2.
  lia.
  apply le_n_S.
  apply IHn.
  auto.
  simpl in H0.
  lia.
Qed.
Fact vs2bs_selN_O: forall l,
selN (valuset2bytesets l) 0 byteset0 = (list2byteset byte0 (map (selN' 0 byte0) (map valu2list (byteset2list l)))).
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Lemma updN_eq: forall A v v' a (l: list A), v = v' -> updN l a v  = updN l a v'.
(* hint proof tokens: 13 *)
Proof. intros; subst; reflexivity. Qed.
Lemma skipn_concat_skipn: forall A j i k (l: list (list A)) def,
i <= k -> j < length l -> Forall (fun sublist : list A => length sublist = k) l ->
skipn i (concat (skipn j l)) = skipn i (selN l j def) ++ concat (skipn (S j) l).
(* hint proof tokens: 85 *)
Proof. induction j; destruct l; intros; simpl.
inversion H0.
apply skipn_app_l.
rewrite Forall_forall in H1.
destruct H1 with (x:= l).
apply in_eq.
lia.
inversion H0.
erewrite IHj.
reflexivity.
eauto.
simpl in H0; lia.
eapply Forall_cons2.
eauto.
Qed.
Fact map_1to1_eq: forall A B (f: A -> B) (l l': list A), 
  (forall x y, f x = f y -> x = y) -> 
  map f l = map f l' ->
  l = l'.
(* hint proof tokens: 106 *)
Proof.
  induction l; intros.
  simpl in H0; symmetry in H0.
  eapply map_eq_nil in H0.
  eauto.
  destruct l'.
  rewrite map_cons in H0; simpl in H0.
  inversion H0.
  repeat rewrite map_cons in H0.
  inversion H0.
  apply H in H2.
  rewrite H2.
  eapply IHl in H.
  apply cons_simpl.
  eauto.
  eauto.
Qed.
Fact map_eq: forall A B (f: A -> B) (l l': list A), 
  l = l' ->
  map f l = map f l'.
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 26 *)

Proof.
  intros A B f l l' H.
  rewrite H.
  reflexivity.
Qed.

Fact minus_eq_O: forall n m, n >= m -> n - m = 0 -> n = m.
Proof.
(* original proof tokens: 39 *)
(* generated proof tokens: 17 *)

intros n m Hge Heq.
lia.
Qed.

Fact valubytes_ne_O: valubytes <> 0.
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Fact divmult_plusminus_eq:forall n m, m <> 0 ->
   m + n / m * m = n + (m - n mod m).
(* hint proof tokens: 114 *)
Proof.
intros.   
rewrite Nat.add_sub_assoc.
replace (n + m - n mod m) 
    with (m + n - n mod m) by lia.
rewrite <- Nat.add_sub_assoc.
rewrite Nat.add_cancel_l with (p:= m); eauto.
rewrite Nat.mod_eq; eauto.
rewrite Rounding.sub_sub_assoc.
apply Nat.mul_comm.
apply Nat.mul_div_le; eauto.
apply Nat.mod_le; eauto.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound; eauto.
Qed.
Fact le_minus_divmult: forall n m k, m <> 0 ->
    n - (m - k mod m) - (n - (m - k mod m)) / m * m <= m.
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Fact grouping_minus: forall n m k a, n - (m - k + a) = n - (m - k) - a.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Lemma mod_dem_neq_dem: forall a b, a <> 0 -> b <> 0 -> b <> a mod b.
Proof.
(* skipped proof tokens: 117 *)
Admitted.
Lemma get_sublist_length: forall A (l: list A) a b,
a + b <= length l ->
length (get_sublist l a b) = b.
(* hint proof tokens: 31 *)
Proof.
intros.
unfold get_sublist.
rewrite firstn_length_l.
reflexivity.
rewrite skipn_length.
lia.
Qed.
Lemma bsplit_list_b2vb: forall b,
  exists l, (bsplit_list (bytes2valubytes (byte2bytes b))) = b::l.
(* hint proof tokens: 205 *)
Proof. 
  intros.
  unfold bytes2valubytes.
  destruct (le_dec 1 valubytes).
  simpl.
  unfold eq_rect.
  destruct (bytes_eq l).
  simpl.
  unfold bsplit1_dep, bsplit2_dep; simpl.
  rewrite bsplit1_bcombine.
  rewrite bsplit2_bcombine.
  unfold natToWord.
  exists (bsplit_list
       ((fix natToWord (sz n : addr) {struct sz} : word sz :=
           match sz as sz0 return (word sz0) with
           | 0 => WO
           | S sz' => WS (mod2 n) (natToWord sz' (Nat.div2 n))
           end) ((valubytes - 1) * 8) 0)).
  unfold byte2bytes.
  unfold word2bytes.
  eq_rect_simpl.
  reflexivity.
  rewrite valubytes_is in n; lia.
Qed.
Lemma app_length_eq: forall A (l l': list A) len a,
length l = len -> a + length l' <= len ->
length (firstn a l ++ l' ++ skipn (a + length l') l) = len.
(* hint proof tokens: 45 *)
Proof.
		intros; repeat rewrite app_length.
		repeat rewrite map_length.
		rewrite firstn_length_l.
		rewrite skipn_length.
		lia.
		lia.
	Qed.
Lemma off_mod_v_l_data_le_v: forall length_data off,
	length_data <= valubytes - off mod valubytes ->
	off mod valubytes + length_data <= valubytes.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Lemma v_off_mod_v_le_length_data: forall length_data off,
~ length_data <= valubytes - off mod valubytes ->
valubytes - off mod valubytes <= length_data.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma three_reorder: forall a b c,
a + b + c = c + b + a.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma last_two_reorder: forall a b c,
a + b + c = a + c + b.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma pm_1_3_cancel: forall a b,
a + b - a = b.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma n_le_n_p_1: forall n,
n <= n + 1.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma ppmp_2_4_cancel: forall a b c d,
a + b + c - b + d = a + c + d.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma mm_dist: forall a b c,
b <= a ->
c <= b ->
a - (b - c) = a - b + c.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma ppmm_4_5_minus_distr_le: forall a b c d e,
d <= a + b + c ->
e <= d ->
a + b + c - (d - e) = a + b + c - d + e.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma le_2: forall a b c,
b <= a + b + c.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma app_assoc_middle_2: forall A (l1 l2 l3 l4 l5: list A),
l1++l2++l3++l4++l5 = l1++l2++(l3++l4)++l5.
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 19 *)

intros.
repeat rewrite <- app_assoc.
reflexivity.
Qed.

Lemma ppmp_3_4_cancel: forall a b c d,
a + b + c - c + d = a + b + d.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma mm_1_3_cancel: forall a b,
a - b - a = 0.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma list_split_chunk_length: forall A n m (l: list A),
m > 0 ->
length l = n * m -> 
length (list_split_chunk n m l) = min n (length l / m).
(* hint proof tokens: 142 *)
Proof.
  induction n; intros; simpl.
  reflexivity.
  destruct (length l / m) eqn:D.
  destruct m eqn:D1; simpl; try lia.
  apply Nat.div_small_iff in D; try lia.
  rewrite IHn; try lia.
  rewrite skipn_length.
  rewrite H0.
  replace (S n * m - m) with (n * m).
  rewrite H0 in D.
  rewrite Nat.div_mul in *.
  inversion D.
  reflexivity.
  all: try lia.
  rewrite skipn_length.
  rewrite H0.
  simpl.
  apply pm_1_3_cancel.
Qed.
Lemma firstn_valuset2bytesets_byte2valu: forall b,
firstn 1 (valuset2bytesets (byte2valu b, nil)) = (b, nil)::nil.
(* hint proof tokens: 185 *)
Proof.
  intros;
  unfold valuset2bytesets.
  simpl.
  unfold byte2valu.
  unfold bytes2valubytes.
  destruct (le_dec 1 valubytes).
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil.
  unfold word2bytes.
  eq_rect_simpl.
  unfold valu2list.
  rewrite bytes2valu2bytes.
  unfold bcombine.
  eq_rect_simpl.
  unfold eq_rect.
  destruct (bytes_eq l).
  simpl.
  unfold bsplit1_dep; simpl.
  unfold bsplit1.
  eq_rect_simpl.
  rewrite Word.split1_combine.
  unfold byte2bytes.
  unfold word2bytes.
  eq_rect_simpl.
  reflexivity.
  rewrite valu2list_len; reflexivity.
  rewrite valubytes_is in n; lia.
Qed.
Lemma list_split_chunk_app_1: forall A a b (l l': list A) ,
length l = a * b ->
length l' = b ->
list_split_chunk (a+1) b (l ++ l') =  list_split_chunk a b l ++ l'::nil.
(* hint proof tokens: 115 *)
Proof.
  induction a; intros.
  simpl in H.
  apply length_zero_iff_nil in H; rewrite H.
  simpl.
  rewrite <- H0; rewrite firstn_exact; reflexivity.
  simpl.
  rewrite skipn_app_l.
  rewrite IHa.
  rewrite firstn_app_l.
  reflexivity.
  all: try lia.
  all: try rewrite H; simpl; try apply le_plus_trans; try lia.
  rewrite skipn_length. rewrite H; simpl. apply pm_1_3_cancel.
Qed.
Lemma list_split_chunk_map_comm: forall A B a b (l: list A) (f:A -> B),
map (fun x => map f x) (list_split_chunk a b l) = list_split_chunk a b (map f l).
(* hint proof tokens: 41 *)
Proof.
    induction a; intros.
    reflexivity.
    simpl.
    rewrite IHa.
    rewrite firstn_map_comm.
    rewrite skipn_map_comm.
    reflexivity.
Qed.
Lemma get_sublist_map_comm: forall A B a b (f: A -> B) (l: list A),
map f (get_sublist l a b) = get_sublist (map f l) a b.
(* hint proof tokens: 34 *)
Proof.
  intros; unfold get_sublist.
  rewrite <- firstn_map_comm; 
  rewrite <- skipn_map_comm;
  reflexivity.
Qed.
Lemma firstn_1_selN: forall A (l: list A) def,
l <> nil -> firstn 1 l = (selN l 0 def)::nil.
(* hint proof tokens: 24 *)
Proof.
  intros. 
  destruct l.
  destruct H; reflexivity.
  reflexivity.
Qed.
Lemma concat_list_split_chunk_id: forall A a b (l: list A),
a * b = length l -> concat (list_split_chunk a b l) = l.
Proof.
(* skipped proof tokens: 73 *)
Admitted.
Lemma list_split_chunk_cons: forall A m1 (l: list A),
length l = m1 * valubytes + valubytes -> 
list_split_chunk (m1 + 1) valubytes l  = firstn valubytes l :: list_split_chunk m1 valubytes (skipn valubytes l).
(* hint proof tokens: 30 *)
Proof.
  intros.
  replace (m1 + 1) with (S m1) by lia.
  reflexivity.
Qed.
Lemma list_split_chunk_nonnil: forall A a b (l: list A),
b > 0 ->
length l = a * b ->
forall x, In x (list_split_chunk a b l) -> x <> nil.
Proof.
(* skipped proof tokens: 98 *)
Admitted.
Lemma le_minus_weaken: forall a b c,
a <= b -> a-c <= b - c.
Proof.
(* skipped proof tokens: 11 *)
Admitted.
Lemma le_minus_dist: forall a b c,
a >= b ->
b >= c ->
a - (b - c) = a - b + c.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Lemma plus_minus_arrange: forall a b c d,
a >= b ->
a - b + c >= d ->
a - b + c - d + b = a + c - d + b - b.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma le_minus_weaken_r: forall a b c,
a <= b - c -> a <= b.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Fact merge_bs_length: forall l l',
length (merge_bs l l') = length l.
(* hint proof tokens: 30 *)
Proof.
induction l; intros.
reflexivity.
simpl.
destruct l'; simpl; rewrite IHl; reflexivity.
Qed.
Fact updN_list_length: forall l a ln,
a + length ln <= length l ->
length (updN_list l a ln) = length l.
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Fact updN_list2firstn_skipn: forall ln a l,
a + length ln <= length l ->
updN_list l a ln = firstn a l ++ (updN_list (get_sublist l a (length ln)) 0 ln) 
                      ++ skipn (a + (length ln)) l.
(* hint proof tokens: 92 *)
Proof.
intros.
unfold updN_list; simpl.
unfold get_sublist; simpl.
rewrite firstn_firstn.
rewrite Nat.min_id.
replace (firstn (length ln) (skipn a l)) with (firstn (length ln + 0) (skipn a l)).
rewrite skipn_firstn_comm.
simpl. rewrite app_nil_r. reflexivity.
rewrite <- plus_n_O; reflexivity.
Qed.
Lemma app_tail_eq: forall A (l l' l'':list A),
  l = l' -> l ++ l'' = l' ++ l''.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Lemma app_head_eq: forall A (l l' l'':list A),
  l = l' -> l'' ++ l = l'' ++ l'.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Lemma valubytes_ge_O: valubytes > 0.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Lemma old_data_m1_ge_0: forall l_old_data m1 l_old_blocks,
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
l_old_data - m1 * valubytes > 0.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Lemma length_data_ge_m1: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 * valubytes <= l_data.
(* hint proof tokens: 18 *)
Proof. intros; rewrite valubytes_is in *; lia. Qed.
Lemma get_sublist_div_length: forall A (data: list A) l_old_data m1 l_old_blocks,
length data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 <= length (get_sublist data 0 (m1 * valubytes)) / valubytes.
(* hint proof tokens: 41 *)
Proof.
intros.
rewrite get_sublist_length.
rewrite Nat.div_mul.
lia.
apply valubytes_ne_O.
simpl.
eapply length_data_ge_m1; eauto.
Qed.
Lemma length_old_data_ge_O: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
l_old_data > 0.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Lemma old_data_ne_nil: forall A (old_data: list A) m1 l_old_blocks,
old_data = nil ->
m1 < l_old_blocks ->
length old_data = l_old_blocks * valubytes ->
False.
(* hint proof tokens: 27 *)
Proof. intros; apply length_zero_iff_nil in H; rewrite valubytes_is in *; lia. Qed.
Lemma length_bytefile_ge_minus: forall l_fy block_off l_old_data m1 l_old_blocks,
block_off * valubytes + l_old_data <= l_fy ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
valubytes <= l_fy - (block_off + m1) * valubytes.
Proof.
(* skipped proof tokens: 18 *)
Admitted.
Lemma length_data_ge_m1_v: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 * valubytes + valubytes <= l_data.
(* hint proof tokens: 18 *)
Proof. intros; rewrite valubytes_is in *; lia. Qed.
Lemma nonnil_exists: forall A (l: list A),
l <> nil -> exists a l', l = a::l'.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma map_same: forall A B (l1 l2: list A) (f: A -> B),
l1 = l2 -> map f l1 = map f l2.
(* hint proof tokens: 13 *)
Proof. intros; subst; reflexivity. Qed.
Lemma pmm_1_3_cancel: forall a b c,
a + b - a -c = b - c.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma le_div_mult_add: forall a b,
b <> 0 -> a <= a/b * b + b.
Proof.
(* skipped proof tokens: 79 *)
Admitted.
Lemma le_minus_middle_cancel: forall a b c d e,
a - c <= d - e -> a - b - c <= d - b - e.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma mppp_two_five_cancel: forall a b c d,
a >= b ->
a - b + c + d + b = a + c + d.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma le_minus_lt: forall a b c,
b > 0 -> c > 0 -> a <= b - c -> a < b.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma modulo_eq: forall b a,
  b <> 0 -> a >= b -> (a - b) mod b = a mod b.
Proof.
(* skipped proof tokens: 135 *)
Admitted.
Lemma minus_middle: forall a b c,
b <> 0 -> a>= b -> b >= c -> (a - (b - c))/ b = (a + c) / b - 1.
Proof.
(* skipped proof tokens: 237 *)
Admitted.
Lemma mod_minus_eq: forall c a b,
	b <> 0 ->
	a >= c * b ->
	(a - c * b) mod b = a mod b.
Proof.
(* skipped proof tokens: 135 *)
Admitted.
Lemma lt_minus_r: forall a b c,
	b > c -> a > c -> a - c > a -b.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma div_lt_le: forall a b c,
      b <> 0 ->
      a >= c ->
      a / b >= c / b.
Proof.
(* skipped proof tokens: 21 *)
Admitted.
Lemma n2w_id: forall a b sz,
a = b -> natToWord sz a = natToWord sz b.
(* hint proof tokens: 13 *)
Proof. intros; subst; reflexivity. Qed.
Lemma mod_minus: forall a b,
b <> 0 ->
a - a mod b = (a / b) * b.
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Lemma mod_minus_mod: forall a b,
b <> 0 ->
(a - a mod b) mod b = 0.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma lt_mp: forall a b c,
a > b -> 
c < b ->
a - b + c < a.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma between_lt_upper: forall a b c,
b <> 0 ->
a > (c - 1) * b ->
a <= c * b ->
a mod b > 0 ->
a < c * b.
(* hint proof tokens: 78 *)
Proof.
  intros.
  destruct c; simpl in *; try lia.
  rewrite Nat.sub_0_r in *.
  destruct (Nat.eq_dec a (b + c * b)); try lia.
  subst.
  exfalso.
  rewrite Nat.mod_add in H2 by auto.
  rewrite Nat.mod_same in * by auto.
  lia.
Qed.
Lemma list_zero_pad_length: forall a l,
length (list_zero_pad l a) = length l + a.
(* hint proof tokens: 36 *)
Proof.
  induction a; intros.
  simpl; apply plus_n_O.
  simpl.
  rewrite IHa.
  rewrite app_length; simpl; lia.
Qed.
Lemma list_zero_pad_selN_l: forall a l i def,
i < length l ->
selN (list_zero_pad l a) i def = selN l i def.
(* hint proof tokens: 47 *)
Proof.
  induction a; intros.
  reflexivity.
  simpl.
  rewrite IHa.
  rewrite selN_app1.
  reflexivity.
  auto.
  rewrite app_length.
  simpl; lia.
Qed.
Lemma list_zero_pad_selN_pad: forall a l i,
i >= length l ->
selN (list_zero_pad l a) i byte0 = byte0.
(* hint proof tokens: 153 *)
Proof.
  intros.
  destruct (lt_dec i (length l + a)).
  generalize dependent l.
  induction a; intros.
  simpl.
  rewrite selN_oob; auto.
  simpl.
  destruct (le_dec (S (length l)) i).
  apply IHa.
  rewrite app_length; simpl; lia.
  rewrite app_length; simpl; lia.
  apply Nat.nle_gt in n.
  rewrite list_zero_pad_selN_l.
  rewrite selN_app2.
  simpl.
  destruct (i - length l); try lia; reflexivity.
  auto.
  rewrite app_length; simpl; lia.
  apply selN_oob.
  rewrite list_zero_pad_length; lia.
Qed.
Lemma between_mod_ne_0: forall c a b,
b <> 0 ->
a > (c - 1) * b ->
a < c * b ->
a mod b <> 0.
Proof.
(* skipped proof tokens: 158 *)
Admitted.
Lemma merge_bs_firstn_comm: forall l l' a,
firstn a (merge_bs l l') = merge_bs (firstn a l) (firstn a l').
Proof.
(* skipped proof tokens: 69 *)
Admitted.
Lemma list_zero_pad_expand: forall a l,
list_zero_pad l a = l ++ list_zero_pad nil a.
(* hint proof tokens: 74 *)
Proof. 
  induction a; intros; simpl.
  rewrite app_nil_r; reflexivity.
  rewrite IHa.
  simpl.
  remember ((l ++ byte0 :: nil) ++ list_zero_pad nil a) as x.
  rewrite IHa.
  rewrite Heqx.
  rewrite <- app_comm_cons.
  apply app_assoc_reverse.
Qed.
Lemma list_zero_pad_nil_iff: forall a l,
list_zero_pad l a = nil <-> l = nil /\ a = 0.
Proof.
(* skipped proof tokens: 83 *)
Admitted.
Lemma pmp_1_4_cancel: forall a b c,
a + b - a + c = b + c.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma lt_minus_S: forall a b,
a > b ->
exists n, a - b = S n.
Proof.
(* original proof tokens: 37 *)
(* generated proof tokens: 21 *)

intros a b H.
exists (a - S b).
lia.
Qed.

Lemma mod_upper_bound_le: forall a b,
a mod b < b ->
a mod b + 1 <= b.
(* hint proof tokens: 10 *)
Proof. intros. lia. Qed.
Lemma list_zero_pad_nil_firstn: forall a b,
firstn a (list_zero_pad nil b) = list_zero_pad nil (min a b).
Proof.
(* skipped proof tokens: 53 *)
Admitted.
Lemma lt_0_S: forall a,
	a > 0 -> exists n, a = S n.
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Lemma mod_minus_lt_0: forall a b,
	b <> 0 ->
	b - a mod b > 0.
(* hint proof tokens: 28 *)
Proof.
	intros. apply Nat.lt_add_lt_sub_r; simpl.
	apply Nat.mod_upper_bound; auto.
	Qed.
Lemma mp_2_3_cancel: forall a b,
	a >= b -> a - b + b = a.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma mod_upper_bound_le': forall a b,
	b <> 0 ->
	b >= a mod b.
Proof.
(* skipped proof tokens: 27 *)
Admitted.
Lemma mod_ne_0: forall a b,
b <> 0 -> a mod b > 0 ->
a > 0.
(* hint proof tokens: 38 *)
Proof. 
	intros. 
	rewrite Nat.div_mod with (x:= a)(y:= b).
	apply Nat.add_nonneg_pos.
	all: try lia.
Qed.
Lemma minus_le_0_eq: forall a b,
a >= b -> a - b = 0 -> a = b.
(* hint proof tokens: 10 *)
Proof. intros; lia. Qed.
Lemma lt_plus_minus_l: forall a b c,
  c > 0 -> a < b + c -> a - b < c.
(* hint proof tokens: 11 *)
Proof.  intros; lia. Qed.
Lemma plus_minus_eq_le: forall a b c,
  a >=  b -> a - b = c -> a = b + c.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Lemma between_exists: forall b a c,
    a >= (b-1) * c -> a < b*c -> c<>0 -> a = (b-1) * c + a mod c.
Proof.
(* skipped proof tokens: 68 *)
Admitted.
Lemma mod_between_upper: forall a b c,
	b <> 0 ->
	a > (c - 1) * b ->
	c * b >= a ->
	a mod b = 0 ->
	a = c * b.
Proof.
(* skipped proof tokens: 55 *)
Admitted.
