Require Import List Lia SetoidList Permutation.
Import ListNotations.
Import Permutation.
Import PeanoNat.
Set Implicit Arguments.
Fixpoint selN (V : Type) (vs : list V) (n : nat) (default : V) : V :=
  match vs with
    | nil => default
    | v :: vs' =>
      match n with
        | O => v
        | S n' => selN vs' n' default
      end
  end.
Fixpoint selNopt (V : Type) (vs : list V) (n : nat) : option V :=
  match vs with
    | nil => None
    | v :: vs' =>
      match n with
        | O => Some v
        | S n' => selNopt vs' n'
      end
  end.
Fixpoint updN T (vs : list T) (n : nat) (v : T) : list T :=
  match vs with
    | nil => nil
    | v' :: vs' =>
      match n with
        | O => v :: vs'
        | S n' => v' :: updN vs' n' v
      end
  end.
Notation "l ⟦ i ⟧" := (selN l i _) (at level 8, no associativity).
Notation "l ⟦ i := v ⟧" := (updN l i v) (at level 8, no associativity).
Hint Rewrite repeat_length map_length app_length Nat.min_idempotent : lists.
Definition eqlen A B (a : list A) (b : list B) := length a = length b.
Definition removeN {V} (l : list V) i :=
   (firstn i l) ++ (skipn (S i) l).
Lemma fst_pair : forall T1 T2 (a : T1) (b : T2) c, 
  c = (a, b) -> fst c = a.
(* hint proof tokens: 12 *)
Proof.
 intros; subst; firstorder.
Qed.
Lemma snd_pair : forall T1 T2 (a : T1) (b : T2) c, 
  c = (a, b) -> snd c = b.
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 14 *)

intros; subst; firstorder.
Qed.

Lemma repeat_selN : forall T i n (v def : T),
  i < n -> selN (repeat v n) i def = v.
Proof.
(* original proof tokens: 27 *)
intros.
induction n.
destruct i.
inversion H.
destruct i.
simpl.
(* No more tactics to try *)
Admitted.

Lemma repeat_selN' : forall T i n (v : T),
  selN (repeat v n) i v = v.
(* hint proof tokens: 18 *)
Proof.
  induction i; destruct n; firstorder; inversion H.
Qed.
Lemma selNopt_selN : forall T i l (v def : T),
  selNopt l i = Some v -> selN l i def = v.
(* hint proof tokens: 20 *)
Proof.
  induction i; destruct l; intros; inversion H; firstorder.
Qed.
Lemma selN_selNopt : forall T i l (v def : T),
  i < length l -> selNopt l i = Some (selN l i def).
Proof.
(* original proof tokens: 30 *)
intros.
induction l; simpl; intros; try congruence.
destruct i; simpl; try congruence.
inversion H.
(* No more tactics to try *)
Admitted.

Lemma selNopt_length : forall T i l (v : T),
  selNopt l i = Some v -> i < length l.
Proof.
(* original proof tokens: 33 *)
induction l; intros; inversion H; auto.
destruct i; auto.
apply Nat.lt_succ_r.
lia.
(* No more tactics to try *)
Admitted.

Lemma repeat_app : forall T i j (x : T),
  repeat x i ++ repeat x j = repeat x (i + j).
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma repeat_map : forall A B (f:A -> B) x n,
  map f (repeat x n) = repeat (f x) n.
Proof.
(* original proof tokens: 27 *)
(* generated proof tokens: 20 *)
induction n; simpl; auto.
rewrite IHn.
reflexivity.
Qed.

Lemma concat_hom_repeat : forall A l k (item : A),
  Forall (fun x => x = repeat item k) l ->
  concat l = repeat item (length l * k).
(* hint proof tokens: 34 *)
Proof.
  induction l; auto; intros.
  simpl.
  inversion H; subst.
  rewrite <- repeat_app.
  f_equal; auto.
Qed.
Lemma length_nil : forall A (l : list A),
  length l = 0 -> l = nil.
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 19 *)

intros.
induction l; auto.
inversion H.
Qed.

Lemma length_nil' : forall A (l : list A),
  length l = 0 -> nil = l.
(* hint proof tokens: 19 *)
Proof.
  intros; apply eq_sym.
  apply length_nil; auto.
Qed.
Lemma eqlen_nil : forall A B (a : list A),
  eqlen a (@nil B) -> a = nil.
Proof.
(* original proof tokens: 21 *)
intros.
unfold eqlen in H.
(* No more tactics to try *)
Admitted.

Lemma cons_app : forall A (a : A) l,
  a :: l = [a] ++ l.
(* hint proof tokens: 10 *)
Proof.
  intros; auto.
Qed.
Lemma nth_selN_eq : forall t n l (z:t), selN l n z = nth n l z.
Proof.
(* original proof tokens: 18 *)
intros.
induction l; simpl; auto; intros; destruct n; auto.
(* No more tactics to try *)
Admitted.

Lemma length_updN : forall T vs n (v : T), length (updN vs n v) = length vs.
(* hint proof tokens: 16 *)
Proof.
  induction vs; destruct n; simpl; intuition.
Qed.
Hint Rewrite length_updN : lists.
Lemma selN_updN_eq : forall V vs n v (default : V),
  n < length vs
  -> selN (updN vs n v) n default = v.
Proof.
(* original proof tokens: 18 *)
intros.
destruct vs; simpl; try lia.
destruct n; simpl; try lia.
inversion H.
inversion H.
(* No more tactics to try *)
Admitted.

Lemma selN_selN_def_eq : forall V vs n (def1 def2 : V),
  n < length vs
  -> selN vs n def1 = selN vs n def2.
Proof.
(* original proof tokens: 31 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_updN_eq_default : forall V vs n (v : V),
  selN (updN vs n v) n v = v.
(* hint proof tokens: 18 *)
Proof.
  induction vs; destruct n; simpl; intuition; lia.
Qed.
Lemma selN_updN_ne : forall V vs n n' v (default : V),
  n <> n'
  -> selN (updN vs n v) n' default = selN vs n' default.
Proof.
(* original proof tokens: 19 *)
intros.
induction vs; destruct n; destruct n'; simpl; auto; try lia.
(* No more tactics to try *)
Admitted.

Lemma selN_eq_updN_eq : forall A (l : list A) i a def,
  a = selN l i def
  -> updN l i a = l.
Proof.
(* original proof tokens: 32 *)
intros.
subst.
(* No more tactics to try *)
Admitted.

Lemma repeat_eq_updN : forall T i n (v x : T) l,
  i < n ->
  repeat v n = updN l i x -> x = v.
(* hint proof tokens: 65 *)
Proof.
  induction i; intros.
  - destruct n. lia.
    destruct l; simpl in *; inversion H0. auto.
  - destruct n. lia.
    destruct l; simpl in *; inversion H0.
    eapply IHi; [> | eauto]. lia.
Qed.
Hint Rewrite selN_updN_eq using (simpl; lia) : lists.
Lemma in_skipn_S : forall A l n (a : A) def,
  selN l n def <> a
  -> In a (skipn n l)
  -> In a (skipn (S n) l).
Proof.
(* original proof tokens: 17 *)
intros.
destruct l; simpl in *; auto; try lia.
(* No more tactics to try *)
Admitted.

Lemma in_firstn_in : forall A l n (a : A),
  In a (firstn n l) -> In a l.
(* hint proof tokens: 17 *)
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.
Lemma in_skipn_in : forall A l n (a : A),
  In a (skipn n l) -> In a l.
Proof.
(* original proof tokens: 17 *)
induction l; simpl; auto; intros; destruct n; auto.
(* No more tactics to try *)
Admitted.

Lemma in_cons_head : forall A l (a:A),
  In a (a :: l).
(* hint proof tokens: 15 *)
Proof.
  intros.
  constructor.
  reflexivity.
Qed.
Lemma in_app_middle : forall A l1 l2 (a:A),
  In a (l1 ++ a :: l2).
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_updN : forall T (v : T) vs i j,
  i <= j
  -> firstn i (updN vs j v) = firstn i vs.
(* hint proof tokens: 30 *)
Proof.
  induction vs; destruct i, j; simpl; intuition.
  lia.
  rewrite IHvs; auto; lia.
Qed.
Theorem updN_firstn_comm : forall T (v : T) vs i j,
  firstn i (updN vs j v) = updN (firstn i vs) j v.
(* hint proof tokens: 29 *)
Proof.
  induction vs; destruct i, j; simpl; intuition.
  rewrite IHvs by lia.
  reflexivity.
Qed.
Hint Rewrite firstn_updN using lia : lists.
Lemma skipn_skipn': forall A n m (l: list A),
  skipn n (skipn m l) = skipn (m + n) l.
(* hint proof tokens: 35 *)
Proof.
  intros until m.
  induction m; intros; simpl; auto.
  destruct l.
  destruct n; auto.
  apply IHm.
Qed.
Lemma skipn_skipn: forall A n m (l: list A),
  skipn n (skipn m l) = skipn (n + m) l.
(* hint proof tokens: 21 *)
Proof.
  intros.
  rewrite Nat.add_comm.
  apply skipn_skipn'.
Qed.
Lemma skipn_selN : forall T i j vs (def: T),
  selN (skipn i vs) j def = selN vs (i + j) def.
Proof.
(* original proof tokens: 21 *)
unfold selN.
induction vs; simpl; intros; auto.
(* No more tactics to try *)
Admitted.

Hint Rewrite skipn_selN using lia : lists.
Lemma skipn_seq : forall n a b, skipn n (seq a b) = seq (a + n) (b - n).
(* hint proof tokens: 47 *)
Proof.
  induction n; intros.
  rewrite Nat.add_0_r, Nat.sub_0_r; auto.
  destruct b; auto.
  simpl.
  rewrite IHn.
  f_equal; lia.
Qed.
Hint Rewrite skipn_seq : lists.
Lemma skipN_updN' : forall T (v : T) vs i j,
  i > j
  -> skipn i (updN vs j v) = skipn i vs.
Proof.
(* original proof tokens: 20 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_updN : forall T (v : T) vs i j,
  i >= j
  -> match updN vs j v with
       | nil => nil
       | _ :: vs' => skipn i vs'
     end
     = match vs with
         | nil => nil
         | _ :: vs' => skipn i vs'
       end.
(* hint proof tokens: 22 *)
Proof.
  destruct vs, j; simpl; eauto using skipN_updN'.
Qed.
Lemma skipn_selN_skipn : forall off A (l : list A) def,
  off < length l ->
  skipn off l = selN l off def :: skipn (S off) l.
(* hint proof tokens: 45 *)
Proof.
  induction off; simpl; intros.
  destruct l; simpl in *; try lia; auto.
  destruct l; simpl in *; try lia.
  apply IHoff.
  lia.
Qed.
Lemma skipn_sub_S_selN_cons : forall A (l : list A) n def,
  n < length l ->
  skipn (length l - S n) l = selN l (length l - n - 1) def :: (skipn (length l - n) l).
(* hint proof tokens: 52 *)
Proof.
  intros.
  replace (length l - n) with (S (length l - n - 1)) at 2 by lia.
  rewrite <- skipn_selN_skipn by lia.
  f_equal; lia.
Qed.
Hint Rewrite skipn_updN using lia : lists.
Lemma updN_twice : forall T (l : list T) a v v',
  updN (updN l a v') a v = updN l a v.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite updN_twice : lists.
Lemma updN_comm : forall T (l : list T) a0 v0 a1 v1,
  a0 <> a1 ->
  updN (updN l a0 v0) a1 v1 = updN (updN l a1 v1) a0 v0.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma updN_firstn_skipn : forall T (l:list T) n v,
  n < length l ->
  updN l n v = firstn n l ++ v::nil ++ skipn (n+1) l.
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Theorem list_selN_ext' : forall len T (a b : list T) default,
  length a = len
  -> length b = len
  -> (forall pos, pos < len -> selN a pos default = selN b pos default)
  -> a = b.
Proof.
(* original proof tokens: 69 *)
induction len; intros; simpl in *; auto.
destruct a; destruct b; simpl in *; try lia; auto.
inversion H; inversion H0; subst; auto.
(* No more tactics to try *)
Admitted.

Theorem list_selN_ext : forall T (a b : list T) default,
  length a = length b
  -> (forall pos, pos < length a -> selN a pos default = selN b pos default)
  -> a = b.
(* hint proof tokens: 28 *)
Proof.
  intros. apply list_selN_ext' with (len:=length a) (default:=default); auto.
Qed.
Ltac nth_selN H := intros; repeat rewrite nth_selN_eq; apply H; assumption.
Lemma in_selN : forall t n l (z:t), n < length l -> In (selN l n z) l.
(* hint proof tokens: 12 *)
Proof.
  nth_selN nth_In.
Qed.
Lemma in_selN_exists : forall A l (a : A) def,
  In a l -> exists i, i < length l /\ selN l i def = a.
(* hint proof tokens: 63 *)
Proof.
  induction l; try easy; intros.
  inversion H; subst.
  exists 0; simpl; split; auto; lia.
  destruct (IHl a0 def H0).
  destruct H1.
  exists (S x); simpl; split; auto; lia.
Qed.
Lemma selN_split_r: forall A B (l : list (A * B)) i d,
  selN (snd (split l)) i (snd d) = snd (selN l i d).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma selN_split_l: forall A B (l : list (A * B)) i d,
  selN (fst (split l)) i (fst d) = fst (selN l i d).
(* hint proof tokens: 32 *)
Proof.
  induction l; cbn; intros.
  auto.
  destruct a, split.
  destruct i; cbn; auto.
Qed.
Lemma map_fst_split: forall A B (l : list (A * B)), map fst l = fst (split l).
(* hint proof tokens: 38 *)
Proof.
  induction l; cbn; auto.
  destruct a; cbn.
  destruct split eqn:?; cbn in *.
  congruence.
Qed.
Lemma map_snd_split: forall A B (l : list (A * B)), map snd l = snd (split l).
Proof.
(* original proof tokens: 38 *)
induction l; cbn; auto.
destruct a; cbn.
rewrite IHl.
(* No more tactics to try *)
Admitted.

Lemma in_updN : forall t n l x (xn:t), In x (updN l n xn) ->
  In x l \/ x = xn.
(* hint proof tokens: 37 *)
Proof.
  induction n; intros; destruct l; intuition; simpl in *; destruct H; auto.
  destruct (IHn l x xn H); auto.
Qed.
Lemma Forall_app: forall A f l (a : A),
  Forall f l -> f a -> Forall f (l ++ a :: nil).
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Lemma Forall_combine_r: forall A B F G (a : list A) (b : list B),
  length a = length b ->
  (forall x, F x <-> G (snd x)) ->
  Forall F (combine a b) <-> Forall G b.
(* hint proof tokens: 76 *)
Proof.
  induction a; destruct b; cbn in *; try congruence; intros.
  split; constructor.
  split; intros H'; inversion H'; constructor; subst.
  eapply H0 in H3; auto.
  eapply IHa; auto.
  eapply H0; auto.
  apply IHa; auto.
Qed.
Lemma Forall_append: forall A f (l1 l2:list A),
  Forall f l1 -> Forall f l2 -> Forall f (l1 ++ l2).
(* hint proof tokens: 47 *)
Proof.
  intros.
  rewrite Forall_forall in *.
  intros.
  apply in_app_or in H1.
  destruct H1.
  apply H; assumption.
  apply H0; assumption.
Qed.
Lemma forall_app_r : forall A P (a b : list A),
  Forall P (a ++ b) -> Forall P a.
Proof.
(* original proof tokens: 27 *)
intros.
apply Forall_forall.
intros x H0.
(* No more tactics to try *)
Admitted.

Lemma forall_app_l : forall A P (a b : list A),
  Forall P (a ++ b) -> Forall P b.
(* hint proof tokens: 27 *)
Proof.
  intros; rewrite Forall_forall in *; firstorder.
  eauto using in_or_app.
Qed.
Lemma Forall_repeat: forall A (f:A -> Prop) a n,
  f a -> Forall f (repeat a n).
Proof.
(* original proof tokens: 31 *)
(* generated proof tokens: 20 *)

induction n; auto; simpl; intros; constructor; auto.
Qed.

Lemma Forall_updN : forall A (l : list A) a i P,
  Forall P l -> P a ->
  Forall P (updN l i a).
Proof.
(* original proof tokens: 34 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma Forall_cons2 : forall A (l : list A) a f,
  Forall f (a :: l) -> Forall f l.
(* hint proof tokens: 30 *)
Proof.
  intros.
  rewrite Forall_forall in *; intros.
  apply H.
  apply in_cons; auto.
Qed.
Lemma Forall_combine_same : forall T T1 T2 (l : list T) P (f1 : T -> T1) (f2 : T -> T2),
  Forall (fun x => P (f1 x, f2 x)) l ->
  Forall P (combine (map f1 l) (map f2 l)).
(* hint proof tokens: 29 *)
Proof.
  induction l; simpl; intros.
  - constructor.
  - inversion H; subst.
    constructor; auto.
Qed.
Lemma concat_repeat: forall T n k (x : T),
  concat (repeat (repeat x k) n) = repeat x (n * k).
(* hint proof tokens: 34 *)
Proof.
  intros.
  erewrite concat_hom_repeat.
  autorewrite with lists.
  eauto.
  apply Forall_repeat; auto.
Qed.
Ltac small_t' := intros; autorewrite with core; autorewrite with core in *;
           eauto; simpl in *; intuition; eauto.
Ltac small_t := repeat small_t'; subst; simpl; eauto.
Lemma forall_skipn: forall A n (l : list A) p,
  Forall p l -> Forall p (skipn n l).
Proof.
(* original proof tokens: 37 *)
induction l; simpl; intros; auto.
(* No more tactics to try *)
Admitted.

Lemma forall_firstn: forall A n (l : list A) p,
  Forall p l -> Forall p (firstn n l).
(* hint proof tokens: 35 *)
Proof.
  induction n; simpl; auto; intros.
  destruct l; auto.
  inversion H; subst.
  apply Forall_cons; auto.
Qed.
Lemma updN_selN_eq : forall T (l : list T) ix default,
  updN l ix (selN l ix default) = l.
(* hint proof tokens: 27 *)
Proof.
  induction l; auto.
  intros. destruct ix. auto. simpl. rewrite IHl. trivial.
Qed.
Lemma updN_app1 : forall t l l' (v:t) n,
  n < length l -> updN (l ++ l') n v = updN l n v ++ l'.
(* hint proof tokens: 44 *)
Proof.
  
  induction l.
  intros.
  inversion H.
  intros l' d n.
  case n; simpl; auto.
  intros; rewrite IHl; auto with arith.
Qed.
Lemma updN_app2 : forall t l l' (v:t) n,
  n >= length l -> updN (l ++ l') n v = l ++ updN l' (n - length l) v.
(* hint proof tokens: 61 *)
Proof.
  
  induction l.
  intros.
  simpl.
  rewrite Nat.sub_0_r; auto.
  intros l' d n.
  case n; simpl; auto.
  intros.
  inversion H.
  intros.
  rewrite IHl; auto with arith.
Qed.
Lemma updN_app_tail : forall T (l : list T) a v,
  updN (l ++ (a :: nil)) (length l) v = l ++ (v :: nil).
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma updN_concat : forall t a b m l (v:t), b < m ->
  Forall (fun sl => length sl = m) l ->
  updN (concat l) (b + a * m) v =
    concat (updN l a (updN (selN l a nil) b v)).
(* hint proof tokens: 105 *)
Proof.
  
  induction a; intros; destruct l; simpl; inversion H0.
  trivial.
  replace (b + 0) with b by lia. subst.
  rewrite updN_app1; auto.
  trivial.
  subst. remember (a * length l) as al. rewrite updN_app2 by lia.
  replace (b + (length l + al) - length l) with (b + al) by lia. subst.
  rewrite IHa; auto.
Qed.
Lemma selN_app1 : forall t l l' (d:t) n,
  n < length l -> selN (l ++ l') n d = selN l n d.
Proof.
(* original proof tokens: 14 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_app2 : forall t l l' (d:t) n,
  n >= length l -> selN (l ++ l') n d = selN l' (n - length l) d.
(* hint proof tokens: 14 *)
Proof.
  nth_selN app_nth2.
Qed.
Lemma selN_cons : forall A (a : A) l i def,
  i > 0 -> selN (a :: l) i def = selN l (i - 1) def.
(* hint proof tokens: 39 *)
Proof.
  intros.
  replace (a :: l) with ([a] ++ l) by (simpl; auto).
  rewrite selN_app2; simpl; auto.
Qed.
Theorem seq_right : forall b a, seq a (S b) = seq a b ++ (a + b :: nil).
(* hint proof tokens: 62 *)
Proof.
  induction b; simpl; intros.
  replace (a + 0) with (a) by lia; reflexivity.
  f_equal.
  replace (a + S b) with (S a + b) by lia.
  rewrite <- IHb.
  auto.
Qed.
Theorem seq_right_0 : forall b, seq 0 (S b) = seq 0 b ++ (b :: nil).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Lemma selN_map_some_range : forall A (l : list A) idx a,
  selN (map (@Some _) l) idx None = Some a ->
  idx < length l.
Proof.
(* original proof tokens: 36 *)
intros.
eapply selNopt_length; eauto.
(* No more tactics to try *)
Admitted.

Lemma map_updN : forall T U (v : T) (f : T -> U) vs i,
  map f (updN vs i v) = updN (map f vs) i (f v).
(* hint proof tokens: 21 *)
Proof.
  induction vs; auto; destruct i; simpl; f_equal; auto.
Qed.
Hint Rewrite map_updN : lists.
Theorem selN_map_seq' : forall T i n f base (default : T), i < n
  -> selN (map f (seq base n)) i default = f (i + base).
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Theorem selN_map_seq : forall T i n f (default : T), i < n
  -> selN (map f (seq 0 n)) i default = f i.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite selN_map_seq using ( solve [ auto ] ) : lists.
Lemma map_selN_seq: forall T (l : list T) n d,
  n = length l ->
  map (fun i => selN l i d) (seq 0 n) = l.
(* hint proof tokens: 38 *)
Proof.
  induction l; intros; subst; cbn in *.
  auto.
  f_equal.
  rewrite <- seq_shift.
  rewrite map_map. auto.
Qed.
Theorem selN_map : forall T T' l i f (default : T) (default' : T'), i < length l
  -> selN (map f l) i default = f (selN l i default').
Proof.
(* original proof tokens: 29 *)
(* generated proof tokens: 33 *)
induction l; intros; simpl in *; try lia.
destruct i; auto; simpl; apply IHl; auto; lia.
Qed.

Lemma in_selN_map : forall A B (l : list (A*B)) i def1 def2,
  i < length l
  -> In (selN (map fst l) i def1, selN (map snd l) i def2) l.
(* hint proof tokens: 39 *)
Proof.
  induction l; destruct i; simpl; try now firstorder.
  left; destruct a; auto.
  intros. right. eapply IHl. lia.
Qed.
Theorem updN_map_seq_app_eq : forall T (f : nat -> T) len start (v : T) x,
  updN (map f (seq start len) ++ (x :: nil)) len v =
  map f (seq start len) ++ (v :: nil).
(* hint proof tokens: 21 *)
Proof.
  induction len; auto; simpl; intros.
  f_equal; auto.
Qed.
Theorem updN_map_seq_app_ne : forall T (f : nat -> T) len start (v : T) x pos, pos < len
  -> updN (map f (seq start len) ++ (x :: nil)) pos v =
     updN (map f (seq start len)) pos v ++ (x :: nil).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Theorem updN_map_seq : forall T f len start pos (v : T), pos < len
  -> updN (map f (seq start len)) pos v =
     map (fun i => if Nat.eq_dec i (start + pos) then v else f i) (seq start len).
(* hint proof tokens: 143 *)
Proof.
  induction len; intros; try lia.
  simpl seq; simpl map.
  destruct pos.
  - replace (start + 0) with (start) by lia; simpl.
    f_equal.
    + destruct (Nat.eq_dec start start); congruence.
    + apply map_ext_in; intros.
      destruct (Nat.eq_dec a start); auto.
      apply in_seq in H0; lia.
  - simpl; f_equal.
    destruct (Nat.eq_dec start (start + S pos)); auto; lia.
    rewrite IHlen by lia.
    replace (S start + pos) with (start + S pos) by lia.
    auto.
Qed.
Lemma combine_l_nil : forall T R (a : list T), List.combine a (@nil R) = nil.
(* hint proof tokens: 11 *)
Proof.
  induction a; auto.
Qed.
Hint Rewrite combine_l_nil : lists.
Theorem firstn_combine_comm : forall n T R (a : list T) (b : list R),
  firstn n (List.combine a b) = List.combine (firstn n a) (firstn n b).
Proof.
(* original proof tokens: 38 *)
(* generated proof tokens: 34 *)
induction n; simpl; auto; intros.
destruct a; destruct b; simpl; auto; try apply IHn; congruence.
Qed.

Theorem skipn_combine_comm : forall n T R (a : list T) (b : list R),
  match (List.combine a b) with
  | nil => nil
  | _ :: c => skipn n c
  end = List.combine (skipn (S n) a) (skipn (S n) b).
(* hint proof tokens: 140 *)
Proof.
  induction n.
  - simpl; intros.
    destruct a; simpl; auto.
    destruct b; simpl; auto.
    autorewrite with lists; auto.
  - intros.
    destruct a; [simpl; auto|].
    destruct b; [simpl; auto|].
    autorewrite with lists; auto.
    replace (skipn (S (S n)) (t :: a)) with (skipn (S n) a) by auto.
    replace (skipn (S (S n)) (r :: b)) with (skipn (S n) b) by auto.
    rewrite <- IHn.
    simpl; auto.
Qed.
Lemma skipn_combine_comm' : forall n T R (a : list T) (b : list R),
  skipn (S n) (List.combine a b) = List.combine (skipn (S n) a) (skipn (S n) b).
Proof.
(* original proof tokens: 15 *)
intros.
induction n; simpl; auto.
destruct a; destruct b; simpl; auto; try congruence.
(* No more tactics to try *)
Admitted.

Lemma skipn_combine : forall A B n (a : list A) (b : list B),
  length a = length b ->
  skipn n (combine a b) = combine (skipn n a) (skipn n b).
(* hint proof tokens: 26 *)
Proof.
  induction n; intros.
  simpl; auto.
  rewrite skipn_combine_comm'; auto.
Qed.
Lemma selN_last: forall A l n def (a : A),
  n = length l -> selN (l ++ a :: nil) n def = a.
Proof.
(* original proof tokens: 25 *)
intros.
subst.
simpl.
auto.
(* No more tactics to try *)
Admitted.

Lemma selN_firstn: forall {A} (l:list A) i n d,
  i < n -> selN (firstn n l) i d = selN l i d.
(* hint proof tokens: 28 *)
Proof.
  induction l; destruct i, n; intros; try lia; auto.
  apply IHl; lia.
Qed.
Lemma selN_oob: forall A n l (def : A),
  length l <= n
  -> selN l n def = def.
(* hint proof tokens: 26 *)
Proof.
  induction n; destruct l; simpl; try now firstorder.
  eauto with arith.
Qed.
Lemma selN_inb : forall A (l : list A) n d1 d2,
  n < length l ->
  selN l n d1 = selN l n d2.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma selN_app: forall A n l l' (def : A),
  n < length l
  -> selN (l ++ l') n def = selN l n def.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_app2: forall A n (l1 l2 : list A),
  n = length l1 -> firstn n (l1 ++ l2) = l1.
(* hint proof tokens: 36 *)
Proof.
  induction n; destruct l1; intros; inversion H; auto; subst.
  unfold firstn; simpl.
  rewrite IHn; auto.
Qed.
Lemma skipn_oob: forall T n (l : list T),
  n >= length l -> skipn n l = nil.
(* hint proof tokens: 38 *)
Proof.
  unfold skipn; induction n; destruct l; intros; auto.
  inversion H.
  apply IHn; firstorder. eauto with arith.
Qed.
Lemma updN_oob: forall T l i (v : T),
  i >= length l -> updN l i v = l.
(* hint proof tokens: 38 *)
Proof.
  unfold updN; induction l; destruct i; intros; auto.
  inversion H.
  rewrite IHl; firstorder. eauto with arith.
Qed.
Lemma firstn_oob: forall A (l : list A) n,
  n >= length l -> firstn n l = l.
Proof.
(* original proof tokens: 37 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_exact: forall A (l : list A),
  firstn (length l) l = l.
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 18 *)
induction l; simpl; auto.
rewrite IHl; auto.
Qed.

Lemma firstn_firstn : forall A (l : list A) n1 n2 ,
  firstn n1 (firstn n2 l) = firstn (Init.Nat.min n1 n2) l.
(* hint proof tokens: 27 *)
Proof.
  induction l; destruct n1, n2; simpl; auto.
  rewrite IHl; auto.
Qed.
Lemma firstn_all : forall A (l : list A), firstn (length l) l = l.
(* hint proof tokens: 26 *)
Proof. induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.
Lemma firstn_plusone_selN : forall A n (l : list A) def,
  n < length l
  -> firstn (n + 1) l = firstn n l ++ (selN l n def :: nil).
(* hint proof tokens: 38 *)
Proof.
  induction n; destruct l; intros; simpl in *; try now firstorder.
  rewrite IHn with (def:=def) by lia; auto.
Qed.
Definition firstn_plusone_selN' : forall A n l (x: A) def,
  x = selN l n def ->
  n < length l ->
  firstn (n + 1) l = firstn n l ++ x::nil.
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 20 *)
intros.
rewrite H; apply firstn_plusone_selN; auto.
Qed.

Lemma firstn_S_selN : forall A n l (def : A),
  n < length l ->
  firstn (S n) l = firstn n l ++ [ (selN l n def) ].
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_S_selN_expand : forall A n l (def : A),
  n < length l ->
  match l with
  | nil => nil
  | a :: l => a :: firstn n l
  end = firstn n l ++ [ (selN l n def) ].
(* hint proof tokens: 24 *)
Proof.
  intros.
  rewrite <- firstn_S_selN by auto.
  simpl; auto.
Qed.
Lemma firstn_updN_oob: forall A (l : list A) n i def,
  n <= i -> firstn n (updN l i def) = firstn n l.
Proof.
(* original proof tokens: 34 *)
(* generated proof tokens: 22 *)

intros.
rewrite firstn_updN by lia.
reflexivity.
Qed.

Lemma firstn_app_updN_eq : forall A l n (x : A),
  n < length l
  -> (firstn n l) ++ x :: nil = firstn (n + 1) (updN l n x).
Proof.
(* original proof tokens: 54 *)
intros.
rewrite updN_firstn_comm by lia.
(* No more tactics to try *)
Admitted.

Lemma length_not_nil : forall A (l : list A),
  l <> nil <-> length l > 0.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Lemma length_not_nil' : forall A (l : list A),
  l <> nil <-> length l <> 0.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_is_nil : forall A n (l : list A),
  n > 0 -> firstn n l = nil -> l = nil.
Proof.
(* original proof tokens: 29 *)
(* generated proof tokens: 93 *)
intros.
inversion H0; auto.
rewrite H0.
apply length_nil; auto.
inversion H0; auto.
destruct l; auto; try lia.
inversion H0; auto.
simpl in H0; inversion H0; auto.
simpl in H0; inversion H0; auto.
inversion H0; auto.
destruct n; simpl in *; try lia; inversion H0; auto.
Qed.

Lemma removelast_firstn_sub : forall A n (l : list A),
  n > 0 -> n <= length l
  -> removelast (firstn n l) = firstn (n - 1) l.
(* hint proof tokens: 57 *)
Proof.
  intros.
  replace n with (S (n - 1)) by lia.
  replace (S (n - 1) - 1) with (n - 1) by lia.
  apply removelast_firstn; lia.
Qed.
Lemma firstn_nil : forall A n,
  firstn n nil = @nil A.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_cons : forall A n (a : A) l,
  firstn (S n) (a :: l) = a :: firstn n l.
(* hint proof tokens: 22 *)
Proof.
  induction n; intros.
  simpl; auto.
  simpl; f_equal.
Qed.
Lemma firstn_length_l : forall A (l : list A) n,
  n <= length l -> length (firstn n l) = n.
(* hint proof tokens: 22 *)
Proof.
  intros.
  rewrite firstn_length.
  rewrite Nat.min_l; auto.
Qed.
Lemma firstn_length_l_iff : forall A (l : list A) n,
  n <= length l <-> length (firstn n l) = n.
Proof.
(* original proof tokens: 46 *)
split.
(* No more tactics to try *)
Admitted.

Lemma firstn_length_r : forall A (l : list A) n,
  n >= length l -> length (firstn n l) = length l.
(* hint proof tokens: 22 *)
Proof.
  intros.
  rewrite firstn_length.
  rewrite Nat.min_r; auto.
Qed.
Lemma skipn_length: forall A n (l : list A),
  length (skipn n l) = length l - n.
(* hint proof tokens: 17 *)
Proof.
  induction n; destruct l; intros; firstorder.
Qed.
Lemma skipn_nil : forall A n,
  skipn n nil = @nil A.
Proof.
(* original proof tokens: 12 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_nil : forall A n,
  removeN nil n = (@nil A).
(* hint proof tokens: 12 *)
Proof.
  induction n; firstorder.
Qed.
Lemma cons_nil_app : forall A l r (a : A),
  (l ++ (a :: nil)) ++ r = l ++ a :: r.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve cons_nil_app.
Lemma firstn_app_r : forall T i (b a : list T),
  firstn (length a + i) (a ++ b) = a ++ (firstn i b).
Proof.
(* original proof tokens: 123 *)
(* generated proof tokens: 22 *)
induction a; simpl; intros; auto.
rewrite IHa.
reflexivity.
Qed.

Lemma firstn_app_l: forall A (a b: list A) n,
  n <= length a ->
  firstn n (a ++ b) = firstn n a.
(* hint proof tokens: 40 *)
Proof.
  induction a; intros; simpl in *.
  inversion H. auto.
  destruct n; simpl in *; auto.
  rewrite IHa by lia; auto.
Qed.
Lemma skipn_app : forall T (a b : list T),
  skipn (length a) (a ++ b) = b.
(* hint proof tokens: 12 *)
Proof.
  induction a; firstorder.
Qed.
Lemma skipn_app_eq : forall T (a b : list T) n,
  length a = n -> skipn n (a ++ b) = b.
(* hint proof tokens: 19 *)
Proof.
  intros.
  rewrite <- H.
  apply skipn_app.
Qed.
Lemma skipn_app_r : forall T i (b a : list T),
  skipn (length a + i) (a ++ b) = skipn i b.
Proof.
(* original proof tokens: 104 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_app_l : forall T i (a b : list T),
  i <= length a ->
  skipn i (a ++ b) = (skipn i a) ++ b.
Proof.
(* original proof tokens: 41 *)
induction a; intros; simpl.
(* No more tactics to try *)
Admitted.

Lemma skipn_app_split: forall T (a b : list T) n,
  skipn n (a ++ b) = skipn n a ++ skipn (n - length a) b.
Proof.
(* original proof tokens: 88 *)
destruct n; simpl; auto.
destruct a; simpl; auto.
destruct n; simpl; auto.
destruct a; simpl; auto.
destruct n; simpl; auto.
destruct a; simpl; auto.
destruct n; simpl; auto.
destruct a; simpl; auto.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
destruct n; simpl; auto; intros; destruct a; simpl; auto; try lia.
induction n; simpl; intros; auto.
destruct a; simpl; auto; try lia.
(* Reached max number of model calls *)
Admitted.

Lemma removeN_app_r : forall T (b a : list T) i,
  removeN (a ++ b) (length a + i) = a ++ (removeN b i).
(* hint proof tokens: 54 *)
Proof.
  unfold removeN; intros.
  rewrite firstn_app_r.
  replace (S (length a + i)) with (length a + (S i)) by lia.
  rewrite skipn_app_r.
  apply app_assoc_reverse.
Qed.
Lemma firstn_repeat : forall T m n (v : T),
  n <= m -> firstn n (repeat v m) = repeat v n.
Proof.
(* original proof tokens: 63 *)
induction n; simpl; auto; intros.
rewrite repeat_cons by lia; auto.
(* No more tactics to try *)
Admitted.

Lemma skipn_repeat' : forall A (v : A) m n,
  n <= m -> skipn n (repeat v m) = repeat v (m - n).
Proof.
(* original proof tokens: 40 *)
induction n; intros; simpl.
destruct m; simpl; auto; try lia.
(* No more tactics to try *)
Admitted.

Lemma skipn_repeat : forall A (v : A) m n,
  skipn n (repeat v m) = repeat v (m - n).
(* hint proof tokens: 56 *)
Proof.
  intros; destruct (Compare_dec.le_dec n m).
  apply skipn_repeat'; auto.
  rewrite skipn_oob.
  replace (m - n) with 0 by lia; simpl; auto.
  rewrite repeat_length; lia.
Qed.
Lemma app_repeat : forall T m n (v : T),
  repeat v m ++ repeat v n = repeat v (m + n).
(* hint proof tokens: 52 *)
Proof.
  induction m; unfold repeat; firstorder; fold repeat.
  rewrite <- app_comm_cons.
  rewrite IHm.
  replace (S m + n) with (S (m + n)) by lia.
  auto.
Qed.
Lemma repeat_app_tail : forall T n (a : T),
  repeat a (S n) = repeat a n ++ (a :: nil).
Proof.
(* original proof tokens: 34 *)
simpl.
(* No more tactics to try *)
Admitted.

Lemma removeN_repeat : forall T n i (e : T),
   n > 0 -> i < n
   -> removeN (repeat e n) i = repeat e (n - 1).
(* hint proof tokens: 40 *)
Proof.
  intros.
  unfold removeN.
  rewrite firstn_repeat by lia.
  rewrite skipn_repeat by lia.
  rewrite app_repeat.
  f_equal; lia.
Qed.
Lemma firstn_nonnil : forall T (l : list T) n, 0 < n -> l <> nil ->
  exists e l', firstn n l = e :: l'.
(* hint proof tokens: 31 *)
Proof.
  destruct l; simpl; intros; try congruence.
  destruct n; simpl; try lia.
  eauto.
Qed.
Lemma skipn_nonnil : forall T (l : list T) n, n < length l ->
  exists e l', skipn n l = e :: l'.
(* hint proof tokens: 49 *)
Proof.
  induction l; simpl; intros; try lia.
  destruct n.
  exists a; exists l; eauto.
  destruct (IHl n); try lia.
  destruct H0.
  eauto.
Qed.
Lemma firstn_sum_split : forall A n off (l: list A),
  firstn (n+off) l = firstn n l ++ firstn off (skipn n l).
(* hint proof tokens: 55 *)
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  - reflexivity.
  - induction l; simpl.
    + rewrite firstn_nil.
      reflexivity.
    + f_equal.
      apply IHn.
Qed.
Lemma skipn_sum_split : forall A n k (l: list A),
  skipn n l = firstn k (skipn n l) ++ skipn (n+k) l.
Proof.
(* original proof tokens: 68 *)
unfold skipn; simpl.
(* No more tactics to try *)
Admitted.

Lemma skipn_sum_split' : forall A n off1 off2 (l: list A),
  off1 <= off2 ->
  skipn (n+off1) l =
    firstn (off2 - off1) (skipn (n+off1) l) ++ skipn (n+off2) l.
(* hint proof tokens: 40 *)
Proof.
  intros.
  replace (n+off2) with (n+off1 + (off2 - off1)) by lia.
  apply skipn_sum_split.
Qed.
Lemma firstn_sum_app : forall A (l1 l2: list A) n1 n2,
  n1 = length l1 ->
  firstn (n1 + n2) (l1 ++ l2) = l1 ++ firstn n2 l2.
(* hint proof tokens: 39 *)
Proof.
  intros.
  rewrite firstn_sum_split.
  rewrite H.
  rewrite firstn_app2 by reflexivity.
  rewrite skipn_app.
  reflexivity.
Qed.
Lemma skipn_sum_app : forall A (l1 l2: list A) n1 n2,
  n1 = length l1 ->
  skipn (n1 + n2) (l1 ++ l2) = skipn n2 l2.
(* hint proof tokens: 30 *)
Proof.
  intros.
  rewrite H.
  rewrite <- skipn_skipn'.
  rewrite skipn_app.
  reflexivity.
Qed.
Lemma firstn_double_skipn : forall A n len1 len2 (l:list A),
  len1 + n <= len2 ->
  firstn len1 (skipn n (firstn len2 l)) = firstn len1 (skipn n l).
Proof.
(* original proof tokens: 103 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_skipn_subslice : forall A n1 len1 n2 len2 (l:list A),
  len1 + n1 <= len2 ->
  firstn len1 (skipn n1 (firstn len2 (skipn n2 l))) =
    firstn len1 (skipn (n1+n2) l).
Proof.
(* original proof tokens: 27 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma concat_hom_length : forall A (lists: list (list A)) k,
  Forall (fun sublist => length sublist = k) lists ->
  length (concat lists) = (length lists) * k.
(* hint proof tokens: 84 *)
Proof.
  intros.
  induction lists.
  rewrite concat_nil.
  simpl; reflexivity.
  rewrite concat_cons.
  rewrite app_length.
  simpl.
  rewrite IHlists.
  rewrite Forall_forall in H.
  replace k with (length a).
  reflexivity.
  apply H; apply in_cons_head.
  eapply Forall_cons2.
  eassumption.
Qed.
Lemma concat_hom_firstn : forall A (lists: list (list A)) n k,
  Forall (fun sublist => length sublist = k) lists ->
  firstn (n * k) (concat lists) = concat (firstn n lists).
(* hint proof tokens: 157 *)
Proof.
  intros.
  generalize dependent n.
  induction lists; intros; simpl.
  repeat (rewrite firstn_nil).
  reflexivity.
  case_eq n; intros.
   + reflexivity.
   + rewrite firstn_cons.
     rewrite concat_cons.
     assert (H' := H).
     rewrite Forall_forall in H'.
     assert (length a = k) as Hk.
     apply H'; apply in_cons_head.
     replace (S n0 * k) with (k + n0 * k) by auto.
     rewrite <- Hk.
     rewrite firstn_app_r.
     f_equal.
     rewrite Hk.
     apply IHlists.
     eapply Forall_cons2.
     eassumption.
Qed.
Lemma concat_hom_skipn : forall A (lists: list (list A)) n k,
  Forall (fun sublist => length sublist = k) lists ->
  skipn (n * k) (concat lists) = concat (skipn n lists).
(* hint proof tokens: 149 *)
Proof.
  intros.
  generalize dependent n.
  induction lists; intros; simpl.
  repeat (rewrite skipn_nil).
  reflexivity.
  case_eq n; intros.
   + reflexivity.
   + simpl.
     assert (H' := H).
     rewrite Forall_forall in H'.
     assert (length a = k) as Hk.
     apply H'. left; reflexivity.
     replace (S n0 * k) with (k + n0 * k) by auto.
     rewrite <- Hk.
     rewrite skipn_app_r.
     f_equal.
     rewrite Hk.
     apply IHlists.
     eapply Forall_cons2.
     eassumption.
Qed.
Lemma concat_hom_updN_first_skip : forall A n k (lists: list (list A)) (l: list A),
  Forall (fun sublist => length sublist = k) lists ->
  n < length lists ->
  firstn (n * k) (concat lists) ++ l ++
  skipn (n * k + k) (concat lists) = concat (updN lists n l).
Proof.
(* original proof tokens: 113 *)
intros.
rewrite concat_hom_firstn by assumption.
(* No more tactics to try *)
Admitted.

Lemma concat_hom_subselect_firstn : forall A n off k (l: list (list A)) (def: list A),
  Forall (fun sublist => length sublist = k) l ->
  off <= k ->
  n < length l ->
  firstn off (selN l n def) = firstn off (concat (skipn n l)).
Proof.
(* original proof tokens: 121 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma concat_hom_subselect_skipn : forall A n off k (l: list (list A)) (def: list A),
  Forall (fun sublist => length sublist = k) l ->
  off <= k ->
  n < length l ->
  skipn off (selN l n def) =
    firstn (k - off) (skipn off (concat (skipn n l))).
Proof.
(* original proof tokens: 132 *)
intros.
(* No more tactics to try *)
Admitted.

Fact div_ge_subt : forall a b, b <> 0 -> (a - b) / b = a / b - 1.
Proof.
(* original proof tokens: 79 *)
intros.
(* No more tactics to try *)
Admitted.

Fact mod_subt : forall a b, b >= a -> (b - a) mod a = b mod a.
(* hint proof tokens: 64 *)
Proof.
  intros.
  destruct (Compare_dec.le_lt_dec a 0).
  apply f_equal2_nat; lia.
  rewrite <- Nat.mod_add with (b := 1) by lia.
  rewrite Nat.mul_1_l.
  rewrite Nat.sub_add by lia.
  auto.
Qed.
Lemma selN_selN_firstn_hom : forall T (l : list (list T)) k nvalid off d1 d2 d3,
  Forall (fun sublist : list T => length sublist = k) (firstn nvalid l) ->
  off < nvalid * k ->
  off < k * length l -> selN (selN l (off / k) d1) (off mod k) d2 = selN (concat l) off d3.
(* hint proof tokens: 234 *)
Proof.
  induction l; intros;
    assert (k > 0) by (destruct (Nat.eq_dec k 0); lia).
  rewrite Nat.mul_0_r in *; lia.
  destruct nvalid; [> lia | ].
  match goal with [H : Forall _ _ |- _] => inversion H end; subst.
  destruct (Compare_dec.lt_dec off (length a)).
  - simpl; rewrite selN_app, Nat.div_small, Nat.mod_small; auto.
    apply selN_inb; auto.
  - rewrite Nat.nlt_ge in *.
    rewrite selN_cons.
    simpl in *; rewrite Nat.mul_comm in *; simpl in *; rewrite Nat.mul_comm in *.
    simpl; rewrite selN_app2 by auto.
    erewrite <- IHl by (eauto; lia).
    rewrite mod_subt; auto.
    rewrite <- div_ge_subt by lia.
    reflexivity.
    simpl in *; rewrite Nat.mul_comm in *; simpl in *; rewrite Nat.mul_comm in *.
    apply Nat.div_str_pos; lia.
Qed.
Lemma skipn_hom_concat: forall T k (l : list (list T)) n,
  Forall (fun x => length x = k) l ->
  k <> 0 ->
  skipn n (concat l) = skipn (n mod k) (selN l (n / k) nil) ++ concat (skipn (S (n / k)) l).
(* hint proof tokens: 167 *)
Proof.
  induction l; cbn; intros.
  repeat rewrite skipn_nil; auto.
  inversion H; subst.
  destruct (Compare_dec.lt_dec n (length a)).
  rewrite skipn_app_l by lia.
  rewrite Nat.mod_small by auto.
  rewrite Nat.div_small by auto.
  auto.
  replace n with (length a + (n - (length a))) at 1 by lia.
  rewrite skipn_app_r.
  rewrite IHl by auto.
  rewrite mod_subt by lia.
  rewrite div_ge_subt by auto.
  rewrite <- Nat.div_small_iff in * by auto.
  destruct (n / length a) eqn:?.
  congruence.
  cbn.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.
Lemma firstn_hom_concat: forall T k (l : list (list T)) n,
  Forall (fun x => length x = k) l ->
  k <> 0 ->
  firstn n (concat l) = concat (firstn (n / k) l) ++ firstn (n mod k) (selN l (n / k) nil).
(* hint proof tokens: 158 *)
Proof.
  induction l; cbn; intros.
  repeat rewrite firstn_nil; auto.
  inversion H; subst.
  destruct (Compare_dec.lt_dec n (length a)).
  rewrite firstn_app_l by lia.
  rewrite Nat.mod_small by auto.
  rewrite Nat.div_small by auto.
  auto.
  rewrite firstn_app by lia.
  rewrite firstn_oob by lia.
  rewrite IHl by auto.
  rewrite mod_subt by lia.
  rewrite div_ge_subt by auto.
  rewrite <- Nat.div_small_iff in * by auto.
  destruct (n / length a) eqn:?.
  congruence.
  cbn.
  rewrite Nat.sub_0_r.
  auto using app_assoc.
Qed.
Lemma selN_selN_hom : forall T (l : list (list T)) k off def,
  Forall (fun sublist => length sublist = k) l ->
  off < k * length l ->
  selN (selN l (off / k) nil) (Nat.modulo off k) def = selN (concat l) off def.
(* hint proof tokens: 39 *)
Proof.
  intros.
  eapply selN_selN_firstn_hom; auto.
  apply forall_firstn; auto.
  rewrite Nat.mul_comm; eauto.
Qed.
Definition combine_updN : forall A B i a b (va:A) (vb:B),
  List.combine (updN a i va) (updN b i vb) = updN (List.combine a b) i (va, vb).
Proof.
(* original proof tokens: 27 *)
intros.
induction a; induction b; simpl; try congruence; intros; subst; auto.
destruct i; simpl; try congruence.
destruct i; simpl; auto; try congruence.
(* No more tactics to try *)
Admitted.

Lemma combine_updN_l: forall A B (a : list A) (b : list B) i x d,
  combine (updN a i x) b = updN (combine a b) i (x, selN b i d).
(* hint proof tokens: 36 *)
Proof.
  intros.
  erewrite <- updN_selN_eq with (l := b) at 1.
  eauto using combine_updN.
Qed.
Lemma combine_updN_r: forall A B (a : list A) (b : list B) i x d,
  combine a (updN b i x) = updN (combine a b) i (selN a i d, x).
Proof.
(* original proof tokens: 36 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_combine : forall Ta Tb i a b (a0:Ta) (b0:Tb),
  length a = length b
  -> selN (List.combine a b) i (a0, b0) = pair (selN a i a0) (selN b i b0).
Proof.
(* original proof tokens: 30 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma combine_length_eq: forall A B (a : list A) (b : list B),
  length a = length b
  -> length (List.combine a b) = length a.
(* hint proof tokens: 19 *)
Proof.
  intros.
  rewrite combine_length.
  rewrite H; intuition.
Qed.
Lemma combine_length_eq2: forall A B (a : list A) (b : list B),
  length a = length b
  -> length (List.combine a b) = length b.
Proof.
(* original proof tokens: 19 *)
(* generated proof tokens: 14 *)
intros.
rewrite combine_length_eq; auto.
Qed.

Theorem combine_app: forall A B (al ar : list A) (bl br: list B),
  length al = length bl
  -> List.combine (al ++ ar) (bl ++ br) 
     = (List.combine al bl) ++ (List.combine ar br).
(* hint proof tokens: 32 *)
Proof.
  induction al; destruct bl; simpl; intros; try lia; auto.
  f_equal.
  apply IHal; lia.
Qed.
Theorem removeN_updN : forall V l i (v : V),
   removeN (updN l i v) i = removeN l i.
(* hint proof tokens: 34 *)
Proof.
   unfold removeN; intros.
   rewrite firstn_updN; auto.
   simpl; rewrite skipn_updN; auto.
Qed.
Theorem removeN_oob: forall A (l : list A) i,
  i >= length l -> removeN l i = l.
Proof.
(* original proof tokens: 36 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_head: forall A l i (a : A),
  removeN (a :: l) (S i) = a :: (removeN l i).
(* hint proof tokens: 13 *)
Proof.
  unfold removeN; firstorder.
Qed.
Theorem removeN_combine: forall A B i (a : list A) (b : list B),
  removeN (List.combine a b) i = List.combine (removeN a i) (removeN b i).
Proof.
(* original proof tokens: 69 *)
intros.
induction a; simpl; intros; try solve [auto; eauto with arith].
destruct b; simpl; auto; eauto.
rewrite removeN_nil.
rewrite removeN_nil.
auto.
rewrite removeN_nil.
rewrite removeN_nil.
auto.
destruct b; simpl; auto; try solve [eauto with arith].
rewrite removeN_nil.
(* No more tactics to try *)
Admitted.

Lemma removeN_length: forall A (l : list A) i,
  i < length l -> length (removeN l i) = length l - 1.
(* hint proof tokens: 56 *)
Proof.
  unfold removeN; induction l; intros; simpl.
  unfold length in H; lia.
  rewrite app_length.
  rewrite firstn_length; rewrite Nat.min_l; simpl in *; try lia.
  rewrite skipn_length; lia.
Qed.
Lemma removeN_length_eq: forall A B (a : list A) (b : list B) i,
  i < length a -> i < length b
  -> length (removeN a i) = length (removeN b i)
  -> length a = length b.
Proof.
(* original proof tokens: 48 *)
(* generated proof tokens: 29 *)
intros.
rewrite removeN_length in H1 by lia; rewrite removeN_length in H1 by lia; lia.
Qed.

Lemma removeN_tail: forall A (l : list A) a,
  removeN (l ++ a :: nil) (length l) = l.
(* hint proof tokens: 42 *)
Proof.
  intros; unfold removeN.
  rewrite skipn_oob.
  rewrite firstn_app2; eauto using app_nil_r.
  rewrite app_length; simpl; lia.
Qed.
Lemma selN_removelast : forall A n l (def : A),
  n < length l - 1
  -> selN (removelast l) n def = selN l n def.
(* hint proof tokens: 63 *)
Proof.
  induction l using rev_ind; destruct n;
  intros; simpl; intuition;
  rewrite removelast_app; try congruence;
  simpl; rewrite app_nil_r;
  rewrite selN_app; auto;
  rewrite app_length in H; simpl in H; lia.
Qed.
Lemma length_removelast : forall A (l : list A),
  l <> nil -> length (removelast l) = length l - 1.
Proof.
(* original proof tokens: 53 *)
destruct l; auto; try lia.
(* No more tactics to try *)
Admitted.

Lemma removeN_removelast : forall A (l : list A),
  length l > 0
  -> removeN l (length l - 1) = removelast l.
(* hint proof tokens: 74 *)
Proof.
  induction l using rev_ind; intros; simpl; firstorder.
  rewrite removelast_app; simpl.
  rewrite app_nil_r.
  rewrite app_length; simpl.
  replace (length l + 1 - 1) with (length l) by lia.
  rewrite removeN_tail; auto.
  congruence.
Qed.
Lemma in_removeN : forall T (l : list T) i x,
  In x (removeN l i) -> In x l.
Proof.
(* original proof tokens: 65 *)
intros.
apply in_app_or in H; auto.
(* No more tactics to try *)
Admitted.

Lemma in_removeN_neq: forall T (l : list T) x d i,
  In x l ->
  selN l i d <> x ->
  In x (removeN l i).
(* hint proof tokens: 56 *)
Proof.
  unfold removeN.
  intros.
  erewrite <- firstn_skipn with (n := i) in H.
  rewrite in_app_iff in *.
  intuition.
  right.
  eapply in_skipn_S; eauto.
Qed.
Lemma in_combine_ex_l: forall A B (a : list A) (b : list B),
  length a >= length b ->
  forall y, In y b -> exists x, In (x, y) (List.combine a b).
(* hint proof tokens: 55 *)
Proof.
  induction a; cbn; intros.
  destruct b; cbn in *; intuition lia.
  destruct b; cbn in *; intuition; subst.
  eauto.
  edestruct IHa; eauto.
  lia.
Qed.
Lemma in_combine_ex_r: forall A B (a : list A) (b : list B),
  length a <= length b ->
  forall x, In x a -> exists y, In (x, y) (List.combine a b).
Proof.
(* original proof tokens: 49 *)
intros.
induction a; cbn; intros; try lia; auto.
inversion H0; subst; clear H0.
(* No more tactics to try *)
Admitted.

Theorem firstn_removelast_eq : forall V (l : list V),
  length l > 0
  -> firstn (length l - 1) l = removelast l.
(* hint proof tokens: 73 *)
Proof.
  destruct l using rev_ind; firstorder.
  rewrite app_length; simpl.
  rewrite removelast_app; simpl; try congruence.
  replace (length l + 1 - 1) with (length l) by lia.
  rewrite firstn_app2; auto.
  rewrite app_nil_r; auto.
Qed.
Lemma firstn_app_le : forall A (a b : list A) n,
  length a <= n ->
    firstn n (a ++ b) = a ++ firstn (n - length a) b.
Proof.
(* original proof tokens: 44 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_repeat_le : forall n m A (x : A),
  n <= m ->
    firstn n (repeat x m) = repeat x n.
Proof.
(* original proof tokens: 36 *)
(* generated proof tokens: 14 *)
intros.
apply firstn_repeat; auto.
Qed.

Lemma firstn_app_split : forall T (l1 l2 : list T) n,
  firstn n (l1 ++ l2) = firstn n l1 ++ firstn (n - length l1) l2.
Proof.
(* original proof tokens: 74 *)
intros.
induction n; destruct l1; simpl; intros; try lia; auto.
f_equal.
(* No more tactics to try *)
Admitted.

Lemma selN_skip_first : forall T (l:list T) n m p def,
  n + m < p ->
    selN l (n + m) def = selN (skipn n (firstn p l)) m def.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Definition setlen A l n (def : A) :=
  firstn n l ++ (repeat def (n - length l)).
Lemma repeat_is_nil : forall T (v : T) n,
  n = 0 -> repeat v n = nil.
(* hint proof tokens: 15 *)
Proof.
  intros; subst; unfold repeat; auto.
Qed.
Lemma setlen_length : forall A l n (def : A),
  length (setlen l n def) = n.
Proof.
(* original proof tokens: 71 *)
unfold setlen; simpl.
(* No more tactics to try *)
Admitted.

Lemma setlen_nil : forall A n (def : A),
  setlen nil n def = repeat def n.
Proof.
(* original proof tokens: 36 *)
unfold setlen; simpl; auto.
intros.
rewrite repeat_is_nil; auto.
(* No more tactics to try *)
Admitted.

Lemma list_isloate_len : forall A tl hd (x : A),
  length (hd ++ x :: tl) = length hd + S (length tl).
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma updN_0_skip_1: forall A l (a: A),
  length l > 0 -> updN l 0 a = a :: skipn 1 l .
Proof.
(* original proof tokens: 22 *)
(* generated proof tokens: 27 *)

unfold selN; simpl; intros; destruct l; simpl in *; try lia; auto.
Qed.

Lemma skipn_map_comm : forall A B n (l : list A) (f : A -> B),
  skipn n (map f l) = map f (skipn n l).
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 30 *)
unfold skipn; induction n; intros; simpl; auto.
destruct l; simpl; auto; apply IHn.
Qed.

Lemma firstn_map_comm : forall A B n (l : list A) (f : A -> B),
  firstn n (map f l) = map f (firstn n l).
(* hint proof tokens: 28 *)
Proof.
  induction n; intros; auto.
  destruct l; simpl; auto.
  rewrite IHn; auto.
Qed.
Lemma removeN_map_comm: forall T T' (f : T -> T') i l,
  removeN (map f l) i = map f (removeN l i).
Proof.
(* original proof tokens: 31 *)
unfold removeN; simpl.
intros.
rewrite firstn_map_comm.
rewrite map_app.
(* No more tactics to try *)
Admitted.

Lemma skipn_firstn_comm : forall A n m (l : list A),
  skipn n (firstn (n + m) l) = firstn m (skipn n l).
(* hint proof tokens: 26 *)
Proof.
  induction n; destruct l; intros; simpl; auto.
  rewrite firstn_nil; auto.
Qed.
Lemma setlen_app_r : forall A n (a b : list A) e0,
  n >= length a ->
  setlen (a ++ b) n e0 = a ++ setlen b (n - length a) e0.
(* hint proof tokens: 43 *)
Proof.
  unfold setlen; intros; simpl.
  rewrite firstn_app_le by auto.
  rewrite app_assoc.
  autorewrite with lists.
  f_equal; f_equal; lia.
Qed.
Lemma setlen_repeat : forall A m n (a : A),
  setlen (repeat a n) m a = repeat a m.
(* hint proof tokens: 96 *)
Proof.
  unfold setlen; intros.
  destruct (Compare_dec.le_gt_dec m n).
  rewrite firstn_repeat by auto.
  rewrite repeat_app, repeat_length.
  replace (m + (m - n)) with m by lia; auto.
  
  rewrite firstn_oob by (rewrite repeat_length; lia).
  rewrite repeat_app, repeat_length.
  replace (n + (m - n)) with m by lia; auto.
Qed.
Lemma skipn_app_r_ge : forall A n (a b : list A),
  n >= length a ->
  skipn n (a ++ b) = skipn (n - length a) b.
(* hint proof tokens: 78 *)
Proof.
  induction n; intros; auto.
  replace a with (@nil A); auto.
  rewrite length_nil; auto; lia.
  destruct a, b; simpl; auto.
  rewrite app_nil_r, skipn_nil, skipn_oob; auto.
  simpl in H; lia.
  apply IHn.
  simpl in H; lia.
Qed.
Lemma firstn_map_exact : forall A B (l : list A) (f : A -> B),
  firstn (length l) (map f l) = map f l.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma combine_map_fst_snd: forall A B (l: list (A * B)),
  List.combine (map fst l) (map snd l) = l.
(* hint proof tokens: 27 *)
Proof.
  induction l; simpl; auto.
  rewrite IHl; rewrite <- surjective_pairing; auto.
Qed.
Lemma combine_map: forall T A' B' (l : list T) (f : _ -> A') (g : _ -> B'),
  map (fun x => (f x, g x)) l = combine (map f l) (map g l).
Proof.
(* original proof tokens: 24 *)
induction l; cbn; auto.
(* No more tactics to try *)
Admitted.

Lemma combine_map': forall T T' A' B' (a : list T) (b : list T') (f : _ -> A') (g : _ -> B'),
  map (fun x => (f (fst x), g (snd x))) (combine a b) = combine (map f a) (map g b).
(* hint proof tokens: 33 *)
Proof.
  induction a; cbn; intros.
  auto.
  destruct b; cbn; auto.
  f_equal; eauto.
Qed.
Lemma combine_map_l : forall A B C (a : list A) (b : list B) (f : _ -> C),
  combine (map f a) b = map (fun ab => (f (fst ab), snd ab)) (combine a b).
(* hint proof tokens: 30 *)
Proof.
  intros.
  setoid_rewrite combine_map' with (g := id).
  rewrite map_id.
  auto.
Qed.
Lemma combine_map_r : forall A B C (a : list A) (b : list B) (f : _ -> C),
  combine a (map f b) = map (fun ab => (fst ab, f (snd ab))) (combine a b).
Proof.
(* original proof tokens: 30 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma map_fst_combine: forall A B (a: list A) (b: list B),
  length a = length b -> map fst (List.combine a b) = a.
(* hint proof tokens: 43 *)
Proof.
  unfold map, List.combine; induction a; intros; auto.
  destruct b; try discriminate; simpl in *.
  rewrite IHa; [ auto | congruence ].
Qed.
Lemma map_snd_combine: forall A B (a: list A) (b: list B),
  length a = length b -> map snd (List.combine a b) = b.
(* hint proof tokens: 36 *)
Proof.
  unfold map, List.combine.
  induction a; destruct b; simpl; auto; try discriminate.
  intros; rewrite IHa; eauto.
Qed.
Lemma map_snd_updN : forall A B (l : list (A*B)) a v,
  map snd (updN l a v) = updN (map snd l) a (snd v).
(* hint proof tokens: 31 *)
Proof.
  induction l; intros; simpl; auto.
  destruct a0; simpl; auto.
  rewrite IHl; auto.
Qed.
Lemma map_fst_map_eq : forall A B (ents : list (A * B)) C (f : B -> C),
  map fst ents = map fst (map (fun e => (fst e, f (snd e))) ents).
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma map_snd_map_eq : forall A B (ents : list (A * B)) C (f : B -> C),
  map snd (map (fun e => (fst e, f (snd e))) ents) = map f (map snd ents).
Proof.
(* original proof tokens: 24 *)
unfold map.
(* No more tactics to try *)
Admitted.

Lemma NoDup_skipn : forall A (l : list A) n,
  NoDup l -> NoDup (skipn n l).
Proof.
(* original proof tokens: 37 *)
induction l; auto; intros; simpl; inversion H.
(* No more tactics to try *)
Admitted.

Lemma NoDup_app_l : forall A (a b : list A),
  NoDup (a ++ b) -> NoDup a.
(* hint proof tokens: 41 *)
Proof.
  induction a; simpl; intros.
  constructor.
  inversion H; constructor; eauto.
  intro; apply H2.
  apply in_or_app; eauto.
Qed.
Lemma NoDup_app_r : forall A (a b : list A),
  NoDup (a ++ b) -> NoDup b.
Proof.
(* original proof tokens: 23 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDup_remove_mid : forall A (a b c : list A),
  NoDup (a ++ b ++ c) -> NoDup (a ++ c).
Proof.
(* original proof tokens: 44 *)
intros.
(* No more tactics to try *)
Admitted.

Hint Resolve in_app_or.
Hint Resolve in_or_app.
Lemma not_In_NoDup_app : forall T (a : T) l1 l2,
  In a l1 -> NoDup (l1 ++ l2) -> ~ In a l2.
Proof.
(* original proof tokens: 42 *)
intros.
apply NoDup_app_r in H0; auto.
inversion H0; auto.
destruct H0; auto.
intros; inversion H3; subst; auto.
inversion H3; subst; auto.
(* No more tactics to try *)
Admitted.

Lemma in_nodup_split : forall T (a : T) l1 l2,
  In a (l1 ++ l2) -> NoDup (l1 ++ l2) -> ~ In a l2 -> In a l1.
Proof.
(* original proof tokens: 32 *)
(* generated proof tokens: 16 *)
intros.
apply in_app_or in H; intuition.
Qed.

Lemma NoDup_app_comm : forall T (l1 l2 : list T),
  NoDup (l1 ++ l2) ->
  NoDup (l2 ++ l1).
(* hint proof tokens: 77 *)
Proof.
  induction l2; simpl; intros; try rewrite app_nil_r in *; eauto.
  constructor.
  intro H'. apply in_app_or in H'.
  eapply NoDup_remove_2; eauto.
  apply in_or_app; intuition.
  eapply IHl2; eapply NoDup_remove_1; eauto.
Qed.
Lemma NoDup_3app_rev : forall T (l1 l2 l3 : list T),
  NoDup (l3 ++ l2 ++ l1) ->
  NoDup (l1 ++ l2 ++ l3).
(* hint proof tokens: 130 *)
Proof.
  induction l1; simpl; intros.
  rewrite app_nil_r in *. eapply NoDup_app_comm; eauto.
  rewrite app_assoc in H. apply NoDup_app_comm in H. simpl in H.
  inversion H; subst.
  constructor.
  - intro H'. apply H2.
    apply in_or_app. apply in_app_or in H'. intuition. right.
    apply in_or_app. apply in_app_or in H0. intuition.
  - eapply IHl1.
    apply NoDup_app_comm in H3. rewrite <- app_assoc in H3. eauto.
Qed.
Lemma in_nodup_firstn_not_skipn: forall T (l : list T) n x,
  NoDup l ->
  In x (firstn n l) -> ~In x (skipn n l).
Proof.
(* original proof tokens: 31 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma in_nodup_not_skipn_firstn: forall T (l : list T) n x,
  NoDup l -> In x l ->
  ~In x (skipn n l) -> In x (firstn n l).
(* hint proof tokens: 27 *)
Proof.
  intros.
  eapply in_nodup_split; rewrite ?firstn_skipn; eauto.
Qed.
Lemma in_map_fst_exists_snd : forall A B (l : list (A * B)) a,
  In a (map fst l) -> exists b, In (a, b) l.
(* hint proof tokens: 27 *)
Proof.
  induction l; simpl; firstorder.
  destruct a; simpl in *; subst; eauto.
Qed.
Lemma setlen_In : forall A n l (a def : A),
  In a (setlen l n def)
  -> a = def \/ In a l.
(* hint proof tokens: 90 *)
Proof.
  unfold setlen; intros.
  destruct (Compare_dec.le_dec n (length l)).
  right.
  rewrite repeat_is_nil in H by lia; rewrite app_nil_r in H.
  eapply in_firstn_in; eauto.
  apply in_app_or in H; destruct H.
  right. eapply in_firstn_in; eauto.
  left. eapply repeat_spec; eauto.
Qed.
Lemma updN_skipn : forall A l i n (v : A),
  updN (skipn n l) i v = skipn n (updN l (i + n) v).
Proof.
(* original proof tokens: 237 *)

(* No more tactics to try *)
Admitted.

Lemma setlen_skipn_updN_absorb : forall A (l : list A) m n i v def,
  i < n \/ i >= m + n ->
  setlen (skipn n (updN l i v)) m def = setlen (skipn n l) m def.
(* hint proof tokens: 64 *)
Proof.
  intros; destruct H.
  rewrite skipN_updN'; auto.
  unfold setlen.
  repeat rewrite <- skipn_firstn_comm.
  rewrite firstn_updN_oob by lia.
  repeat rewrite skipn_length.
  rewrite length_updN; auto.
Qed.
Lemma setlen_inbound : forall A n (l : list A) def,
  n <= length l ->
  setlen l n def = firstn n l.
(* hint proof tokens: 36 *)
Proof.
  unfold setlen; intros.
  replace (n - length l) with 0 by lia.
  simpl; rewrite app_nil_r; auto.
Qed.
Lemma setlen_oob : forall A n (l : list A) def,
  n >= length l ->
  setlen l n def = l ++ repeat def (n - length l).
(* hint proof tokens: 23 *)
Proof.
  unfold setlen; intros.
  rewrite firstn_oob by lia; auto.
Qed.
Lemma setlen_exact : forall A n (l : list A) def,
  n = length l ->
  setlen l n def = l.
(* hint proof tokens: 41 *)
Proof.
  unfold setlen; intros; subst.
  rewrite firstn_oob by lia; auto.
  rewrite Nat.sub_diag; simpl.
  rewrite app_nil_r; auto.
Qed.
Lemma selN_map_eq: forall T T' (f : T -> T') (l l' : list T) d,
  (forall i, f (selN l i d) = f (selN l' i d)) ->
  length l = length l' ->
  map f l = map f l'.
(* hint proof tokens: 72 *)
Proof.
  induction l; cbn; intros.
  rewrite length_nil; auto.
  autorewrite with list. auto.
  destruct l'; cbn in *. lia.
  rewrite (H 0).
  f_equal; auto.
  eapply IHl.
  intros i. apply (H (S i)).
  lia.
Qed.
Lemma combine_repeat : forall A B n (a : A) (b : B),
  combine (repeat a n) (repeat b n) = repeat (a, b) n.
(* hint proof tokens: 21 *)
Proof.
  induction n; simpl; intros; auto.
  f_equal; auto.
Qed.
Lemma Forall_selN : forall A (l : list A) P i def,
  Forall P l -> i < length l -> P (selN l i def).
Proof.
(* original proof tokens: 29 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_Forall : forall A (l : list A) (P : A -> Prop) def,
  (forall i, i < length l -> P (selN l i def)) ->
  Forall P l.
Proof.
(* original proof tokens: 51 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem remove_not_In :
  forall T dec (a : T) l, ~ In a l -> remove dec a l = l.
Proof.
(* original proof tokens: 55 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem remove_still_In : forall T dec (a b : T) l,
  In a (remove dec b l) -> In a l.
Proof.
(* original proof tokens: 53 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem remove_still_In_ne : forall T dec (a b : T) l,
  In a (remove dec b l) -> b <> a.
(* hint proof tokens: 45 *)
Proof.
  induction l; simpl; [tauto|].
  destruct (dec b a0).
  assumption.
  intro H. destruct H. subst. auto.
  apply IHl; assumption.
Qed.
Theorem remove_other_In : forall T dec (a b : T) l,
  b <> a -> In a l -> In a (remove dec b l).
Proof.
(* original proof tokens: 65 *)
intros.
induction l; simpl; auto; intros; destruct (dec b a); subst; auto; eauto.
destruct (dec a a0); auto; eauto.
apply IHl; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; subst; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
inversion H0; auto.
(* Reached max number of model calls *)
Admitted.

Lemma NoDup_remove : forall T (l : list T) v EQ,
  NoDup l ->
  NoDup (remove EQ v l).
Proof.
(* original proof tokens: 54 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma remove_cons_eq: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l: list T) a,
  NoDup (a :: l) ->
  remove E a (a :: l) = l.
Proof.
(* original proof tokens: 161 *)
(* generated proof tokens: 36 *)
intros.
simpl.
inversion H; subst.
destruct (E a a); auto; try congruence.
apply remove_not_In; auto.
Qed.

Lemma remove_cons_neq: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l: list T) a b,
  a <> b ->
  remove E a (b :: l) = b :: remove E a l.
(* hint proof tokens: 51 *)
Proof.
  induction l; intros; subst.
  - simpl.
    destruct (E a b); subst; try congruence.
  - unfold remove.
    destruct (E a0 b); subst; try congruence.
Qed.
Lemma remove_comm: forall T E x x' (l : list T),
  remove E x' (remove E x l) = remove E x (remove E x' l).
Proof.
(* original proof tokens: 30 *)
induction l; simpl; intros; auto.
destruct (E x a); subst; auto.
destruct (E x' a); auto.
rewrite IHl.
destruct (E x' a); auto; try congruence.
destruct (E x' a); simpl; auto; try congruence.
destruct (E a a); simpl; auto; try congruence.
destruct (E x' a); simpl; auto; rewrite IHl; auto; try congruence.
destruct (E x' a); auto.
case (E x' a); auto.
case e; subst; auto.
(* No more tactics to try *)
Admitted.

Lemma remove_same: forall T E x y (l : list T),
  x = y ->
  remove E x (remove E y l) = remove E x l.
Proof.
(* original proof tokens: 49 *)
intros.
rewrite H.
(* No more tactics to try *)
Admitted.

Lemma remove_cons: forall T E x (l : list T),
  remove E x (x :: l) = remove E x l.
(* hint proof tokens: 18 *)
Proof.
  cbn; intros; destruct E; congruence.
Qed.
Lemma selN_cons_fold : forall A (a : A) l i def,
  match i with | O => a | S n' => selN l n' def end = selN (a :: l) i def.
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 17 *)

intros.
simpl.
destruct i; auto.
Qed.

Lemma removeN_0_skipn : forall A n (l : list A),
  removeN (skipn n l) 0 = skipn (S n) l.
Proof.
(* original proof tokens: 17 *)
unfold removeN; simpl.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto.
destruct l; simpl; auto; destruct n; simpl; auto; try lia.
destruct l; simpl; auto; destruct n; simpl; auto; try lia.
destruct l; simpl; auto; destruct n; simpl; auto; try lia.
destruct l; simpl; auto; destruct n; simpl; auto; try lia.
destruct l; simpl; auto; destruct n; simpl; auto; try lia.
destruct l; simpl; auto; destruct n; simpl; auto; try lia.
(* Reached max number of model calls *)
Admitted.

Lemma skipn_firstn_length_eq : forall A B (a : list A) (b : list B) n,
  length (firstn n a) = length (firstn n b) ->
  length (skipn n a) = length (skipn n b) ->
  length a = length b.
(* hint proof tokens: 128 *)
Proof.
  intros.
  repeat rewrite firstn_length in H.
  repeat rewrite skipn_length in H0.
  destruct (Compare_dec.le_dec n (length a)); destruct (Compare_dec.le_dec n (length b)).
  lia.
  rewrite Nat.min_l in H by auto.
  rewrite Nat.min_r in H by lia; subst.
  lia.
  rewrite Nat.min_r in H by lia.
  rewrite Nat.min_l in H by lia; subst.
  lia.
  rewrite Nat.min_r in H by lia.
  rewrite Nat.min_r in H by lia; subst.
  lia.
Qed.
Lemma Forall_map : forall A B (l : list A) P (f : A -> B),
  Forall (fun x => P (f x)) l <->
  Forall P (map f l).
Proof.
(* original proof tokens: 47 *)
(* generated proof tokens: 48 *)
split; intros; induction l; simpl; auto; constructor; auto.
inversion H; auto.
inversion H; auto.
inversion H; auto.
apply Forall_cons2 in H; auto.
Qed.

Lemma Forall_map_l : forall A B C P (l : list A) (b : B) (f : A -> C),
  Forall (fun a => P (f a) b) l <->
  Forall (fun a => P a b) (map f l).
Proof.
(* original proof tokens: 40 *)
split; intros; repeat rewrite Forall_forall; intros; subst.
apply in_map_iff in H0; subst.
(* No more tactics to try *)
Admitted.

Lemma Forall_map_r : forall A B C P (l : list A) (b : B) (f : A -> C),
  Forall (fun a => P b (f a)) l <->
  Forall (fun a => P b a) (map f l).
(* hint proof tokens: 40 *)
Proof.
  induction l; simpl; split; intros;
  try apply Forall_nil; inversion H;
  subst; firstorder.
  apply Forall_cons; firstorder.
Qed.
Lemma Forall_remove : forall A (l : list A) a P EQ,
  Forall P l ->
  Forall P (remove EQ a l).
(* hint proof tokens: 33 *)
Proof.
  induction l; simpl; intros; eauto.
  inversion H; subst.
  destruct (EQ a0 a); eauto.
Qed.
Lemma forall2_length : forall A B (a : list A) (b : list B) P,
  Forall2 P a b -> length a = length b.
(* hint proof tokens: 14 *)
Proof.
  induction 1; simpl; auto.
Qed.
Lemma forall2_forall : forall A B (a : list A) (b : list B) P,
  Forall2 P a b -> Forall (fun x => P (fst x) (snd x)) (combine a b).
(* hint proof tokens: 14 *)
Proof.
  induction 1; simpl; auto.
Qed.
Lemma forall_forall2 : forall A B (a : list A) (b : list B) P,
  Forall (fun x => P (fst x) (snd x)) (combine a b) ->
  length a = length b ->
  Forall2 P a b.
(* hint proof tokens: 40 *)
Proof.
  induction a; destruct b; firstorder.
  inversion H0.
  inversion H0.
  inversion H; subst; simpl in *.
  constructor; auto.
Qed.
Lemma forall2_forall_l' : forall A B (la : list A) (lb : list B) P,
  Forall2 P la lb -> Forall (fun a => exists b, P a b) la.
(* hint proof tokens: 31 *)
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.
Lemma forall2_forall_l : forall A B (la : list A) (lb : list B) P,
  Forall2 (fun a b => P a) la lb -> Forall P la.
(* hint proof tokens: 31 *)
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.
Lemma forall2_forall_r' : forall A B (la : list A) (lb : list B) P,
  Forall2 P la lb -> Forall (fun b => exists a, P a b) lb.
(* hint proof tokens: 31 *)
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.
Lemma forall2_forall_r : forall A B (la : list A) (lb : list B) P,
  Forall2 (fun a b => P b) la lb -> Forall P lb.
Proof.
(* original proof tokens: 31 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall_forall2_l : forall A B (la : list A) (lb : list B) P,
  length la = length lb -> Forall P la -> Forall2 (fun a b => P a) la lb.
Proof.
(* original proof tokens: 39 *)
induction la; simpl; intros; auto.
inversion H0; subst; clear H0.
(* No more tactics to try *)
Admitted.

Lemma forall_forall2_r : forall A B (la : list A) (lb : list B) P,
  length la = length lb -> Forall P lb -> Forall2 (fun a b => P b) la lb.
Proof.
(* original proof tokens: 39 *)
intros.
induction la; simpl; intros; inversion H0; subst; auto.
inversion H.
inversion H.
constructor; auto.
inversion H0; subst; eauto.
inversion H0; subst; eauto.
inversion H0; subst; eauto.
inversion H0; subst; auto.
inversion H0; subst; eauto.
inversion H0; subst; eauto.
(* No more tactics to try *)
Admitted.

Lemma forall2_impl : forall A B (la : list A) (lb : list B) (P Q : A -> B -> Prop),
  Forall2 P la lb ->
  Forall2 (fun a b => P a b -> Q a b) la lb ->
  Forall2 Q la lb.
Proof.
(* original proof tokens: 55 *)
induction la; destruct lb; simpl; intros; auto.
inversion H0; subst; auto.
inversion H0; subst.
constructor.
(* No more tactics to try *)
Admitted.

Lemma forall2_lift : forall A B (la : list A) (lb : list B) (P : A -> B -> Prop),
  (forall a b, P a b) ->
  length la = length lb ->
  Forall2 P la lb.
Proof.
(* original proof tokens: 34 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall2_selN : forall A B (a : list A) (b : list B) P n ad bd,
  Forall2 P a b ->
  n < length a ->
  P (selN a n ad) (selN b n bd).
Proof.
(* original proof tokens: 63 *)

(* No more tactics to try *)
Admitted.

Lemma forall2_updN : forall A B P (a : list A) (b : list B) xa xb i,
  Forall2 P a b ->
  P xa xb ->
  Forall2 P (updN a i xa) (updN b i xb).
(* hint proof tokens: 59 *)
Proof.
  intros.
  apply forall_forall2.
  rewrite combine_updN.
  apply Forall_updN; auto.
  apply forall2_forall; auto.
  repeat rewrite length_updN.
  eapply forall2_length; eauto.
Qed.
Lemma selN_Forall2 : forall A B (a : list A) (b : list B) (P : A -> B -> Prop) da db,
  length a = length b ->
  (forall i, i < length a -> P (selN a i da) (selN b i db)) ->
  Forall2 P a b.
Proof.
(* original proof tokens: 83 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall2_map2_in: forall  A (l1 : list A) B l2 T1 T2 (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) (f1 : A -> T1) (f2 : B -> T2),
    (forall a b, In a l1 -> In b l2 -> q a b -> p (f1 a) (f2 b)) ->
    Forall2 q l1 l2 ->
    Forall2 p (map f1 l1) (map f2 l2).
Proof.
(* original proof tokens: 89 *)
intros.
induction H0; simpl; auto.
constructor.
apply H; auto; constructor.
(* No more tactics to try *)
Admitted.

Lemma forall2_map2_selN: forall  A (l1 : list A) B l2 T1 T2 (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) (f1 : A -> T1) (f2 : B -> T2) def1 def2,
    (forall a b n, n < Datatypes.length l1 -> selN l1 n def1 = a -> selN l2 n def2 = b -> q a b -> p (f1 a) (f2 b)) ->
    Forall2 q l1 l2 ->
    Forall2 p (map f1 l1) (map f2 l2).
(* hint proof tokens: 140 *)
Proof.
  intros.
  induction H0.
  - simpl. eapply Forall2_nil.
  - constructor.
    specialize (H x y 0).
    eapply H; eauto.
    simpl; lia.
    eapply IHForall2; intros.
    eapply H; eauto.
    instantiate (1 := (S n)).
    simpl; lia.
    rewrite selN_cons; eauto.
    replace (S n - 1) with n by lia; eauto.
    lia.
    rewrite selN_cons; eauto.
    replace (S n - 1) with n by lia; eauto.
    lia.
Qed.
Lemma Forall2_eq : forall T (l l' : list T),
  Forall2 eq l l' -> l = l'.
Proof.
(* original proof tokens: 35 *)
(* generated proof tokens: 20 *)

induction 1; auto; cbn; congruence.
Qed.

Lemma Forall2_to_map_eq : forall T U l l' (R : T -> T -> Prop) (f : T -> U),
  (forall a b, R a b -> f a = f b) ->
  Forall2 R l l' ->
  map f l = map f l'.
(* hint proof tokens: 27 *)
Proof.
  intros.
  apply Forall2_eq.
  eapply forall2_map2_in; eauto.
Qed.
Definition cuttail A n (l : list A) := firstn (length l - n) l.
Lemma cuttail_length : forall A (l : list A) n,
  length (cuttail n l) = length l - n.
Proof.
(* original proof tokens: 26 *)
unfold cuttail.
(* No more tactics to try *)
Admitted.

Lemma cuttail_0 : forall A (l : list A),
  cuttail 0 l = l.
(* hint proof tokens: 23 *)
Proof.
  unfold cuttail; intros.
  rewrite firstn_oob by lia; auto.
Qed.
Lemma cuttail_oob : forall A (l : list A) n,
  n >= length l -> cuttail n l = nil.
(* hint proof tokens: 31 *)
Proof.
  unfold cuttail; intros.
  replace (length l - n) with 0 by lia.
  simpl; auto.
Qed.
Lemma last_selN : forall A (l : list A) def,
  last l def = selN l (length l - 1) def.
(* hint proof tokens: 70 *)
Proof.
  induction l; intuition; simpl.
  rewrite Nat.sub_0_r, IHl.
  case_eq (length l); intros.
  erewrite length_nil with (l := l); auto.
  destruct l.
  inversion H.
  replace (S n - 1) with n by lia; auto.
Qed.
Lemma last_cuttail_selN : forall A n (l : list A) def,
  n < length l ->
  last (cuttail n l) def = selN l (length l - n - 1) def.
Proof.
(* original proof tokens: 47 *)
(* generated proof tokens: 35 *)
unfold cuttail.
intros.
rewrite last_selN.
rewrite firstn_length_l by lia.
rewrite selN_firstn by lia; auto.
Qed.

Lemma cuttail_cuttail : forall A (l : list A) m n,
  cuttail m (cuttail n l) = cuttail (n + m) l.
(* hint proof tokens: 59 *)
Proof.
  unfold cuttail; intros.
  rewrite firstn_firstn, firstn_length.
  f_equal.
  apply Nat.min_case_strong; intros.
  apply Nat.min_case_strong; intros; lia.
  rewrite Nat.min_l in H; lia.
Qed.
Lemma cuttail_tail : forall A (l : list A) a n,
  cuttail (S n) (l ++ [a]) = cuttail n l.
Proof.
(* original proof tokens: 52 *)
unfold cuttail; simpl.
(* No more tactics to try *)
Admitted.

Lemma selN_cuttail : forall A n (l : list A) idx def,
  idx < length (cuttail n l) ->
  selN (cuttail n l) idx def = selN l idx def.
Proof.
(* original proof tokens: 66 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma cuttail_cons : forall A (a : A) l n,
  n <= length l ->
  cuttail n (a :: l) = a :: (cuttail n l).
Proof.
(* original proof tokens: 44 *)
unfold cuttail; intros; simpl.
destruct n; simpl; auto; try lia.
(* No more tactics to try *)
Admitted.

Lemma cuttail_app_one: forall T (l : list T) n i d,
  n < length l ->
  i = length l - S n ->
  cuttail (S n) l ++ [selN l i d] = cuttail n l.
(* hint proof tokens: 56 *)
Proof.
  unfold cuttail.
  intros; subst.
  destruct (length l) eqn:?. lia.
  rewrite Nat.sub_succ, Nat.sub_succ_l by lia.
  erewrite firstn_S_selN; auto.
  lia.
Qed.
Lemma cuttail_concat_hom: forall T (l : list (list T)) n k,
  (Forall (fun x => length x = k) l) ->
  cuttail (n * k) (concat l) = concat (cuttail n l).
Proof.
(* original proof tokens: 48 *)
intros.
induction l; simpl; auto; intros.
rewrite <- concat_cons.
(* No more tactics to try *)
Admitted.

Lemma incl_cons2 : forall T (a b : list T) (v : T), 
  incl a b
  -> incl (v :: a) (v :: b).
Proof.
(* original proof tokens: 9 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_nil : forall T (l : list T), 
  incl nil l.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma incl_in_nil : forall T (l : list T),
  incl l nil -> l = nil.
Proof.
(* original proof tokens: 33 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_remove : forall T dec (a : T) (l : list T),
  incl (remove dec a l) l.
(* hint proof tokens: 40 *)
Proof.
  induction l; unfold incl; simpl; auto; intros.
  destruct (dec a a0); subst; eauto.
  inversion H; subst; eauto.
Qed.
Fixpoint upd_range {T} l start len (v : T) :=
  match len with
  | 0 => l
  | S len' => updN (upd_range l (S start) len' v) start v
  end.
Fixpoint upd_range_fast {T} vs start len (v : T) :=
  match vs with
  | nil => nil
  | v' :: vs' =>
    match start with
    | S start' => v' :: upd_range_fast vs' start' len v
    | O =>
      match len with
      | O => v' :: vs'
      | S len' => v :: upd_range_fast vs' O len' v
      end
    end
  end.
Lemma upd_range_0 : forall T l start (v : T),
  upd_range l start 0 v = l.
Proof.
(* original proof tokens: 8 *)
(* generated proof tokens: 10 *)

reflexivity.
Qed.

Lemma upd_range_length : forall T l start len (v : T),
  length (upd_range l start len v) = length l.
(* hint proof tokens: 49 *)
Proof.
  intros T l start len.
  generalize dependent l.
  generalize dependent start.
  induction len; intros; auto.
  unfold upd_range in *. simpl.
  rewrite length_updN. auto.
Qed.
Lemma upd_range_selN : forall T l start len (v : T) n d,
  start <= n < start + len ->
  n < length l ->
  selN (upd_range l start len v) n d = v.
Proof.
(* original proof tokens: 86 *)
intros.
(* No more tactics to try *)
Admitted.

Definition upd_range' T l start len (v : T) :=
  firstn start l ++ repeat v len ++ skipn (start + len) l.
Lemma upd_range_eq_upd_range' : forall T (l : list T) start len v,
  start + len <= length l ->
  upd_range l start len v = upd_range' l start len v.
(* hint proof tokens: 151 *)
Proof.
  intros T l start len.
  generalize dependent l.
  generalize dependent start.
  induction len; intros. simpl.
  - unfold upd_range'. rewrite Nat.add_0_r. simpl.
    rewrite firstn_skipn. auto.
  - simpl. rewrite IHlen by lia.
    unfold upd_range'. simpl repeat.
    erewrite firstn_S_selN by lia.
    repeat rewrite <- app_assoc.
    rewrite updN_app2. rewrite updN_app1.
    all : rewrite firstn_length_l by lia.
    rewrite Plus.plus_Snm_nSm.
    rewrite Nat.sub_diag. simpl. auto.
    all : simpl; lia.
  Unshelve.
  eauto.
Qed.
Theorem upd_range_fast_eq_upd_range' : forall T (l: list T) start len v,
    start + len <= length l ->
    upd_range_fast l start len v = upd_range' l start len v.
(* hint proof tokens: 100 *)
Proof.
  unfold upd_range'.
  induction l; simpl; intros.
  - assert (start = 0) by lia.
    assert (len = 0) by lia.
    subst; auto.
  - destruct start, len; simpl.
    unfold upd_range'; simpl; auto.
    erewrite IHl; eauto; try lia.
    erewrite IHl; eauto; try lia.
    erewrite IHl; eauto; try lia.
Qed.
Lemma upd_range_concat_hom_small : forall T l start len (v : T) k d,
  start + len <= length (concat l) ->
  Forall (fun l' => length l' = k) l ->
  start mod k + len <= k ->
  0 < k -> 0 < len ->
  upd_range (concat l) start len v =
  concat (updN l (start / k) (upd_range (selN l (start / k) d) (start mod k) len v)).
(* hint proof tokens: 446 *)
Proof.
  intros. assert (k <> 0) by lia.
  match goal with [H : context [length (concat _)]|- _ ] =>
    pose proof H; erewrite concat_hom_length in H by eauto end.
  repeat rewrite upd_range_eq_upd_range'.
  unfold upd_range'.
  erewrite <- concat_hom_updN_first_skip; eauto.
  erewrite concat_hom_subselect_firstn; eauto.
  erewrite <- concat_hom_skipn; eauto.
  rewrite <- skipn_firstn_comm. rewrite Nat.mul_comm. rewrite <- Nat.div_mod by auto.
  erewrite <- Nat.min_l with (n := _ * _) at 1. rewrite <- firstn_firstn.
  repeat rewrite app_assoc. rewrite firstn_skipn.
  repeat rewrite <- app_assoc. repeat f_equal.
  erewrite concat_hom_subselect_skipn; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite Minus.le_plus_minus_r by auto.
  erewrite <- concat_hom_skipn; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite skipn_skipn. rewrite Nat.add_shuffle0.
  rewrite Nat.add_comm with (m := _ * _). rewrite Nat.mul_comm. rewrite <- Nat.div_mod by auto.
  remember (k - start mod k - len) as e.
  replace k with (start mod k + len + e) at 3 6 by lia.
  repeat rewrite Nat.add_assoc. rewrite <- Nat.div_mod by auto.
  rewrite skipn_firstn_comm.
  rewrite Nat.add_comm with (m := e).
  repeat rewrite <- skipn_skipn.
  rewrite firstn_skipn. auto.
  all : try (apply Nat.div_lt_upper_bound; auto; rewrite Nat.mul_comm; lia).
  all : try apply Nat.mul_div_le; auto.
  - lia.
  - eapply Nat.le_trans; eauto. apply Nat.eq_le_incl.
    symmetry. apply Forall_selN; auto.
    apply Nat.div_lt_upper_bound; auto. rewrite Nat.mul_comm; lia.
Qed.
Lemma upd_range_concat_hom_start_aligned : forall T l start len (v : T) k d,
  start + len <= length (concat l) ->
  Nat.divide k start ->
  Forall (fun l' => length l' = k) l ->
  0 < len <= k -> 0 < k ->
  upd_range (concat l) start len v =
  concat (updN l (start / k) (upd_range (selN l (start / k) d) 0 len v)).
(* hint proof tokens: 45 *)
Proof.
  intros.
  rewrite <- Nat.mod_divide in * by lia.
  erewrite upd_range_concat_hom_small; eauto. repeat (f_equal; auto).
  all : lia.
Qed.
Lemma upd_range_nil : forall T start len (v : T),
  upd_range nil start len v = nil.
(* hint proof tokens: 33 *)
Proof.
  intros T start len.
  generalize start.
  induction len; intros; simpl; auto.
  rewrite IHlen. auto.
Qed.
Lemma upd_range_same : forall T start len n (v : T),
  upd_range (repeat v n) start len v = repeat v n.
(* hint proof tokens: 89 *)
Proof.
  intros.
  generalize dependent start. generalize dependent len.
  induction len; intros. auto.
  simpl. rewrite IHlen.
  destruct (Compare_dec.lt_dec start n).
  erewrite selN_eq_updN_eq. auto.
  rewrite repeat_selN; auto.
  rewrite updN_oob. auto.
  rewrite repeat_length. lia.
  Unshelve. eauto.
Qed.
Hint Rewrite upd_range_0 upd_range_length upd_range_selN upd_range_nil upd_range_same : lists.
Lemma forall_upd_range : forall T l start len (v : T) f,
  Forall f l -> f v -> Forall f (upd_range l start len v).
Proof.
(* original proof tokens: 46 *)
induction len; intros; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma firstn_upd_range : forall T l n n' len (v : T),
  n <= n' -> firstn n (upd_range l n' len v) = firstn n l.
Proof.
(* original proof tokens: 55 *)
intros.
induction len; simpl; auto; intros.
(* No more tactics to try *)
Admitted.

Lemma upd_range_updN_oob : forall T l start len (v v2 : T) i,
  i < start \/ i >= start + len ->
  upd_range (updN l i v2) start len v = updN (upd_range l start len v) i v2.
Proof.
(* original proof tokens: 50 *)
intros.
rewrite upd_range_eq_upd_range'; auto.
destruct H; simpl; auto.
destruct H; simpl; auto.
rewrite upd_range_eq_upd_range' ; auto.
(* No more tactics to try *)
Admitted.

Lemma upd_range_upd_range : forall T l start len1 len2 (v : T),
  upd_range (upd_range l start len1 v) (start + len1) len2 v = upd_range l start (len1 + len2) v.
(* hint proof tokens: 72 *)
Proof.
  intros T l start len1.
  generalize dependent l. generalize dependent start.
  induction len1; intros; simpl.
  rewrite Nat.add_0_r. auto.
  rewrite upd_range_updN_oob by lia.
  rewrite <- Plus.plus_Snm_nSm. rewrite IHlen1. auto.
Qed.
Lemma upd_range_hd : forall T l start len x (v : T),
  upd_range (x :: l) (S start) len v = x :: upd_range l start len v.
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma upd_range_fast_len_0 : forall T vs start (v : T),
  upd_range_fast vs start 0 v = vs.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Theorem upd_range_fast_eq : forall T vs start len (v : T),
    upd_range_fast vs start len v = upd_range vs start len v.
Proof.
(* original proof tokens: 80 *)
induction vs; simpl; intros; auto.
unfold upd_range_fast, upd_range.
destruct start; simpl; try apply IHvs; try lia.
(* No more tactics to try *)
Admitted.

Hint Rewrite upd_range_upd_range upd_range_hd : lists.
Lemma upd_range_app_l : forall T l1 l2 start len (v : T),
  start + len <= length l1 ->
  upd_range (l1 ++ l2) start len v = upd_range l1 start len v ++ l2.
Proof.
(* original proof tokens: 67 *)
intros.
rewrite upd_range_eq_upd_range'; auto.
(* No more tactics to try *)
Admitted.

Lemma upd_range_app_r : forall T l1 l2 start len (v : T),
  length l1 <= start ->
  upd_range (l1 ++ l2) start len v = l1 ++ upd_range l2 (start - length l1) len v.
(* hint proof tokens: 65 *)
Proof.
  intros T l1 l2 start len. generalize dependent start.
  generalize dependent l1. generalize dependent l2.
  induction len; intros; simpl; auto.
  rewrite IHlen by lia.
  rewrite updN_app2 by lia. repeat f_equal. lia.
Qed.
Lemma upd_range_selN_oob : forall T (l : list T) start len v i d,
  i < start \/ i >= start + len ->
  selN (upd_range l start len v) i d = selN l i d.
(* hint proof tokens: 51 *)
Proof.
  intros T l start len.
  generalize dependent start. generalize dependent l.
  induction len; intros; simpl; auto.
  rewrite selN_updN_ne by lia. apply IHlen.
  lia.
Qed.
Lemma removeN_upd_range_l : forall T (l : list T) start len v,
  removeN (upd_range l (S start) len v) start = removeN (upd_range l start (S len) v) start.
Proof.
(* original proof tokens: 23 *)
unfold removeN; simpl.
(* No more tactics to try *)
Admitted.

Lemma removeN_updN_lt : forall T (l : list T) i i' v,
  i < i' ->
  removeN (updN l i v) i' = updN (removeN l i') i v.
Proof.
(* original proof tokens: 93 *)
unfold removeN; simpl.
(* No more tactics to try *)
Admitted.

Lemma removeN_upd_range_r : forall T (l : list T) start len v,
  removeN (upd_range l start len v) (start + len) = removeN (upd_range l start (S len) v) (start + len).
(* hint proof tokens: 79 *)
Proof.
  intros T l start len. generalize dependent start.
  generalize dependent l.
  induction len; intros; simpl.
  - rewrite Nat.add_0_r. rewrite removeN_updN. auto.
  - repeat rewrite removeN_updN_lt by lia. f_equal.
    rewrite <- Plus.plus_Snm_nSm. apply IHlen.
Qed.
Lemma upd_range_eq_app_firstn_repeat : forall T (l : list T) start len v,
  length l <= start + len ->
  upd_range l start len v = firstn start l ++ repeat v (length l - start).
Proof.
(* original proof tokens: 257 *)

(* No more tactics to try *)
Admitted.

Lemma upd_range_oob : forall T (l : list T) start len v,
  length l <= start ->
  upd_range l start len v = l.
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Lemma removeN_upd_range_mid : forall T (l : list T) start len v i i',
  start <= i < start + len ->
  start <= i' < start + len ->
  i <= i' < length l ->
  removeN (upd_range l start len v) i = removeN (upd_range l start len v) i'.
(* hint proof tokens: 491 *)
Proof.
  intros.
  destruct (Compare_dec.le_lt_dec (length l) (start + len)).
  + rewrite upd_range_eq_app_firstn_repeat by auto.
    unfold removeN.
    repeat rewrite firstn_app_le by (rewrite firstn_length_l; lia).
    rewrite firstn_length_l by lia.
    repeat rewrite skipn_app_r_ge by (rewrite firstn_length_l; lia).
    repeat rewrite skipn_repeat.
    repeat rewrite firstn_repeat by lia.
    repeat rewrite <- app_assoc. repeat rewrite repeat_app.
    f_equal. f_equal. rewrite firstn_length_l by lia.
    repeat rewrite <- Nat.sub_add_distr.
    lia.
  + repeat rewrite upd_range_eq_upd_range' by lia.
    unfold upd_range', removeN.
    repeat (
      rewrite firstn_app_le; rewrite firstn_length;
      (let H := fresh in let H' := fresh in
        edestruct Min.min_spec as [ [H H']|[H H'] ];
        rewrite H' in *; clear H'); try lia;
      rewrite firstn_app_l by (rewrite repeat_length; lia)).
    repeat rewrite <- app_assoc. f_equal.
    rewrite skipn_app_r_ge by (rewrite firstn_length_l; lia).
    rewrite skipn_app_r_ge with (n := S _) by (rewrite firstn_length_l; lia).
    repeat rewrite firstn_length_l by lia.
    repeat rewrite firstn_repeat by lia.
    match goal with [|- context [skipn ?a (repeat _ ?b ++ _)] ] =>
      rewrite Minus.le_plus_minus with (m := b) (n := a) at 1 by lia;
      rewrite <- repeat_app, <- app_assoc;
      rewrite skipn_app_l, skipn_oob by (rewrite repeat_length; lia)
    end. symmetry.
    match goal with [|- context [skipn ?a (repeat _ ?b ++ _)] ] =>
      rewrite Minus.le_plus_minus with (m := b) (n := a) at 1 by lia;
      rewrite <- repeat_app, <- app_assoc;
      rewrite skipn_app_l, skipn_oob by (rewrite repeat_length; lia)
    end.
    repeat rewrite app_nil_l. repeat rewrite app_assoc.
    repeat rewrite repeat_app. do 2 f_equal.
    lia.
Qed.
Lemma concat_hom_upd_range : forall T l start len (v : T) k,
  Forall (fun x => length x = k) l ->
  concat (upd_range l start len (repeat v k)) = upd_range (concat l) (start * k) (len * k) v.
(* hint proof tokens: 190 *)
Proof.
  induction l; intros; simpl.
  repeat rewrite upd_range_nil. auto.
  apply Forall_inv in H as H'.
  apply Forall_cons2 in H as H''. subst.
  destruct len. auto.
  simpl. rewrite upd_range_hd.
  destruct start; simpl.
  -rewrite IHl by auto. simpl.
    rewrite <- upd_range_upd_range. simpl.
    rewrite upd_range_app_l by lia.
    rewrite upd_range_app_r.
    rewrite upd_range_eq_app_firstn_repeat with (len := length _) by lia.
    simpl. rewrite repeat_length. rewrite Nat.sub_0_r, Nat.sub_diag. auto.
    rewrite upd_range_length. lia.
  - rewrite upd_range_app_r. f_equal.
    rewrite Minus.minus_plus.
    rewrite <- IHl with (len := S len) by auto.
    auto.
    apply Plus.le_plus_l.
Qed.
Lemma upd_range_start_0 : forall T l len (v : T),
  len <= length l ->
  upd_range l 0 len v = repeat v len ++ skipn len l.
(* hint proof tokens: 67 *)
Proof.
  induction l; intros.
  rewrite upd_range_nil. rewrite skipn_nil. rewrite app_nil_r.
  replace len with 0 by (simpl in *; lia). auto.
  destruct len. auto. simpl in *.
  rewrite upd_range_hd. rewrite IHl by lia. auto.
Qed.
Lemma upd_range_all : forall T l len (v : T),
  length l <= len ->
  upd_range l 0 len v = repeat v (length l).
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma upd_range_app : forall T l1 l2 start len (v : T),
  start <= length l1 < start + len ->
  start + len <= length (l1 ++ l2) ->
  upd_range (l1 ++ l2) start len v =
    upd_range l1 start len v ++ upd_range l2 0 (len - (length l1 - start)) v.
Proof.
(* original proof tokens: 193 *)
unfold upd_range.
induction len; simpl; intros; auto; try lia.
(* No more tactics to try *)
Admitted.

Lemma In_incl : forall A (x : A) (l1 l2 : list A),
  In x l1 -> incl l1 l2 -> In x l2.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 15 *)

intros.
apply H0; auto.
Qed.

Definition postfix A (a b : list A) :=
  exists n, a = skipn n b.
Lemma postfix_nil : forall A (l : list A),
  postfix nil l.
Proof.
(* original proof tokens: 26 *)
exists 0; auto.
(* No more tactics to try *)
Admitted.

Lemma postfix_refl : forall A (a : list A),
  postfix a a.
(* hint proof tokens: 18 *)
Proof.
  unfold postfix; intros.
  exists 0; auto.
Qed.
Lemma postfix_app : forall A (l a b: list A),
  postfix l b ->
  postfix l (a ++ b).
Proof.
(* original proof tokens: 30 *)
intros.
destruct H.
exists (x + length a).
rewrite skipn_app_l; auto.
(* No more tactics to try *)
Admitted.

Lemma postfix_tl : forall A x (l a: list A),
  postfix l a ->
  postfix l (x :: a).
Proof.
(* original proof tokens: 20 *)
intros.
exists (length a); auto.
inversion H; subst.
(* No more tactics to try *)
Admitted.

Lemma postfix_singular : forall A (a : A) l,
  postfix l [ a ] -> l <> nil -> l = [ a ].
(* hint proof tokens: 49 *)
Proof.
  unfold postfix; intros.
  destruct H.
  destruct l; try congruence.
  destruct x; simpl in *; try congruence.
  rewrite skipn_nil in H; congruence.
Qed.
Theorem rev_injective :
  forall A (l1 l2 : list A), rev l1 = rev l2 -> l1 = l2.
Proof.
(* original proof tokens: 31 *)
intros.
induction l1; destruct l2; simpl in *; try congruence; inversion H; subst; auto.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H1; subst.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H.
inversion H1; subst.
inversion H.
inversion H.
inversion H1; subst.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H1; subst.
inversion H1; subst; auto.
inversion H1; subst.
inversion H1; subst.
inversion H1; subst.
inversion H.
inversion H1; subst.
inversion H.
inversion H1; subst.
inversion H.
inversion H.
inversion H1.
inversion H1; subst.
inversion H1; subst.
inversion H.
inversion H1; subst.
inversion H1; subst.
inversion H1; subst.
inversion H1; subst.
inversion H.
inversion H.
inversion H1; subst.
inversion H1; subst.
(* No more tactics to try *)
Admitted.

Lemma rev_eq_iff : forall T (l l' : list T),
  l = rev l' <-> rev l = l'.
Proof.
(* original proof tokens: 35 *)
split; intros.
(* No more tactics to try *)
Admitted.

Lemma NoDup_app_not_In : forall A (l : list A) (a : A),
  NoDup (l ++ [a]) -> ~ In a l.
Proof.
(* original proof tokens: 51 *)
intros A l a H.
(* No more tactics to try *)
Admitted.

Lemma NoDup_rev_1 : forall A (l : list A),
  NoDup l -> NoDup (rev l).
Proof.
(* original proof tokens: 70 *)
induction l; simpl; auto; intros.
apply NoDup_app_comm.
constructor; auto.
(* No more tactics to try *)
Admitted.

Lemma NoDup_rev_2 : forall A (l : list A),
  NoDup (rev l) -> NoDup l.
(* hint proof tokens: 61 *)
Proof.
  induction l; simpl; intros; auto.
  apply NoDup_app_l in H as H1.
  apply NoDup_app_not_In in H as H2.
  constructor; eauto.
  contradict H2.
  apply in_rev in H2; auto.
Qed.
Lemma NoDup_rev : forall A (l : list A),
  NoDup l <-> NoDup (rev l).
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma selN_rev: forall T n (l : list T) d,
  n < length l ->
  selN (rev l) n d = selN l (length l - S n) d.
Proof.
(* original proof tokens: 124 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_rev: forall T (l : list T) n, firstn n (rev l) = rev (skipn (length l - n) l).
Proof.
(* original proof tokens: 126 *)
induction l; simpl; intros; try rewrite firstn_nil; auto; try rewrite skipn_nil; auto.
destruct n; simpl.
(* No more tactics to try *)
Admitted.

Lemma combine_rev: forall A B (a : list A) (b : list B),
  length a = length b ->
  rev (combine a b) = combine (rev a) (rev b).
(* hint proof tokens: 46 *)
Proof.
  induction a; destruct b; cbn; intros; auto.
  congruence.
  rewrite combine_app; cbn.
  f_equal; auto.
  repeat rewrite rev_length; auto.
Qed.
Lemma list_isolate: forall T (l : list T) m n d,
  length l = m + 1 + n ->
  l = firstn m l ++ [selN l m d] ++ rev (firstn n (rev l)).
(* hint proof tokens: 66 *)
Proof.
  intros.
  erewrite <- firstn_skipn at 1.
  f_equal.
  cbn.
  erewrite skipn_selN_skipn.
  f_equal.
  rewrite firstn_rev by auto.
  rewrite rev_involutive.
  f_equal; lia.
  lia.
Qed.
Lemma filter_length : forall A f (l : list A),
  length (filter f l) <= length l.
(* hint proof tokens: 25 *)
Proof.
  induction l; simpl; auto.
  destruct (f a); simpl; auto; lia.
Qed.
Definition disjoint A (a b : list A) :=
  forall x, (In x a -> ~ In x b) /\ (In x b -> ~ In x a).
Lemma disjoint_sym : forall A (a b : list A),
  disjoint a b -> disjoint b a.
Proof.
(* original proof tokens: 13 *)
(* generated proof tokens: 23 *)
intros.
unfold disjoint; intros; split; intros; apply H; auto.
Qed.

Lemma disjoint_nil_l : forall A (a : list A),
  disjoint nil a.
(* hint proof tokens: 13 *)
Proof.
  unfold disjoint; firstorder.
Qed.
Lemma disjoint_cons_l : forall A (a b : list A) x,
  disjoint a b ->
  ~ In x b ->
  disjoint (x :: a) b.
Proof.
(* original proof tokens: 48 *)
intros.
unfold disjoint; intros.
split.
(* No more tactics to try *)
Admitted.

Definition enumerate A (l : list A) := combine (seq 0 (length l)) l.
Theorem selN_enumerate : forall A (l : list A) d i,
  i < length l -> selN (enumerate l) i d = (i, selN l i (snd d)).
(* hint proof tokens: 41 *)
Proof.
  intros.
  unfold enumerate.
  destruct d.
  rewrite selN_combine.
  rewrite nth_selN_eq, seq_nth; auto.
  apply seq_length.
Qed.
Fact length_enumerate : forall T (l : list T), length (enumerate l) = length l.
(* hint proof tokens: 23 *)
Proof.
  unfold enumerate; intros.
  rewrite combine_length_eq; rewrite seq_length; auto.
Qed.
Lemma firstn_seq : forall n a b, firstn n (seq a b) = seq a (min n b).
(* hint proof tokens: 28 *)
Proof.
  induction n; intros; auto; simpl.
  destruct b; auto; simpl; f_equal; auto.
Qed.
Lemma firstn_enumerate : forall A (l : list A) n, firstn n (enumerate l) = enumerate (firstn n l).
(* hint proof tokens: 39 *)
Proof.
  unfold enumerate; intros.
  rewrite firstn_combine_comm; f_equal.
  rewrite firstn_seq; f_equal.
  rewrite firstn_length; auto.
Qed.
Lemma enumerate_inj : forall A (l1 l2 : list A), enumerate l1 = enumerate l2 <-> l1 = l2.
Proof.
(* original proof tokens: 66 *)
split; intros.
(* No more tactics to try *)
Admitted.

Hint Rewrite length_enumerate firstn_enumerate selN_enumerate enumerate_inj : lists.
Definition part {T} (l : list T) (k : nat) :=
  map (fun i => firstn k (skipn (i * k) l)) (seq 0 (length l / k)).
Definition part_nil : forall T k, part (@nil T) k = nil.
(* hint proof tokens: 38 *)
Proof.
  unfold part. intros.
  destruct (Nat.eq_dec 0 k); subst.
  auto.
  rewrite Nat.div_0_l by auto. auto.
Qed.
Lemma part_length : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  length (part l k) = length l / k.
Proof.
(* original proof tokens: 41 *)
(* generated proof tokens: 26 *)

unfold part; simpl; intros; rewrite map_length; simpl.
rewrite seq_length; auto.
Qed.

Lemma part_forall_length : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  Forall (fun x => length x = k) (part l k).
(* hint proof tokens: 102 *)
Proof.
  intros.
  destruct H. unfold part; rewrite H.
  rewrite Nat.div_mul by auto.
  apply Forall_map, Forall_forall.
  intros x0 HH.
  apply in_seq in HH.
  apply firstn_length_l.
  rewrite skipn_length, H.
  rewrite <- Nat.mul_sub_distr_r, Nat.mul_comm.
  rewrite <- Nat.mul_1_r at 1.
  apply Mult.mult_le_compat_l. lia.
Qed.
Lemma concat_hom_part : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  concat (part l k) = l.
Proof.
(* original proof tokens: 213 *)
induction l; intros; simpl.
rewrite part_nil; auto.
(* No more tactics to try *)
Admitted.

Lemma part_hom_concat : forall T (l : list (list T)) k, Forall (fun x => length x = k) l -> k <> 0 ->
  part (concat l) k = l.
(* hint proof tokens: 105 *)
Proof.
  unfold part.
  intros.
  erewrite concat_hom_length; eauto.
  rewrite Nat.div_mul by auto.
  induction l; simpl; intros. auto.
  inversion H; subst.
  f_equal. rewrite firstn_app2; auto.
  rewrite <- seq_shift, map_map.
  simpl in *.
  rewrite <- IHl at 2 by auto.
  apply map_ext.
  intros.
  f_equal.
  rewrite skipn_app_r. auto.
Qed.
Section ifind_list.
Variable T : Type.
Fixpoint ifind_list (cond : T -> nat -> bool) (vs : list T) start : option (nat * T ) :=
    match vs with
    | nil => None
    | x :: rest =>
        if (cond x start) then Some (start, x)
                          else ifind_list cond rest (S start)
    end.
Lemma ifind_list_ok_mono : forall cond vs start r,
    ifind_list cond vs start = Some r ->
    fst r >= start.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma ifind_list_ok_bound : forall cond vs start r,
    ifind_list cond vs start = Some r ->
    fst r < start + length vs.
Proof.
(* original proof tokens: 67 *)
induction vs; simpl; intros; inversion H.
(* No more tactics to try *)
Admitted.

Lemma ifind_list_ok_cond : forall cond vs start r,
    ifind_list cond vs start = Some r ->
    cond (snd r) (fst r) = true.
(* hint proof tokens: 48 *)
Proof.
    induction vs; simpl; intros; try congruence.
    destruct (cond a) eqn: C.
    inversion H; simpl; auto.
    eapply IHvs; eauto.
  Qed.
Lemma ifind_list_ok_item : forall cond vs start r d,
    ifind_list cond vs start = Some r ->
    selN vs ((fst r) - start) d = (snd r).
(* hint proof tokens: 80 *)
Proof.
    induction vs; simpl; intros; try congruence.
    destruct cond.
    inversion H; simpl; auto.
    rewrite Nat.sub_diag; simpl; auto.
    replace (fst r - start) with (S (fst r - S start)).
    apply IHvs; auto.
    apply ifind_list_ok_mono in H; lia.
  Qed.
Lemma ifind_list_ok_facts : forall cond vs start r d,
    ifind_list cond vs start = Some r ->
    (fst r) >= start /\
    (fst r) < start + length vs /\
    cond (snd r) (fst r) = true /\
    selN vs ((fst r) - start) d = (snd r).
(* hint proof tokens: 44 *)
Proof.
    intros; intuition eauto using
      ifind_list_ok_mono,
      ifind_list_ok_bound,
      ifind_list_ok_cond,
      ifind_list_ok_item.
  Qed.
Lemma ifind_list_none : forall cond l start d,
    ifind_list cond l start = None ->
    forall ix, ix < length l ->
    cond (selN l ix d) (start + ix) = false.
(* hint proof tokens: 66 *)
Proof.
    induction l; simpl; intros; try lia.
    destruct ix.
    rewrite Nat.add_0_r.
    destruct cond; congruence.
    rewrite <- Plus.plus_Snm_nSm.
    apply IHl; try lia.
    destruct (cond a); congruence.
  Qed.
End ifind_list.
Inductive list_same {T : Type} (v : T) : list T -> Prop :=
| ListSameNil : list_same v nil
| ListSameCons : forall l, list_same v l -> list_same v (v :: l).
Lemma list_same_app_l : forall T v (a b : list T),
  list_same v (a ++ b) -> list_same v a.
Proof.
(* original proof tokens: 29 *)
(* generated proof tokens: 35 *)
induction a; simpl; intros; auto; inversion H; constructor; auto.
inversion H; subst; eapply IHa; eauto.
Qed.

Lemma list_same_app_r : forall T v (a b : list T),
  list_same v (a ++ b) -> list_same v b.
(* hint proof tokens: 25 *)
Proof.
  induction a; simpl; intros; eauto.
  inversion H; subst; eauto.
Qed.
Lemma list_same_app_both : forall T v (a b : list T),
  list_same v a -> list_same v b -> list_same v (a ++ b).
Proof.
(* original proof tokens: 28 *)
(* generated proof tokens: 26 *)
intros.
induction a; simpl; intros; auto; inversion H; subst; constructor; auto.
Qed.

Lemma list_same_repeat : forall T (v : T) n,
  list_same v (repeat v n).
Proof.
(* original proof tokens: 18 *)
(* generated proof tokens: 18 *)

induction n; simpl; auto; constructor; auto.
Qed.

Lemma list_same_firstn : forall T (v : T) n l,
  list_same v l -> list_same v (firstn n l).
Proof.
(* original proof tokens: 35 *)
induction l; simpl; intros; auto.
(* No more tactics to try *)
Admitted.

Lemma list_same_skipn : forall T (v : T) n l,
  list_same v l -> list_same v (skipn n l).
Proof.
(* original proof tokens: 32 *)
induction l; simpl; intros; auto.
(* No more tactics to try *)
Admitted.

Lemma list_same_firstn_le : forall T (v : T) n2 n1 l,
  n2 <= n1 -> list_same v (firstn n1 l) -> list_same v (firstn n2 l).
Proof.
(* original proof tokens: 64 *)
intros.
apply list_same_firstn.
auto.
(* No more tactics to try *)
Admitted.

Lemma list_same_skipn_ge : forall T (v : T) n1 n2 l,
  n2 >= n1 -> list_same v (skipn n1 l) -> list_same v (skipn n2 l).
Proof.
(* original proof tokens: 59 *)
intros.
induction n2; simpl; intros; auto.
inversion H.
inversion H0; subst; auto.
inversion H0; subst; auto.
destruct l; simpl; auto; eauto using IHn2.
apply ListSameNil.
inversion H2; subst.
inversion H0; subst; auto.
inversion H0; subst; auto.
(* No more tactics to try *)
Admitted.

Lemma list_same_skipn_upd_range_tail : forall T (v : T) l off,
  list_same v (skipn off (upd_range l off (length l - off) v)).
(* hint proof tokens: 157 *)
Proof.
  intros.
  destruct (Compare_dec.le_dec off (length l)).
  - rewrite upd_range_eq_upd_range' by lia; unfold upd_range'.
    rewrite skipn_app_r_ge by ( rewrite firstn_length, min_l; lia ).
    rewrite firstn_length, min_l by lia.
    replace (off - off) with 0 by lia.
    simpl.
    apply list_same_app_both.
    apply list_same_repeat.
    replace (off + (length l - off)) with (length l) by lia.
    rewrite skipn_oob by lia.
    constructor.
  - rewrite Minus.not_le_minus_0 by auto. rewrite upd_range_0.
    rewrite skipn_oob by lia. constructor.
Qed.
Lemma list_same_skipn_upd_range_mid : forall T (v : T) l off count,
  list_same v (skipn (off + count) l) ->
  off + count <= length l ->
  list_same v (skipn off (upd_range l off count v)).
Proof.
(* original proof tokens: 87 *)
intros.
rewrite upd_range_eq_upd_range' by lia; unfold upd_range'; simpl.
(* No more tactics to try *)
Admitted.

Lemma list_same_skipn_selN : forall T (v : T) off l def,
  off < length l -> list_same v (skipn off l) -> v = selN l off def.
Proof.
(* original proof tokens: 54 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma updN_concat' : forall T (l : list (list T)) l' off k x ld,
  k <> 0 ->
  off < k * length l ->
  Forall (fun y => length y = k) l ->
  l' = updN (selN l (off / k) ld) (off mod k) x ->
  updN (concat l) off x = concat (updN l (off / k) l').
Proof.
(* original proof tokens: 79 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma not_in_app: forall (A : Type) (x: A) l1 l2,
  ~In x (l1++l2) -> (~In x l1) /\ (~In x l2).
(* hint proof tokens: 14 *)
Proof.
  split; auto using in_or_app.
Qed.
Hint Resolve incl_app incl_appl incl_appr incl_refl : incl_app.
Lemma incl_app2r : forall T (l1 l2 l2' : list T),
  incl l2 l2' ->
  incl (l1 ++ l2) (l1 ++ l2').
Proof.
(* original proof tokens: 12 *)
intros.
eapply incl_app; eauto.
apply incl_appr.
(* No more tactics to try *)
Admitted.

Lemma incl_app2l : forall T (l1' l1 l2 : list T),
  incl l1 l1' ->
  incl (l1 ++ l2) (l1' ++ l2).
Proof.
(* original proof tokens: 12 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_app_commr: forall (A: Type) (l: list A) l1 l2,
  incl l (l1++l2) -> incl l (l2++l1).
Proof.
(* original proof tokens: 38 *)
intros.
induction l; simpl; intros; auto; try congruence.
(* No more tactics to try *)
Admitted.

Lemma incl_app_comml: forall (A: Type) (l: list A) l1 l2,
  incl (l1++l2) l -> incl (l2++l1) l.
Proof.
(* original proof tokens: 35 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_appl' : forall (A : Type) (l m n : list A),
  incl (l ++ m) n -> incl l n.
(* hint proof tokens: 27 *)
Proof.
  unfold incl; intros.
  eapply H.
  eapply in_or_app.
  eauto.
Qed.
Lemma incl_appr' : forall (A : Type) (l m n : list A),
  incl (l ++ m) n -> incl m n.
(* hint proof tokens: 27 *)
Proof.
  unfold incl; intros.
  eapply H.
  eapply in_or_app.
  eauto.
Qed.
Lemma NoDup_incl_l : forall T (l1 l2 l2' : list T),
  NoDup (l1 ++ l2) ->
  NoDup l2' ->
  incl l2' l2 ->
  NoDup (l1 ++ l2').
(* hint proof tokens: 56 *)
Proof.
  induction l1; intros; eauto.
  simpl.
  inversion H; subst.
  constructor; eauto.
  contradict H4.
  eapply In_incl; eauto.
  eapply incl_app2r; eauto.
Qed.
Lemma NoDup_remove_inverse : forall T a (l' l : list T),
  NoDup (l ++ l') -> ~ In a (l ++ l') -> NoDup (l ++ a :: l').
(* hint proof tokens: 107 *)
Proof.
  induction l; simpl; intros; eauto.
  constructor; eauto.
  inversion H; subst.
  constructor.
  - apply not_in_app in H3; destruct H3.
    intro H'.
    apply in_app_or in H'; destruct H'.
    eauto.
    rewrite cons_app in H3. apply in_app_or in H3. destruct H3.
    simpl in *; intuition eauto.
    eauto.
  - eapply IHl; eauto.
Qed.
Lemma NoDup_incl_r : forall T (l2 l1 l1' : list T),
  NoDup (l1 ++ l2) ->
  NoDup l1' ->
  incl l1' l1 ->
  NoDup (l1' ++ l2).
(* hint proof tokens: 89 *)
Proof.
  induction l2; intros; eauto.
  rewrite app_nil_r; eauto.

  eapply List.NoDup_remove in H; intuition.
  specialize (IHl2 _ _ H2 H0 H1).

  eapply NoDup_remove_inverse; eauto.
  contradict H3.
  eapply In_incl.
  eauto.
  eapply incl_app2l; eauto.
Qed.
Lemma incl_cons2_inv : forall T (l1 l2 : list T) a,
  ~ In a l1 ->
  incl (a :: l1) (a :: l2) ->
  incl l1 l2.
Proof.
(* original proof tokens: 82 *)

(* No more tactics to try *)
Admitted.

Lemma incl_cons_inv : forall T (a : T) l1 l2,
  incl (a :: l1) l2 -> incl l1 l2.
(* hint proof tokens: 17 *)
Proof.
  unfold incl; intros.
  apply H; intuition.
Qed.
Lemma incl_cons_inv' : forall T (a : T) l1 l2,
  incl (a :: l1) l2 -> In a l2 /\ incl l1 l2.
Proof.
(* original proof tokens: 14 *)

(* No more tactics to try *)
Admitted.

Lemma incl_tl_inv : forall T l1 l2 (a : T),
  incl l1 (a :: l2) ->
  ~ In a l1 ->
  incl l1 l2.
(* hint proof tokens: 70 *)
Proof.
  induction l1; simpl; intros.
  - apply incl_nil.
  - intuition.
    apply incl_cons.
    + specialize (H a).
      simpl in *. intuition. exfalso; eauto.
    + eapply IHl1; eauto.
      eapply incl_cons_inv; eauto.
Qed.
Definition incl_count T (E : forall (a b : T), {a=b}+{a<>b}) (l1 l2 : list T) :=
  forall x, count_occ E l1 x <= count_occ E l2 x.
Definition permutation T (E : forall (a b : T), {a=b}+{a<>b}) (l1 l2 : list T) :=
  forall x, count_occ E l1 x = count_occ E l2 x.
Lemma count_occ_app : forall T E (l1 l2 : list T) x,
  count_occ E (l1 ++ l2) x = count_occ E l1 x + count_occ E l2 x.
Proof.
(* original proof tokens: 33 *)
(* generated proof tokens: 18 *)

intros.
rewrite count_occ_app.
reflexivity.
Qed.

Lemma count_occ_remove_ne : forall T E (l : list T) a b,
  a <> b ->
  count_occ E (remove E a l) b = count_occ E l b.
Proof.
(* original proof tokens: 93 *)
(* generated proof tokens: 60 *)
induction l; simpl; intros; try congruence.
destruct (E a0 a); subst; simpl; auto; try congruence.
destruct (E a b); simpl; try congruence; auto.
rewrite IHl by auto; auto.
Qed.

Lemma incl_count_In: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1: list T) n l2,
  incl_count E (n ::l2) l1 ->
  In n l1.
Proof.
(* original proof tokens: 75 *)
unfold incl_count; intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_not_In: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T) x,
    count_occ E l x <= 0 ->
    ~In x l.
Proof.
(* original proof tokens: 111 *)
intros.
eapply count_occ_not_In; eauto.
(* No more tactics to try *)
Admitted.

Lemma count_occ_NoDup: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T),
  NoDup l <->
  forall x, count_occ E l x <= 1.
Proof.
(* original proof tokens: 221 *)
split; intros; induction l; simpl; try solve [ constructor; congruence ]; auto; try lia.
destruct (E a x); try lia.
inversion H.
inversion H; subst; auto; try lia.
inversion H; auto; try lia.
constructor; auto; try lia.
inversion H.
inversion H; subst; auto.
inversion H.
inversion H; subst; eauto.
inversion H; subst; auto; try lia.
(* No more tactics to try *)
Admitted.

Lemma count_occ_NoDup_dec: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T) x,
  NoDup l -> count_occ E l x = 0 \/ count_occ E l x = 1.
(* hint proof tokens: 79 *)
Proof.
  intros.
  destruct (In_dec E x l).
  + right.
    eapply count_occ_NoDup with (E:= E) (x := x) in H.
    assert (count_occ E l x > 0).
    apply count_occ_In; eauto.
    lia.
  + left.
    apply count_occ_not_In; auto.
Qed.
Lemma occ_count_NoDup_impl_NoDup: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l1 l2 : list T),
  incl_count E l1 l2 ->
  NoDup l2 ->
  NoDup l1.
Proof.
(* original proof tokens: 79 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_incl : forall T E (l1 l2 : list T),
  incl_count E l1 l2 ->
  incl l1 l2.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma permutation_incl_count : forall T E (l1 l2 : list T),
  permutation E l1 l2 ->
  incl_count E l1 l2.
(* hint proof tokens: 23 *)
Proof.
  unfold incl_count, permutation; intros.
  specialize (H x).
  lia.
Qed.
Lemma incl_count_tl : forall T E (l1 l2 : list T) x,
  incl_count E l1 l2 ->
  incl_count E l1 (x :: l2).
Proof.
(* original proof tokens: 32 *)
(* generated proof tokens: 46 *)
intros.
unfold incl_count; intros.
apply Nat.le_trans with (m := count_occ E l2 x0); auto; simpl.
destruct (E x x0); auto; lia.
Qed.

Lemma incl_count_cons : forall T E (l1 l2 : list T) x,
  incl_count E l1 l2 ->
  incl_count E (x :: l1) (x :: l2).
Proof.
(* original proof tokens: 32 *)
intros.
unfold incl_count; intros; simpl.
destruct (E x x0); try lia.
(* No more tactics to try *)
Admitted.

Lemma incl_count_cons': forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1 l2: list T) n,
  incl_count E (n::l1) (n::l2) ->
  incl_count E l1 l2.
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Module Type HIDDEN_APP.
Parameter app : forall {T : Type} (l1 l2 : list T), list T.
Axiom app_is : @app = List.app.
End HIDDEN_APP.
Module Hidden_App : HIDDEN_APP.
Definition app := List.app.
Theorem app_is : @app = List.app.
reflexivity.
Qed.
End Hidden_App.
Lemma incl_count_rotate_start : forall T E (l1 l2 : list T),
  incl_count E l1 (Hidden_App.app l2 nil) ->
  incl_count E l1 l2.
(* hint proof tokens: 31 *)
Proof.
  intros.
  rewrite Hidden_App.app_is in *.
  rewrite app_nil_r in *.
  intros; eauto.
Qed.
Lemma incl_count_rotate_one : forall T E (l1 l2 l2' : list T) x,
  incl_count E l1 (Hidden_App.app l2 (l2' ++ [x])) ->
  incl_count E l1 (Hidden_App.app (x :: l2) l2').
(* hint proof tokens: 49 *)
Proof.
  rewrite Hidden_App.app_is.
  unfold incl_count; intros.
  specialize (H x0).
  repeat rewrite count_occ_app in *; simpl in *.
  destruct (E x x0); lia.
Qed.
Lemma incl_count_rotate_cons : forall T E (l1 l2 l2' : list T) x,
  incl_count E l1 (l2 ++ l2') ->
  incl_count E (x :: l1) (Hidden_App.app (x :: l2) l2').
Proof.
(* original proof tokens: 39 *)
(* generated proof tokens: 45 *)

rewrite Hidden_App.app_is; unfold incl_count; intros; specialize (H x0); repeat rewrite count_occ_app in *; simpl in *; destruct (E x x0); lia.
Qed.

Lemma incl_count_nil : forall T E (l : list T),
  incl_count E [] l.
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 17 *)

unfold incl_count; intros.
simpl.
lia.
Qed.

Lemma incl_count_trans : forall T E (l1 l2 l3 : list T),
  incl_count E l1 l2 ->
  incl_count E l2 l3 ->
  incl_count E l1 l3.
(* hint proof tokens: 28 *)
Proof.
  unfold incl_count; intros.
  specialize (H x).
  specialize (H0 x).
  lia.
Qed.
Lemma incl_count_refl : forall T E (l : list T),
  incl_count E l l.
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 15 *)

unfold incl_count; intros.
auto.
Qed.

Lemma count_occ_remove_eq: forall T E (l : list T) x,
  count_occ E (remove E x l) x = 0.
Proof.
(* original proof tokens: 35 *)
(* generated proof tokens: 92 *)
simpl; induction l; intros; auto; destruct (E x a); subst; auto.
simpl; auto.
destruct (E a a); simpl; auto; try congruence.
destruct (E x a); simpl; auto; try congruence.
destruct (E x a); simpl; auto; try congruence.
destruct (E a x); simpl; try congruence; auto.
Qed.

Lemma count_occ_remove_NoDup_eq: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l: list T) n,
  NoDup l ->
  count_occ E (remove E n l) n <= 0.
Proof.
(* original proof tokens: 152 *)

(* No more tactics to try *)
Admitted.

Lemma incl_count_remove_NoDup: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1: list T) n l2,
  NoDup l1 -> 
  NoDup (n :: l2) ->
  incl_count E (n::l2) l1 ->
  incl_count E l2 (remove E n l1).
Proof.
(* original proof tokens: 222 *)
intros.
unfold incl_count.
(* No more tactics to try *)
Admitted.

Lemma incl_count_add: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1 l2: list T) x,
  incl_count E l1 l2 ->
  incl_count E (x::l1) (x::l2).
(* hint proof tokens: 45 *)
Proof.
  unfold incl_count; intros.
  specialize (H x0).
  rewrite cons_app.
  rewrite cons_app with (l := l2).
  repeat rewrite count_occ_app.
  lia.
Qed.
Lemma permutation_trans : forall T E (l1 l2 l3 : list T),
  permutation E l1 l2 ->
  permutation E l2 l3 ->
  permutation E l1 l3.
(* hint proof tokens: 27 *)
Proof.
  unfold permutation; intros.
  specialize (H x).
  specialize (H0 x).
  lia.
Qed.
Lemma permutation_refl : forall T E (l : list T),
  permutation E l l.
(* hint proof tokens: 9 *)
Proof.
  firstorder.
Qed.
Lemma permutation_comm : forall T E (l1 l2 : list T),
  permutation E l1 l2 ->
  permutation E l2 l1.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 26 *)

intros.
unfold permutation in *.
intros.
symmetry in H.
apply H.
Qed.

Lemma permutation_cons: forall T E (l l' : list T) x,
  permutation E l l' ->
  permutation E (x :: l) (x :: l').
(* hint proof tokens: 22 *)
Proof.
  unfold permutation. cbn; intros.
  destruct E; congruence.
Qed.
Lemma incl_count_app_comm : forall T E (l1 l2 : list T),
  incl_count E (l1 ++ l2) (l2 ++ l1).
Proof.
(* original proof tokens: 22 *)
(* generated proof tokens: 23 *)
unfold incl_count; intros.
rewrite count_occ_app; rewrite count_occ_app; lia.
Qed.

Lemma permutation_app_comm : forall T E (l1 l2 : list T),
  permutation E (l1 ++ l2) (l2 ++ l1).
(* hint proof tokens: 21 *)
Proof.
  unfold permutation; intros.
  repeat rewrite count_occ_app.
  lia.
Qed.
Lemma permutation_app_split : forall T E (l1 l1' l2 l2' : list T),
  permutation E l1 l1' ->
  permutation E l2 l2' ->
  permutation E (l1 ++ l2) (l1' ++ l2').
Proof.
(* original proof tokens: 34 *)
(* generated proof tokens: 22 *)
unfold permutation; intros.
rewrite count_occ_app; rewrite count_occ_app; auto.
Qed.

Lemma permutation_remove: forall T E (l l' : list T) x,
  permutation E l l' ->
  permutation E (remove E x l) (remove E x l').
Proof.
(* original proof tokens: 46 *)
unfold permutation; intros.
destruct (E x x0); subst; auto.
rewrite count_occ_remove_ne; auto.
rewrite count_occ_remove_ne; auto.
(* No more tactics to try *)
Admitted.

Lemma permutation_in: forall T E (l l' : list T) x,
  permutation E l l' -> In x l -> In x l'.
(* hint proof tokens: 28 *)
Proof.
  unfold permutation.
  intros.
  rewrite count_occ_In in *.
  rewrite <- H. eauto.
Qed.
Lemma incl_count_app_split : forall T E (l1 l1' l2 l2' : list T),
  incl_count E l1 l1' ->
  incl_count E l2 l2' ->
  incl_count E (l1 ++ l2) (l1' ++ l2').
Proof.
(* original proof tokens: 35 *)
intros. unfold incl_count. intros.
rewrite count_occ_app.
rewrite count_occ_app.
(* No more tactics to try *)
Admitted.

Hint Resolve incl_count_trans incl_count_refl incl_count_app_comm incl_count_app_split : incl_count_app.
Hint Resolve permutation_trans permutation_refl permutation_app_comm permutation_app_split : permutation_app.
Definition NoDupApp (T : Type) (l : list (list T)) := NoDup (concat l).
Lemma NoDupApp_pick : forall T (l1 l2 l3 : list (list T)),
  NoDupApp (l1 ++ l2 ++ l3) -> NoDupApp (l2 ++ l1 ++ l3).
(* hint proof tokens: 44 *)
Proof.
  unfold NoDupApp; intros; repeat rewrite concat_app in *.
  rewrite app_assoc. apply NoDup_app_comm.
  apply NoDup_3app_rev.
  eauto.
Qed.
Lemma NoDupApp_cons_nil : forall T (l : list (list T)),
  NoDupApp ([] :: l) <-> NoDupApp l.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 18 *)
unfold NoDupApp; simpl; intros.
reflexivity.
Qed.

Lemma NoDupApp_cons : forall T a (l : list (list T)),
  NoDupApp l ->
  NoDup a ->
  (forall x, In x a -> ~ In x (concat l)) ->
  NoDupApp (a :: l).
Proof.
(* original proof tokens: 78 *)
unfold NoDupApp; intros.
rewrite concat_cons.
(* No more tactics to try *)
Admitted.

Lemma NoDupApp_In : forall T a (l : list (list T)),
  NoDupApp l ->
  In a l ->
  NoDup a.
(* hint proof tokens: 76 *)
Proof.
  induction l; simpl; intros.
  firstorder.
  intuition subst.
  unfold NoDupApp in H; simpl in H.
  eapply NoDup_app_l; eauto.
  eapply IHl; eauto.
  unfold NoDupApp in H; simpl in H.
  eapply NoDup_app_r; eauto.
Qed.
Lemma incl_pick_inv : forall T (l1 l2 l : list T) x,
  NoDup (x :: l1 ++ l2) ->
  incl (l1 ++ x :: l2) (x :: l) ->
  incl (l1 ++ l2) l.
Proof.
(* original proof tokens: 63 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_pick_inv' : forall T (E : forall a b, {a=b}+{a<>b}) (l1 l2 l : list T) x,
  incl_count E (x :: l) (l1 ++ x :: l2) ->
  incl_count E l (l1 ++ l2).
(* hint proof tokens: 47 *)
Proof.
  intros.
  unfold incl_count in *; intros.
  specialize (H x0).
  rewrite count_occ_app in *.
  simpl in *.
  destruct (E x x0); lia.
Qed.
Lemma incl_concat' : forall T (x : list T) l,
  In x l ->
  incl x (concat l).
Proof.
(* original proof tokens: 66 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_concat : forall T (l1 l2 : list (list T)),
  incl l1 l2 ->
  incl (concat l1) (concat l2).
(* hint proof tokens: 50 *)
Proof.
  induction l1; simpl; intros.
  - apply incl_nil.
  - apply incl_cons_inv' in H; intuition.
    eapply incl_app; eauto.
    eapply incl_concat'; eauto.
Qed.
Theorem NoDupApp_incl : forall T (E : forall (a b : T), {a=b}+{a<>b}) (l2 l1 : list (list T)),
  NoDupApp l1 ->
  incl_count (list_eq_dec E) l2 l1 ->
  NoDupApp l2.
Proof.
(* original proof tokens: 216 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDup_incl_count : forall T E (l1 l2 : list T),
  incl_count E l1 l2 ->
  NoDup l2 ->
  NoDup l1.
Proof.
(* original proof tokens: 53 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDupApp_start : forall T (l : list T) ls,
  l = concat ls ->
  NoDup l = NoDupApp ls.
(* hint proof tokens: 13 *)
Proof.
  intros; subst; reflexivity.
Qed.
Lemma concat_build_app : forall T (a b : list T) la lb,
  a = concat la ->
  b = concat lb ->
  a ++ b = concat (la ++ lb).
(* hint proof tokens: 17 *)
Proof.
  intros; subst.
  rewrite concat_app; auto.
Qed.
Lemma concat_build_cons : forall T a (b : list T) lb,
  b = concat lb ->
  a :: b = concat ([[a]] ++ lb).
(* hint proof tokens: 17 *)
Proof.
  intros; subst.
  rewrite concat_app; auto.
Qed.
Lemma concat_build_nil : forall T,
  @nil T = concat nil.
(* hint proof tokens: 9 *)
Proof.
  reflexivity.
Qed.
Lemma concat_build_one : forall T (x : list T),
  x = concat [x].
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Ltac concat_build :=
  repeat ( eapply concat_build_app || eapply concat_build_cons || eapply concat_build_one ).
Ltac nodupapp_build :=
  repeat match goal with
  | [ |- context[NoDup (?a ++ ?b)] ] =>
    erewrite NoDupApp_start with (l := a ++ b) by concat_build
  | [ |- context[NoDup (?a :: ?b)] ] =>
    erewrite NoDupApp_start with (l := a :: b) by concat_build
  | [ H : context[NoDup (?a ++ ?b)] |- _ ] =>
    erewrite NoDupApp_start with (l := a ++ b) in H by concat_build
  | [ H : context[NoDup (?a :: ?b)] |- _ ] =>
    erewrite NoDupApp_start with (l := a :: b) in H by concat_build
  end.
Ltac solve_incl_count_one :=
  ( eapply incl_count_rotate_cons; simpl ) || ( eapply incl_count_rotate_one; solve_incl_count_one ).
Ltac solve_incl_count :=
  repeat ( eapply incl_count_rotate_start; solve_incl_count_one );
  eapply incl_count_nil.
Hint Resolve NoDupApp_incl : nodupapp.
Hint Extern 1 (incl_count _ _ _) => solve_incl_count : nodupapp.
Ltac nodupapp :=
  nodupapp_build;
  eauto with nodupapp.
Example nodupapp_5 : forall (a : list nat) b c d e,
  NoDup (a ++ b ++ c ++ d :: e) ->
  NoDup (b ++ d :: e ++ a ++ c).
(* hint proof tokens: 27 *)
Proof.
  intros.
  nodupapp.
  Unshelve.
  exact Peano_dec.eq_nat_dec.
Qed.
Example nodupapp_3_5 : forall (a : list nat) b c d e,
  NoDup (a ++ b ++ c ++ d :: e) ->
  NoDup (b ++ d :: c).
(* hint proof tokens: 27 *)
Proof.
  intros.
  nodupapp.
  Unshelve.
  exact Peano_dec.eq_nat_dec.
Qed.
Definition selN_each {T} (l : list (list T)) n (def : T) : list T :=
  map (fun l => selN l n def) l.
Lemma selN_each_S: forall T (l : list (list T)) n def,
  selN_each l (S n) def = selN_each (map (skipn 1) l) n def.
(* hint proof tokens: 41 *)
Proof.
  unfold selN_each.
  induction l; cbn -[skipn]; intros; auto.
  rewrite skipn_selN.
  f_equal.
  eauto.
Qed.
Lemma NoDup_NoDupA_eq: forall T E,
  (forall x y, E x y <-> x = y) ->
  forall (l : list T),
  NoDupA E l <-> NoDup l.
(* hint proof tokens: 137 *)
Proof.
  induction l; cbn; intros.
  split; constructor.
  split; intro H'; inversion H'; subst.
  constructor; auto.
  rewrite IHl in *.
  rewrite InA_alt in *.
  intro Ha.
  match goal with H: context [not] |- _ => eapply H end.
  eexists; split; eauto.
  eapply H; auto.
  eapply IHl; eauto.
  constructor.
  rewrite InA_alt in *.
  intro Ha.
  destruct Ha; intuition.
  rewrite H in *.
  subst; auto.
  eapply IHl; auto.
Qed.
Lemma NoDup_filter: forall T f (l : list T),
  NoDup l -> NoDup (filter f l).
(* hint proof tokens: 43 *)
Proof.
  induction l; cbn; intros.
  constructor.
  inversion H; subst.
  destruct f; auto.
  constructor; eauto.
  rewrite filter_In.
  intuition.
Qed.
Lemma combine_no_dup: forall A B (a : list A) (b : list B),
  NoDup a \/ NoDup b -> NoDup (List.combine a b).
Proof.
(* original proof tokens: 68 *)
intros.
destruct H.
induction a; cbn; intros; auto.
constructor.
destruct b; cbn; try (constructor; auto).
inversion H; subst; auto.
inversion H; auto.
inversion H; subst; auto.
inversion H; subst; auto.
inversion H; subst; auto.
inversion H; subst.
inversion H; subst; auto.
inversion H;eauto.
apply NoDup_app_not_In; auto.
(* Reached max number of model calls *)
Admitted.

Fact NoDup_In_inj: forall T V (f : T -> V) (l : list T),
  NoDup (map f l) ->
  forall a b,
  In a l -> In b l ->
  f a = f b ->
  a = b.
Proof.
(* original proof tokens: 89 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma filter_ext: forall T (f f' : T -> bool) l,
  (forall x, f x = f' x) ->
  filter f l = filter f' l.
Proof.
(* original proof tokens: 40 *)
(* generated proof tokens: 13 *)
intros.
apply filter_ext; auto.
Qed.

Definition index_of {T} (f : T -> bool) (l : list T) :=
  match (ifind_list (fun x _ => f x) l 0) with
  | Some (i, x) => i
  | None => length l
  end.
Fixpoint sort_by_index {S T} (f : T -> T -> bool) (ls : list (S * T)) (lt : list T) s0 t0 :=
  match lt with
  | nil => nil
  | t :: lt =>
    let i := index_of (fun a => f t (snd a)) ls in
    (selN ls i (s0, t0)) :: (sort_by_index f ls lt s0 t0)
  end.
Definition inb {T} {E} (l : list T) (x : T) :=
  if in_dec E x l then true else false.
Lemma index_of_spec: forall T (l : list T) f d,
  let i := index_of f l in
  i < length l -> f (selN l i d) = true.
(* hint proof tokens: 70 *)
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'; eauto.
  rewrite Nat.sub_0_r in *.
  intuition.
  match goal with H: _ |- _ => rewrite H end.
  auto.
  lia.
Qed.
Lemma index_of_inb: forall T (l : list T) f,
  (exists x, In x l /\ f x = true) ->
  index_of f l < length l.
Proof.
(* original proof tokens: 119 *)

(* No more tactics to try *)
Admitted.

Lemma inb_spec: forall T E l x,
  In x l <-> @inb T E l x = true.
(* hint proof tokens: 23 *)
Proof.
  unfold inb.
  intros.
  destruct in_dec; intuition congruence.
Qed.
Lemma sort_by_index_length: forall S T t f (l : list (S * T)) s0 t0,
  length (sort_by_index f l t s0 t0) = length t.
(* hint proof tokens: 14 *)
Proof.
  induction t; cbn; auto.
Qed.
Lemma sort_by_index_spec: forall S T (ls : list (S * T)) f lt s0 t0,
  (forall x, In x lt -> In x (snd (split ls))) ->
  (forall a b, f a b = true <-> a = b) ->
  snd (split (sort_by_index f ls lt s0 t0)) = lt.
(* hint proof tokens: 301 *)
Proof.
  induction lt; cbn.
  auto.
  intros.
  destruct selN eqn: Hp.
  remember (split (sort_by_index _ _ _ _ _)) as r.
  rewrite (surjective_pairing r); cbn.
  subst r.
  rewrite IHlt; auto.
  f_equal.
  unfold index_of in *.
  destruct ifind_list eqn:Ha.
  eapply ifind_list_ok_facts in Ha.
  rewrite Nat.sub_0_r in *.
  intuition subst.
  eapply f_equal with (f := snd) in Hp.
  match goal with H: selN _ _ _ = _ |- _ => rewrite H in * end.
  rewrite Hp in *.
  rewrite H0 in *. subst.
  auto.
  specialize (H a) as ?.
  intuition.
  match goal with H: _ |- _ => eapply in_selN_exists in H;
    destruct H as [i ?]; intuition end.
  rewrite split_length_r in *.
  eapply ifind_list_none with (ix := i) in Ha; eauto.
  rewrite <- selN_split_r in *.
  match goal with
    Hf : context [iff],
    Hb : _ = a |- _ => symmetry in Hb; eapply Hf in Hb end.
  rewrite Ha in *.
  congruence.
Unshelve.
  all: eauto.
Qed.
Lemma index_of_in_sort_by_index: forall T V (fn : T -> V) f (l : list T) d x,
  In x l ->
  NoDup (map fn l) ->
  (forall x y, f x y = true <-> x = y) ->
  selN l (index_of (fun a => f (fn x) (fn a)) l) d = x.
(* hint proof tokens: 210 *)
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'.
  rewrite Nat.sub_0_r in *.
  intuition auto.
  repeat match goal with H: _ |- _ => rewrite H in * end.
  eapply NoDup_In_inj; eauto.
  match goal with H: _ |- _ => rewrite <- H end.
  eapply in_selN; eauto.
  eapply in_selN_exists in H.
  destruct H as [i [? Hs] ].
  eapply ifind_list_none in H'; eauto.
  eapply f_equal with (f := fn) in Hs.
  match goal with H: forall x y, _, H' : f ?a ?b = false |- _ =>
    specialize (H a b) end.
  rewrite Hs in *.
  intuition.
  congruence.
Unshelve.
  all: eauto.
Qed.
Lemma NoDup_selN_index_of_multiple: forall T V f (fn : T -> V) (l : list T) a d,
  NoDup l ->
  In a l ->
  (forall x y, f x y = true <-> x = y) ->
  fn (selN l (index_of (fun x => f (fn a) (fn x)) l) d) <> fn a -> False.
Proof.
(* original proof tokens: 166 *)

(* No more tactics to try *)
Admitted.

Lemma in_sort_by_index': forall S T f t (l : list (S * T)) x s0 t0,
  NoDup (map snd l) ->
  In x l ->
  In (snd x) t ->
  (forall x y, f x y = true <-> x = y) ->
  In x (sort_by_index f l t s0 t0).
Proof.
(* original proof tokens: 47 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma in_sort_by_index: forall S T f t (l : list (S * T)) (x : S * T) s0 t0,
  NoDup t -> NoDup l ->
  (forall x, In x t -> exists y, In (y, x) l) ->
  (forall x y, f x y = true <-> x = y) ->
  In x (sort_by_index f l t s0 t0) -> In x l /\ In (snd x) t.
(* hint proof tokens: 216 *)
Proof.
  induction t; cbn in *.
  intuition auto.
  intros.
  match goal with H: context [iff] |- _ => rename H into Hf end.
  inversion H; subst.
  edestruct (H1 a).
  left; eauto.
  intuition subst.
  eapply in_selN.
  eapply index_of_inb.
  eexists.
  split; try eassumption.
  rewrite Hf; auto.
  match goal with |- ?a = ?b \/ _ => destruct (f a b) eqn:? end.
  left.
  rewrite <- Hf; eauto.
  exfalso; eapply NoDup_selN_index_of_multiple with (fn := snd) (l := l); eauto.
  intro Hs.
  symmetry in Hs.
  rewrite <- Hf in Hs.
  rewrite Hs in *.
  congruence.
  eapply IHt; eauto.
  right.
  eapply IHt; eauto.
Qed.
Lemma filter_elements_permutation: forall T (l : list (T * _)) a t0,
  NoDup (map snd l) ->
  NoDup a ->
  (forall x, In x a -> exists y, In (y, x) l) ->
  let e := (sort_by_index Nat.eqb l a t0 0) in
  let p := filter (fun x => inb (E:=Nat.eq_dec) a (snd x)) l in
  Permutation e p.
Proof.
(* original proof tokens: 236 *)

(* No more tactics to try *)
Admitted.

Lemma partition_permutation_app: forall T f (l : list T),
  let p := partition f l in
  Permutation l (fst p ++ snd p).
(* hint proof tokens: 52 *)
Proof.
  cbn; induction l; cbn.
  constructor.
  destruct partition eqn:?.
  destruct f; cbn in *.
  constructor.
  auto.
  eapply Permutation_cons_app.
  eauto.
Qed.
Lemma sort_by_index_combine: forall A B f (la : list A) (lb : list B) t a0 b0,
  length la = length lb ->
  incl t lb ->
  (forall x y, f x y = true <-> x = y) ->
  let s := sort_by_index f (List.combine la lb) t a0 b0 in
  s = List.combine (fst (split s)) t.
(* hint proof tokens: 100 *)
Proof.
  intros.
  pose proof (split_combine s).
  destruct (split s) eqn:Hs; cbn.
  pose proof H2 l l0 (eq_refl _).
  rewrite <- H3.
  f_equal.
  eapply f_equal with (f := snd) in Hs; cbn in Hs.
  subst.
  eapply sort_by_index_spec; auto.
  intros.
  rewrite List.combine_split; auto.
Qed.
Lemma partition_eq_filter: forall T (l : list T) f,
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
(* original proof tokens: 46 *)
cbn; induction l; cbn; auto; intros; destruct (f a); cbn; auto; f_equal.
destruct (f a); cbn; auto; f_equal.
destruct (f a); cbn; auto; f_equal.
destruct (f a); cbn; auto; f_equal.
destruct (f a); cbn; auto; f_equal.
destruct (f a); cbn; auto; f_equal.
destruct (f a); cbn; auto; f_equal.
destruct (f a); cbn; auto; f_equal.
destruct (f a); cbn; auto; f_equal.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); simpl; f_equal; auto.
destruct (f a); cbn; f_equal; auto; try apply IHl.
destruct (partition f l) eqn:H; cbn; f_equal; auto.
destruct (f a); simpl; f_equal; auto; try apply IHl.
destruct (f a); simpl; f_equal; auto; try apply IHl.
destruct (f a); cbn; auto; f_equal; auto; try apply IHl.
destruct (f a); cbn; auto; try (f_equal; apply IHl).
(* Reached max number of model calls *)
Admitted.

Lemma filter_map_ext: forall T T' f f' (g : T -> T') l,
  (forall x, In x l -> f x = f' (g x)) ->
  filter f' (map g l) = map g (filter f l).
(* hint proof tokens: 39 *)
Proof.
  induction l; cbn; intros.
  auto.
  rewrite H by auto.
  destruct f'; cbn.
  f_equal; auto.
  auto.
Qed.
Lemma filter_r: forall A B (f : B -> bool) (a : list A) b da db,
  length a = length b ->
  filter (fun x => f (snd x)) (List.combine a b) = List.combine (map (fun i => selN a i da) (filter (fun i => f (selN b i db)) (seq 0 (length a)))) (filter f b).
Proof.
(* original proof tokens: 65 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma filter_l: forall A B (f : A -> bool) a b da (db : B),
  length a = length b ->
  filter (fun x => f (fst x)) (List.combine a b) = List.combine (filter f a) (map (fun i => selN b i db) (filter (fun i => f (selN a i da)) (seq 0 (length a)))).
(* hint proof tokens: 65 *)
Proof.
  induction a; cbn; intros.
  auto.
  destruct b; cbn in *; try congruence.
  rewrite <- seq_shift.
  erewrite filter_map_ext.
  destruct f; cbn; rewrite map_map.
  f_equal.
  all: eauto.
Qed.
Lemma filter_selN_length: forall T f (l : list T) d,
  length (filter f l) = length (filter (fun i => f (selN l i d)) (seq 0 (length l))).
Proof.
(* original proof tokens: 52 *)
intros.
induction l; cbn; auto; intros.
destruct f; cbn; try lia.
rewrite IHl.
(* No more tactics to try *)
Admitted.

Lemma permutation_filter: forall T E (l l' : list T),
  NoDup l -> NoDup l' ->
  incl l' l ->
  Permutation.Permutation (filter (@inb _ E l') l) l'.
(* hint proof tokens: 49 *)
Proof.
  intros.
  apply Permutation.NoDup_Permutation; auto using NoDup_filter.
  intros.
  rewrite filter_In.
  unfold inb.
  destruct in_dec; intuition.
  congruence.
Qed.
