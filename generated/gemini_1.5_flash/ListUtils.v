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
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 14 *)
intros.
rewrite H.
reflexivity.
Qed.

Lemma snd_pair : forall T1 T2 (a : T1) (b : T2) c, 
  c = (a, b) -> snd c = b.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma repeat_selN : forall T i n (v def : T),
  i < n -> selN (repeat v n) i def = v.
Proof.
(* original proof tokens: 27 *)
intros.
induction n.
inversion H.
destruct i.
reflexivity.
simpl.
(* No more tactics to try *)
Admitted.

Lemma repeat_selN' : forall T i n (v : T),
  selN (repeat v n) i v = v.
Proof.
(* original proof tokens: 18 *)
intros.
apply repeat_selN.
(* No more tactics to try *)
Admitted.

Lemma selNopt_selN : forall T i l (v def : T),
  selNopt l i = Some v -> selN l i def = v.
Proof.
(* original proof tokens: 20 *)

(* No more tactics to try *)
Admitted.

Lemma selN_selNopt : forall T i l (v def : T),
  i < length l -> selNopt l i = Some (selN l i def).
Proof.
(* original proof tokens: 30 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selNopt_length : forall T i l (v : T),
  selNopt l i = Some v -> i < length l.
Proof.
(* original proof tokens: 33 *)
induction l; intros; simpl.
destruct i; simpl in *; auto.
inversion H.
destruct i; simpl in *; auto; try lia.
inversion H.
(* No more tactics to try *)
Admitted.

Lemma repeat_app : forall T i j (x : T),
  repeat x i ++ repeat x j = repeat x (i + j).
Proof.
(* original proof tokens: 22 *)
induction i; intros.
(* No more tactics to try *)
Admitted.

Lemma repeat_map : forall A B (f:A -> B) x n,
  map f (repeat x n) = repeat (f x) n.
Proof.
(* original proof tokens: 27 *)
induction n; auto.
(* No more tactics to try *)
Admitted.

Lemma concat_hom_repeat : forall A l k (item : A),
  Forall (fun x => x = repeat item k) l ->
  concat l = repeat item (length l * k).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma length_nil : forall A (l : list A),
  length l = 0 -> l = nil.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma length_nil' : forall A (l : list A),
  length l = 0 -> nil = l.
Proof.
(* original proof tokens: 19 *)
(* generated proof tokens: 14 *)
symmetry.
apply length_nil.
exact H.
Qed.

Lemma eqlen_nil : forall A B (a : list A),
  eqlen a (@nil B) -> a = nil.
Proof.
(* original proof tokens: 21 *)
(* generated proof tokens: 22 *)
intros A B a H.
inversion H.
apply length_nil.
assumption.
Qed.

Lemma cons_app : forall A (a : A) l,
  a :: l = [a] ++ l.
Proof.
(* original proof tokens: 10 *)
(* generated proof tokens: 10 *)

reflexivity.
Qed.

Lemma nth_selN_eq : forall t n l (z:t), selN l n z = nth n l z.
Proof.
(* original proof tokens: 18 *)

(* No more tactics to try *)
Admitted.

Lemma length_updN : forall T vs n (v : T), length (updN vs n v) = length vs.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite length_updN : lists.
Lemma selN_updN_eq : forall V vs n v (default : V),
  n < length vs
  -> selN (updN vs n v) n default = v.
Proof.
(* original proof tokens: 18 *)

(* No more tactics to try *)
Admitted.

Lemma selN_selN_def_eq : forall V vs n (def1 def2 : V),
  n < length vs
  -> selN vs n def1 = selN vs n def2.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma selN_updN_eq_default : forall V vs n (v : V),
  selN (updN vs n v) n v = v.
Proof.
(* original proof tokens: 18 *)

(* No more tactics to try *)
Admitted.

Lemma selN_updN_ne : forall V vs n n' v (default : V),
  n <> n'
  -> selN (updN vs n v) n' default = selN vs n' default.
Proof.
(* original proof tokens: 19 *)
intros.
destruct vs; simpl; try lia.
case n'; try lia.
case n'; try lia.
reflexivity.
destruct n'; try lia.
reflexivity.
(* No more tactics to try *)
Admitted.

Lemma selN_eq_updN_eq : forall A (l : list A) i a def,
  a = selN l i def
  -> updN l i a = l.
Proof.
(* original proof tokens: 32 *)
intros.
rewrite H.
(* No more tactics to try *)
Admitted.

Lemma repeat_eq_updN : forall T i n (v x : T) l,
  i < n ->
  repeat v n = updN l i x -> x = v.
Proof.
(* original proof tokens: 65 *)
intros.
(* No more tactics to try *)
Admitted.

Hint Rewrite selN_updN_eq using (simpl; lia) : lists.
Lemma in_skipn_S : forall A l n (a : A) def,
  selN l n def <> a
  -> In a (skipn n l)
  -> In a (skipn (S n) l).
Proof.
(* original proof tokens: 17 *)
destruct l; simpl; try congruence.
intros.
(* No more tactics to try *)
Admitted.

Lemma in_firstn_in : forall A l n (a : A),
  In a (firstn n l) -> In a l.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Lemma in_skipn_in : forall A l n (a : A),
  In a (skipn n l) -> In a l.
Proof.
(* original proof tokens: 17 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma in_cons_head : forall A l (a:A),
  In a (a :: l).
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 13 *)
intros.
auto.
apply in_eq.
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
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Theorem updN_firstn_comm : forall T (v : T) vs i j,
  firstn i (updN vs j v) = updN (firstn i vs) j v.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite firstn_updN using lia : lists.
Lemma skipn_skipn': forall A n m (l: list A),
  skipn n (skipn m l) = skipn (m + n) l.
Proof.
(* original proof tokens: 35 *)
induction l; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma skipn_skipn: forall A n m (l: list A),
  skipn n (skipn m l) = skipn (n + m) l.
Proof.
(* original proof tokens: 21 *)
induction l; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma skipn_selN : forall T i j vs (def: T),
  selN (skipn i vs) j def = selN vs (i + j) def.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite skipn_selN using lia : lists.
Lemma skipn_seq : forall n a b, skipn n (seq a b) = seq (a + n) (b - n).
Proof.
(* original proof tokens: 47 *)
intros.
destruct n.
simpl.
(* No more tactics to try *)
Admitted.

Hint Rewrite skipn_seq : lists.
Lemma skipN_updN' : forall T (v : T) vs i j,
  i > j
  -> skipn i (updN vs j v) = skipn i vs.
Proof.
(* original proof tokens: 20 *)

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
Proof.
(* original proof tokens: 22 *)
intros.
destruct vs; simpl; try lia.
destruct i; try lia.
simpl.
f_equal.
auto.
case j.
inversion H.
reflexivity.
(* No more tactics to try *)
Admitted.

Lemma skipn_selN_skipn : forall off A (l : list A) def,
  off < length l ->
  skipn off l = selN l off def :: skipn (S off) l.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma skipn_sub_S_selN_cons : forall A (l : list A) n def,
  n < length l ->
  skipn (length l - S n) l = selN l (length l - n - 1) def :: (skipn (length l - n) l).
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite skipn_updN using lia : lists.
Lemma updN_twice : forall T (l : list T) a v v',
  updN (updN l a v') a v = updN l a v.
Proof.
(* original proof tokens: 31 *)
unfold updN.
(* No more tactics to try *)
Admitted.

Hint Rewrite updN_twice : lists.
Lemma updN_comm : forall T (l : list T) a0 v0 a1 v1,
  a0 <> a1 ->
  updN (updN l a0 v0) a1 v1 = updN (updN l a1 v1) a0 v0.
Proof.
(* original proof tokens: 42 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma updN_firstn_skipn : forall T (l:list T) n v,
  n < length l ->
  updN l n v = firstn n l ++ v::nil ++ skipn (n+1) l.
Proof.
(* original proof tokens: 53 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem list_selN_ext' : forall len T (a b : list T) default,
  length a = len
  -> length b = len
  -> (forall pos, pos < len -> selN a pos default = selN b pos default)
  -> a = b.
Proof.
(* original proof tokens: 69 *)
intros.
induction len.
inversion H.
(* No more tactics to try *)
Admitted.

Theorem list_selN_ext : forall T (a b : list T) default,
  length a = length b
  -> (forall pos, pos < length a -> selN a pos default = selN b pos default)
  -> a = b.
Proof.
(* original proof tokens: 28 *)
intros T a b default H.
induction a; intros.
inversion H.
rewrite H in H0; simpl in H0.
inversion H.
simpl in H.
destruct b.
reflexivity.
inversion H.
inversion H.
destruct b.
simpl in H.
(* No more tactics to try *)
Admitted.

Ltac nth_selN H := intros; repeat rewrite nth_selN_eq; apply H; assumption.
Lemma in_selN : forall t n l (z:t), n < length l -> In (selN l n z) l.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma in_selN_exists : forall A l (a : A) def,
  In a l -> exists i, i < length l /\ selN l i def = a.
Proof.
(* original proof tokens: 63 *)
intros.
eexists.
split; eauto.
(* No more tactics to try *)
Admitted.

Lemma selN_split_r: forall A B (l : list (A * B)) i d,
  selN (snd (split l)) i (snd d) = snd (selN l i d).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma selN_split_l: forall A B (l : list (A * B)) i d,
  selN (fst (split l)) i (fst d) = fst (selN l i d).
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma map_fst_split: forall A B (l : list (A * B)), map fst l = fst (split l).
Proof.
(* original proof tokens: 38 *)
induction l; simpl; auto.
rewrite IHl.
(* No more tactics to try *)
Admitted.

Lemma map_snd_split: forall A B (l : list (A * B)), map snd l = snd (split l).
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma in_updN : forall t n l x (xn:t), In x (updN l n xn) ->
  In x l \/ x = xn.
Proof.
(* original proof tokens: 37 *)
intros.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 76 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma Forall_append: forall A f (l1 l2:list A),
  Forall f l1 -> Forall f l2 -> Forall f (l1 ++ l2).
Proof.
(* original proof tokens: 47 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall_app_r : forall A P (a b : list A),
  Forall P (a ++ b) -> Forall P a.
Proof.
(* original proof tokens: 27 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall_app_l : forall A P (a b : list A),
  Forall P (a ++ b) -> Forall P b.
Proof.
(* original proof tokens: 27 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma Forall_repeat: forall A (f:A -> Prop) a n,
  f a -> Forall f (repeat a n).
Proof.
(* original proof tokens: 31 *)
(* generated proof tokens: 14 *)

induction n; simpl; auto.
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
Proof.
(* original proof tokens: 30 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma Forall_combine_same : forall T T1 T2 (l : list T) P (f1 : T -> T1) (f2 : T -> T2),
  Forall (fun x => P (f1 x, f2 x)) l ->
  Forall P (combine (map f1 l) (map f2 l)).
Proof.
(* original proof tokens: 29 *)
induction l; auto.
intros.
apply Forall_forall.
intros.
(* No more tactics to try *)
Admitted.

Lemma concat_repeat: forall T n k (x : T),
  concat (repeat (repeat x k) n) = repeat x (n * k).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Ltac small_t' := intros; autorewrite with core; autorewrite with core in *;
           eauto; simpl in *; intuition; eauto.
Ltac small_t := repeat small_t'; subst; simpl; eauto.
Lemma forall_skipn: forall A n (l : list A) p,
  Forall p l -> Forall p (skipn n l).
Proof.
(* original proof tokens: 37 *)
induction l; simpl; auto.
intros.
(* No more tactics to try *)
Admitted.

Lemma forall_firstn: forall A n (l : list A) p,
  Forall p l -> Forall p (firstn n l).
Proof.
(* original proof tokens: 35 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma updN_selN_eq : forall T (l : list T) ix default,
  updN l ix (selN l ix default) = l.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma updN_app1 : forall t l l' (v:t) n,
  n < length l -> updN (l ++ l') n v = updN l n v ++ l'.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma updN_app2 : forall t l l' (v:t) n,
  n >= length l -> updN (l ++ l') n v = l ++ updN l' (n - length l) v.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 105 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_app1 : forall t l l' (d:t) n,
  n < length l -> selN (l ++ l') n d = selN l n d.
Proof.
(* original proof tokens: 14 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_app2 : forall t l l' (d:t) n,
  n >= length l -> selN (l ++ l') n d = selN l' (n - length l) d.
Proof.
(* original proof tokens: 14 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_cons : forall A (a : A) l i def,
  i > 0 -> selN (a :: l) i def = selN l (i - 1) def.
Proof.
(* original proof tokens: 39 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem seq_right : forall b a, seq a (S b) = seq a b ++ (a + b :: nil).
Proof.
(* original proof tokens: 62 *)
induction b; simpl.
(* No more tactics to try *)
Admitted.

Theorem seq_right_0 : forall b, seq 0 (S b) = seq 0 b ++ (b :: nil).
Proof.
(* original proof tokens: 15 *)
induction b; simpl.
(* No more tactics to try *)
Admitted.

Lemma selN_map_some_range : forall A (l : list A) idx a,
  selN (map (@Some _) l) idx None = Some a ->
  idx < length l.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma map_updN : forall T U (v : T) (f : T -> U) vs i,
  map f (updN vs i v) = updN (map f vs) i (f v).
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite map_updN : lists.
Theorem selN_map_seq' : forall T i n f base (default : T), i < n
  -> selN (map f (seq base n)) i default = f (i + base).
Proof.
(* original proof tokens: 48 *)
intros.
rewrite nth_selN_eq.
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
Proof.
(* original proof tokens: 38 *)
intros.
rewrite H.
(* No more tactics to try *)
Admitted.

Theorem selN_map : forall T T' l i f (default : T) (default' : T'), i < length l
  -> selN (map f l) i default = f (selN l i default').
Proof.
(* original proof tokens: 29 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma in_selN_map : forall A B (l : list (A*B)) i def1 def2,
  i < length l
  -> In (selN (map fst l) i def1, selN (map snd l) i def2) l.
Proof.
(* original proof tokens: 39 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem updN_map_seq_app_eq : forall T (f : nat -> T) len start (v : T) x,
  updN (map f (seq start len) ++ (x :: nil)) len v =
  map f (seq start len) ++ (v :: nil).
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 143 *)
unfold selN; unfold updN; simpl.
induction len; simpl.
destruct pos; simpl.
(* No more tactics to try *)
Admitted.

Lemma combine_l_nil : forall T R (a : list T), List.combine a (@nil R) = nil.
Proof.
(* original proof tokens: 11 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite combine_l_nil : lists.
Theorem firstn_combine_comm : forall n T R (a : list T) (b : list R),
  firstn n (List.combine a b) = List.combine (firstn n a) (firstn n b).
Proof.
(* original proof tokens: 38 *)
(* generated proof tokens: 37 *)
induction n; simpl.
simpl; auto.
intros.
simpl.
destruct a; simpl; destruct b; simpl; auto; try congruence.
Qed.

Theorem skipn_combine_comm : forall n T R (a : list T) (b : list R),
  match (List.combine a b) with
  | nil => nil
  | _ :: c => skipn n c
  end = List.combine (skipn (S n) a) (skipn (S n) b).
Proof.
(* original proof tokens: 140 *)
induction a; induction b; auto; simpl; try rewrite IHb; try rewrite IHa; try lia.
rewrite combine_l_nil.
auto.
(* No more tactics to try *)
Admitted.

Lemma skipn_combine_comm' : forall n T R (a : list T) (b : list R),
  skipn (S n) (List.combine a b) = List.combine (skipn (S n) a) (skipn (S n) b).
Proof.
(* original proof tokens: 15 *)
induction a; simpl; auto; try congruence.
intros b.
(* No more tactics to try *)
Admitted.

Lemma skipn_combine : forall A B n (a : list A) (b : list B),
  length a = length b ->
  skipn n (combine a b) = combine (skipn n a) (skipn n b).
Proof.
(* original proof tokens: 26 *)
induction a; induction b; intros; simpl; try congruence.
(* No more tactics to try *)
Admitted.

Lemma selN_last: forall A l n def (a : A),
  n = length l -> selN (l ++ a :: nil) n def = a.
Proof.
(* original proof tokens: 25 *)
intros.
rewrite H.
(* No more tactics to try *)
Admitted.

Lemma selN_firstn: forall {A} (l:list A) i n d,
  i < n -> selN (firstn n l) i d = selN l i d.
Proof.
(* original proof tokens: 28 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_oob: forall A n l (def : A),
  length l <= n
  -> selN l n def = def.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Lemma selN_inb : forall A (l : list A) n d1 d2,
  n < length l ->
  selN l n d1 = selN l n d2.
Proof.
(* original proof tokens: 28 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_app: forall A n l l' (def : A),
  n < length l
  -> selN (l ++ l') n def = selN l n def.
Proof.
(* original proof tokens: 26 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_app2: forall A n (l1 l2 : list A),
  n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof.
(* original proof tokens: 36 *)
intros.
rewrite H.
(* No more tactics to try *)
Admitted.

Lemma skipn_oob: forall T n (l : list T),
  n >= length l -> skipn n l = nil.
Proof.
(* original proof tokens: 38 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma updN_oob: forall T l i (v : T),
  i >= length l -> updN l i v = l.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_oob: forall A (l : list A) n,
  n >= length l -> firstn n l = l.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_exact: forall A (l : list A),
  firstn (length l) l = l.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_firstn : forall A (l : list A) n1 n2 ,
  firstn n1 (firstn n2 l) = firstn (Init.Nat.min n1 n2) l.
Proof.
(* original proof tokens: 27 *)
(* generated proof tokens: 12 *)

apply firstn_firstn.
Qed.

Lemma firstn_all : forall A (l : list A), firstn (length l) l = l.
Proof.
(* original proof tokens: 26 *)
(* generated proof tokens: 11 *)

apply firstn_all.
Qed.

Lemma firstn_plusone_selN : forall A n (l : list A) def,
  n < length l
  -> firstn (n + 1) l = firstn n l ++ (selN l n def :: nil).
Proof.
(* original proof tokens: 38 *)
intros.
(* No more tactics to try *)
Admitted.

Definition firstn_plusone_selN' : forall A n l (x: A) def,
  x = selN l n def ->
  n < length l ->
  firstn (n + 1) l = firstn n l ++ x::nil.
Proof.
(* original proof tokens: 23 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_S_selN : forall A n l (def : A),
  n < length l ->
  firstn (S n) l = firstn n l ++ [ (selN l n def) ].
Proof.
(* original proof tokens: 35 *)
(* generated proof tokens: 29 *)
intros.
rewrite <- firstn_plusone_selN; auto.
rewrite Nat.add_1_r.
reflexivity.
Qed.

Lemma firstn_S_selN_expand : forall A n l (def : A),
  n < length l ->
  match l with
  | nil => nil
  | a :: l => a :: firstn n l
  end = firstn n l ++ [ (selN l n def) ].
Proof.
(* original proof tokens: 24 *)
intros.
case l; auto.
inversion H.
destruct l; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma firstn_updN_oob: forall A (l : list A) n i def,
  n <= i -> firstn n (updN l i def) = firstn n l.
Proof.
(* original proof tokens: 34 *)
(* generated proof tokens: 20 *)
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
intros.
(* No more tactics to try *)
Admitted.

Lemma removelast_firstn_sub : forall A n (l : list A),
  n > 0 -> n <= length l
  -> removelast (firstn n l) = firstn (n - 1) l.
Proof.
(* original proof tokens: 57 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_nil : forall A n,
  firstn n nil = @nil A.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_cons : forall A n (a : A) l,
  firstn (S n) (a :: l) = a :: firstn n l.
Proof.
(* original proof tokens: 22 *)
(* generated proof tokens: 10 *)

reflexivity.
Qed.

Lemma firstn_length_l : forall A (l : list A) n,
  n <= length l -> length (firstn n l) = n.
Proof.
(* original proof tokens: 22 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_length_l_iff : forall A (l : list A) n,
  n <= length l <-> length (firstn n l) = n.
Proof.
(* original proof tokens: 46 *)
split.
intros.
apply firstn_length_l.
assumption.
(* No more tactics to try *)
Admitted.

Lemma firstn_length_r : forall A (l : list A) n,
  n >= length l -> length (firstn n l) = length l.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma skipn_length: forall A n (l : list A),
  length (skipn n l) = length l - n.
Proof.
(* original proof tokens: 17 *)
induction l; simpl.
case n; simpl; lia.
destruct n; simpl; try lia.
(* No more tactics to try *)
Admitted.

Lemma skipn_nil : forall A n,
  skipn n nil = @nil A.
Proof.
(* original proof tokens: 12 *)
(* generated proof tokens: 11 *)

apply skipn_nil.
Qed.

Lemma removeN_nil : forall A n,
  removeN nil n = (@nil A).
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

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
(* generated proof tokens: 20 *)
induction a; simpl; auto.
rewrite IHa.
reflexivity.
Qed.

Lemma firstn_app_l: forall A (a b: list A) n,
  n <= length a ->
  firstn n (a ++ b) = firstn n a.
Proof.
(* original proof tokens: 40 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_app : forall T (a b : list T),
  skipn (length a) (a ++ b) = b.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma skipn_app_eq : forall T (a b : list T) n,
  length a = n -> skipn n (a ++ b) = b.
Proof.
(* original proof tokens: 19 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_app_r : forall T i (b a : list T),
  skipn (length a + i) (a ++ b) = skipn i b.
Proof.
(* original proof tokens: 104 *)

(* No more tactics to try *)
Admitted.

Lemma skipn_app_l : forall T i (a b : list T),
  i <= length a ->
  skipn i (a ++ b) = (skipn i a) ++ b.
Proof.
(* original proof tokens: 41 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_app_split: forall T (a b : list T) n,
  skipn n (a ++ b) = skipn n a ++ skipn (n - length a) b.
Proof.
(* original proof tokens: 88 *)
destruct a; simpl.
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_app_r : forall T (b a : list T) i,
  removeN (a ++ b) (length a + i) = a ++ (removeN b i).
Proof.
(* original proof tokens: 54 *)
intros.
unfold removeN.
rewrite firstn_app_r.
(* No more tactics to try *)
Admitted.

Lemma firstn_repeat : forall T m n (v : T),
  n <= m -> firstn n (repeat v m) = repeat v n.
Proof.
(* original proof tokens: 63 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_repeat' : forall A (v : A) m n,
  n <= m -> skipn n (repeat v m) = repeat v (m - n).
Proof.
(* original proof tokens: 40 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_repeat : forall A (v : A) m n,
  skipn n (repeat v m) = repeat v (m - n).
Proof.
(* original proof tokens: 56 *)
destruct m; simpl.
induction n; simpl.
reflexivity.
reflexivity.
intros n.
(* No more tactics to try *)
Admitted.

Lemma app_repeat : forall T m n (v : T),
  repeat v m ++ repeat v n = repeat v (m + n).
Proof.
(* original proof tokens: 52 *)
induction m; simpl.
(* No more tactics to try *)
Admitted.

Lemma repeat_app_tail : forall T n (a : T),
  repeat a (S n) = repeat a n ++ (a :: nil).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma removeN_repeat : forall T n i (e : T),
   n > 0 -> i < n
   -> removeN (repeat e n) i = repeat e (n - 1).
Proof.
(* original proof tokens: 40 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_nonnil : forall T (l : list T) n, 0 < n -> l <> nil ->
  exists e l', firstn n l = e :: l'.
Proof.
(* original proof tokens: 31 *)
destruct n.
destruct l.
(* No more tactics to try *)
Admitted.

Lemma skipn_nonnil : forall T (l : list T) n, n < length l ->
  exists e l', skipn n l = e :: l'.
Proof.
(* original proof tokens: 49 *)
intros.
destruct l as [|x xs].
inversion H.
elim n.
exists x, xs.
destruct n.
reflexivity.
inversion H.
reflexivity.
simpl.
inversion H.
reflexivity.
inversion H.
reflexivity.
(* No more tactics to try *)
Admitted.

Lemma firstn_sum_split : forall A n off (l: list A),
  firstn (n+off) l = firstn n l ++ firstn off (skipn n l).
Proof.
(* original proof tokens: 55 *)
induction l; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma skipn_sum_split : forall A n k (l: list A),
  skipn n l = firstn k (skipn n l) ++ skipn (n+k) l.
Proof.
(* original proof tokens: 68 *)

(* No more tactics to try *)
Admitted.

Lemma skipn_sum_split' : forall A n off1 off2 (l: list A),
  off1 <= off2 ->
  skipn (n+off1) l =
    firstn (off2 - off1) (skipn (n+off1) l) ++ skipn (n+off2) l.
Proof.
(* original proof tokens: 40 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_sum_app : forall A (l1 l2: list A) n1 n2,
  n1 = length l1 ->
  firstn (n1 + n2) (l1 ++ l2) = l1 ++ firstn n2 l2.
Proof.
(* original proof tokens: 39 *)
intros.
rewrite H.
(* No more tactics to try *)
Admitted.

Lemma skipn_sum_app : forall A (l1 l2: list A) n1 n2,
  n1 = length l1 ->
  skipn (n1 + n2) (l1 ++ l2) = skipn n2 l2.
Proof.
(* original proof tokens: 30 *)
intros.
rewrite H.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 84 *)

(* No more tactics to try *)
Admitted.

Lemma concat_hom_firstn : forall A (lists: list (list A)) n k,
  Forall (fun sublist => length sublist = k) lists ->
  firstn (n * k) (concat lists) = concat (firstn n lists).
Proof.
(* original proof tokens: 157 *)

(* No more tactics to try *)
Admitted.

Lemma concat_hom_skipn : forall A (lists: list (list A)) n k,
  Forall (fun sublist => length sublist = k) lists ->
  skipn (n * k) (concat lists) = concat (skipn n lists).
Proof.
(* original proof tokens: 149 *)
induction lists; simpl.
intros.
(* No more tactics to try *)
Admitted.

Lemma concat_hom_updN_first_skip : forall A n k (lists: list (list A)) (l: list A),
  Forall (fun sublist => length sublist = k) lists ->
  n < length lists ->
  firstn (n * k) (concat lists) ++ l ++
  skipn (n * k + k) (concat lists) = concat (updN lists n l).
Proof.
(* original proof tokens: 113 *)

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
Proof.
(* original proof tokens: 64 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_selN_firstn_hom : forall T (l : list (list T)) k nvalid off d1 d2 d3,
  Forall (fun sublist : list T => length sublist = k) (firstn nvalid l) ->
  off < nvalid * k ->
  off < k * length l -> selN (selN l (off / k) d1) (off mod k) d2 = selN (concat l) off d3.
Proof.
(* original proof tokens: 234 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_hom_concat: forall T k (l : list (list T)) n,
  Forall (fun x => length x = k) l ->
  k <> 0 ->
  skipn n (concat l) = skipn (n mod k) (selN l (n / k) nil) ++ concat (skipn (S (n / k)) l).
Proof.
(* original proof tokens: 167 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_hom_concat: forall T k (l : list (list T)) n,
  Forall (fun x => length x = k) l ->
  k <> 0 ->
  firstn n (concat l) = concat (firstn (n / k) l) ++ firstn (n mod k) (selN l (n / k) nil).
Proof.
(* original proof tokens: 158 *)

(* No more tactics to try *)
Admitted.

Lemma selN_selN_hom : forall T (l : list (list T)) k off def,
  Forall (fun sublist => length sublist = k) l ->
  off < k * length l ->
  selN (selN l (off / k) nil) (Nat.modulo off k) def = selN (concat l) off def.
Proof.
(* original proof tokens: 39 *)
intros.
(* No more tactics to try *)
Admitted.

Definition combine_updN : forall A B i a b (va:A) (vb:B),
  List.combine (updN a i va) (updN b i vb) = updN (List.combine a b) i (va, vb).
Proof.
(* original proof tokens: 27 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma combine_updN_l: forall A B (a : list A) (b : list B) i x d,
  combine (updN a i x) b = updN (combine a b) i (x, selN b i d).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma combine_updN_r: forall A B (a : list A) (b : list B) i x d,
  combine a (updN b i x) = updN (combine a b) i (selN a i d, x).
Proof.
(* original proof tokens: 36 *)
unfold combine.
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
Proof.
(* original proof tokens: 19 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma combine_length_eq2: forall A B (a : list A) (b : list B),
  length a = length b
  -> length (List.combine a b) = length b.
Proof.
(* original proof tokens: 19 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem combine_app: forall A B (al ar : list A) (bl br: list B),
  length al = length bl
  -> List.combine (al ++ ar) (bl ++ br) 
     = (List.combine al bl) ++ (List.combine ar br).
Proof.
(* original proof tokens: 32 *)
induction al; intros.
simpl.
inversion H.
(* No more tactics to try *)
Admitted.

Theorem removeN_updN : forall V l i (v : V),
   removeN (updN l i v) i = removeN l i.
Proof.
(* original proof tokens: 34 *)
unfold removeN.
(* No more tactics to try *)
Admitted.

Theorem removeN_oob: forall A (l : list A) i,
  i >= length l -> removeN l i = l.
Proof.
(* original proof tokens: 36 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_head: forall A l i (a : A),
  removeN (a :: l) (S i) = a :: (removeN l i).
Proof.
(* original proof tokens: 13 *)
(* generated proof tokens: 10 *)

reflexivity.
Qed.

Theorem removeN_combine: forall A B i (a : list A) (b : list B),
  removeN (List.combine a b) i = List.combine (removeN a i) (removeN b i).
Proof.
(* original proof tokens: 69 *)
induction a; simpl; auto; try congruence.
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_length: forall A (l : list A) i,
  i < length l -> length (removeN l i) = length l - 1.
Proof.
(* original proof tokens: 56 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_length_eq: forall A B (a : list A) (b : list B) i,
  i < length a -> i < length b
  -> length (removeN a i) = length (removeN b i)
  -> length a = length b.
Proof.
(* original proof tokens: 48 *)
(* generated proof tokens: 29 *)
intros.
rewrite removeN_length in H1 by lia.
rewrite removeN_length in H1 by lia.
lia.
Qed.

Lemma removeN_tail: forall A (l : list A) a,
  removeN (l ++ a :: nil) (length l) = l.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma selN_removelast : forall A n l (def : A),
  n < length l - 1
  -> selN (removelast l) n def = selN l n def.
Proof.
(* original proof tokens: 63 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma length_removelast : forall A (l : list A),
  l <> nil -> length (removelast l) = length l - 1.
Proof.
(* original proof tokens: 53 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_removelast : forall A (l : list A),
  length l > 0
  -> removeN l (length l - 1) = removelast l.
Proof.
(* original proof tokens: 74 *)
intros.
destruct l.
inversion H.
simpl.
(* No more tactics to try *)
Admitted.

Lemma in_removeN : forall T (l : list T) i x,
  In x (removeN l i) -> In x l.
Proof.
(* original proof tokens: 65 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma in_removeN_neq: forall T (l : list T) x d i,
  In x l ->
  selN l i d <> x ->
  In x (removeN l i).
Proof.
(* original proof tokens: 56 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma in_combine_ex_l: forall A B (a : list A) (b : list B),
  length a >= length b ->
  forall y, In y b -> exists x, In (x, y) (List.combine a b).
Proof.
(* original proof tokens: 55 *)
intros.
eexists.
(* No more tactics to try *)
Admitted.

Lemma in_combine_ex_r: forall A B (a : list A) (b : list B),
  length a <= length b ->
  forall x, In x a -> exists y, In (x, y) (List.combine a b).
Proof.
(* original proof tokens: 49 *)
intros.
induction a; auto.
destruct H0.
destruct H0;eauto.
(* No more tactics to try *)
Admitted.

Theorem firstn_removelast_eq : forall V (l : list V),
  length l > 0
  -> firstn (length l - 1) l = removelast l.
Proof.
(* original proof tokens: 73 *)
induction l; simpl.
intros.
inversion H.
(* No more tactics to try *)
Admitted.

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
(* generated proof tokens: 15 *)
intros.
apply firstn_repeat.
assumption.
Qed.

Lemma firstn_app_split : forall T (l1 l2 : list T) n,
  firstn n (l1 ++ l2) = firstn n l1 ++ firstn (n - length l1) l2.
Proof.
(* original proof tokens: 74 *)
induction l1; simpl.
intros.
(* No more tactics to try *)
Admitted.

Lemma selN_skip_first : forall T (l:list T) n m p def,
  n + m < p ->
    selN l (n + m) def = selN (skipn n (firstn p l)) m def.
Proof.
(* original proof tokens: 29 *)
intros.
rewrite skipn_selN by lia.
(* No more tactics to try *)
Admitted.

Definition setlen A l n (def : A) :=
  firstn n l ++ (repeat def (n - length l)).
Lemma repeat_is_nil : forall T (v : T) n,
  n = 0 -> repeat v n = nil.
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 16 *)

intros.
rewrite H.
reflexivity.
Qed.

Lemma setlen_length : forall A l n (def : A),
  length (setlen l n def) = n.
Proof.
(* original proof tokens: 71 *)
unfold setlen.
(* No more tactics to try *)
Admitted.

Lemma setlen_nil : forall A n (def : A),
  setlen nil n def = repeat def n.
Proof.
(* original proof tokens: 36 *)

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
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_map_comm : forall A B n (l : list A) (f : A -> B),
  skipn n (map f l) = map f (skipn n l).
Proof.
(* original proof tokens: 21 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_map_comm : forall A B n (l : list A) (f : A -> B),
  firstn n (map f l) = map f (firstn n l).
Proof.
(* original proof tokens: 28 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_map_comm: forall T T' (f : T -> T') i l,
  removeN (map f l) i = map f (removeN l i).
Proof.
(* original proof tokens: 31 *)
induction l; auto; simpl.
(* No more tactics to try *)
Admitted.

Lemma skipn_firstn_comm : forall A n m (l : list A),
  skipn n (firstn (n + m) l) = firstn m (skipn n l).
Proof.
(* original proof tokens: 26 *)
(* generated proof tokens: 16 *)
intros.
rewrite firstn_skipn_comm; auto.
Qed.

Lemma setlen_app_r : forall A n (a b : list A) e0,
  n >= length a ->
  setlen (a ++ b) n e0 = a ++ setlen b (n - length a) e0.
Proof.
(* original proof tokens: 43 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma setlen_repeat : forall A m n (a : A),
  setlen (repeat a n) m a = repeat a m.
Proof.
(* original proof tokens: 96 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma skipn_app_r_ge : forall A n (a b : list A),
  n >= length a ->
  skipn n (a ++ b) = skipn (n - length a) b.
Proof.
(* original proof tokens: 78 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_map_exact : forall A B (l : list A) (f : A -> B),
  firstn (length l) (map f l) = map f l.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma combine_map_fst_snd: forall A B (l: list (A * B)),
  List.combine (map fst l) (map snd l) = l.
Proof.
(* original proof tokens: 27 *)
induction l; simpl; auto; f_equal; auto.
(* No more tactics to try *)
Admitted.

Lemma combine_map: forall T A' B' (l : list T) (f : _ -> A') (g : _ -> B'),
  map (fun x => (f x, g x)) l = combine (map f l) (map g l).
Proof.
(* original proof tokens: 24 *)
induction l; auto.
(* No more tactics to try *)
Admitted.

Lemma combine_map': forall T T' A' B' (a : list T) (b : list T') (f : _ -> A') (g : _ -> B'),
  map (fun x => (f (fst x), g (snd x))) (combine a b) = combine (map f a) (map g b).
Proof.
(* original proof tokens: 33 *)
induction a; simpl; auto; intros.
(* No more tactics to try *)
Admitted.

Lemma combine_map_l : forall A B C (a : list A) (b : list B) (f : _ -> C),
  combine (map f a) b = map (fun ab => (f (fst ab), snd ab)) (combine a b).
Proof.
(* original proof tokens: 30 *)
unfold combine; simpl.
induction a; simpl; auto.
destruct b; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma combine_map_r : forall A B C (a : list A) (b : list B) (f : _ -> C),
  combine a (map f b) = map (fun ab => (fst ab, f (snd ab))) (combine a b).
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Lemma map_fst_combine: forall A B (a: list A) (b: list B),
  length a = length b -> map fst (List.combine a b) = a.
Proof.
(* original proof tokens: 43 *)
(* generated proof tokens: 42 *)
induction a; intros; simpl.
inversion H.
reflexivity.
destruct b; simpl; try rewrite IHa; auto; try congruence.
inversion H.
Qed.

Lemma map_snd_combine: forall A B (a: list A) (b: list B),
  length a = length b -> map snd (List.combine a b) = b.
Proof.
(* original proof tokens: 36 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma map_snd_updN : forall A B (l : list (A*B)) a v,
  map snd (updN l a v) = updN (map snd l) a (snd v).
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

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

(* No more tactics to try *)
Admitted.

Lemma NoDup_skipn : forall A (l : list A) n,
  NoDup l -> NoDup (skipn n l).
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma NoDup_app_l : forall A (a b : list A),
  NoDup (a ++ b) -> NoDup a.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma NoDup_app_r : forall A (a b : list A),
  NoDup (a ++ b) -> NoDup b.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma NoDup_remove_mid : forall A (a b c : list A),
  NoDup (a ++ b ++ c) -> NoDup (a ++ c).
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Hint Resolve in_app_or.
Hint Resolve in_or_app.
Lemma not_In_NoDup_app : forall T (a : T) l1 l2,
  In a l1 -> NoDup (l1 ++ l2) -> ~ In a l2.
Proof.
(* original proof tokens: 42 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma in_nodup_split : forall T (a : T) l1 l2,
  In a (l1 ++ l2) -> NoDup (l1 ++ l2) -> ~ In a l2 -> In a l1.
Proof.
(* original proof tokens: 32 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDup_app_comm : forall T (l1 l2 : list T),
  NoDup (l1 ++ l2) ->
  NoDup (l2 ++ l1).
Proof.
(* original proof tokens: 77 *)

(* No more tactics to try *)
Admitted.

Lemma NoDup_3app_rev : forall T (l1 l2 l3 : list T),
  NoDup (l3 ++ l2 ++ l1) ->
  NoDup (l1 ++ l2 ++ l3).
Proof.
(* original proof tokens: 130 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 27 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma in_map_fst_exists_snd : forall A B (l : list (A * B)) a,
  In a (map fst l) -> exists b, In (a, b) l.
Proof.
(* original proof tokens: 27 *)
induction l; intros.
destruct H.
inversion H; subst.
exists (snd a).
apply in_cons.
destruct H.
(* No more tactics to try *)
Admitted.

Lemma setlen_In : forall A n l (a def : A),
  In a (setlen l n def)
  -> a = def \/ In a l.
Proof.
(* original proof tokens: 90 *)
intros.
destruct (setlen l n def) eqn:E.
inversion E.
right.
(* No more tactics to try *)
Admitted.

Lemma updN_skipn : forall A l i n (v : A),
  updN (skipn n l) i v = skipn n (updN l (i + n) v).
Proof.
(* original proof tokens: 237 *)

(* No more tactics to try *)
Admitted.

Lemma setlen_skipn_updN_absorb : forall A (l : list A) m n i v def,
  i < n \/ i >= m + n ->
  setlen (skipn n (updN l i v)) m def = setlen (skipn n l) m def.
Proof.
(* original proof tokens: 64 *)
intros.
destruct H.
(* No more tactics to try *)
Admitted.

Lemma setlen_inbound : forall A n (l : list A) def,
  n <= length l ->
  setlen l n def = firstn n l.
Proof.
(* original proof tokens: 36 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma setlen_oob : forall A n (l : list A) def,
  n >= length l ->
  setlen l n def = l ++ repeat def (n - length l).
Proof.
(* original proof tokens: 23 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma setlen_exact : forall A n (l : list A) def,
  n = length l ->
  setlen l n def = l.
Proof.
(* original proof tokens: 41 *)
intros.
rewrite H.
(* No more tactics to try *)
Admitted.

Lemma selN_map_eq: forall T T' (f : T -> T') (l l' : list T) d,
  (forall i, f (selN l i d) = f (selN l' i d)) ->
  length l = length l' ->
  map f l = map f l'.
Proof.
(* original proof tokens: 72 *)
intros.
apply f_equal.
(* No more tactics to try *)
Admitted.

Lemma combine_repeat : forall A B n (a : A) (b : B),
  combine (repeat a n) (repeat b n) = repeat (a, b) n.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma Forall_selN : forall A (l : list A) P i def,
  Forall P l -> i < length l -> P (selN l i def).
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma selN_Forall : forall A (l : list A) (P : A -> Prop) def,
  (forall i, i < length l -> P (selN l i def)) ->
  Forall P l.
Proof.
(* original proof tokens: 51 *)

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
induction l; simpl; intros.
destruct H.
right; auto.
apply IHl; auto.
(* No more tactics to try *)
Admitted.

Theorem remove_still_In_ne : forall T dec (a b : T) l,
  In a (remove dec b l) -> b <> a.
Proof.
(* original proof tokens: 45 *)
intros.
destruct (dec a b).
(* No more tactics to try *)
Admitted.

Theorem remove_other_In : forall T dec (a b : T) l,
  b <> a -> In a l -> In a (remove dec b l).
Proof.
(* original proof tokens: 65 *)
intros.
(* No more tactics to try *)
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
intros.
(* No more tactics to try *)
Admitted.

Lemma remove_cons_neq: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l: list T) a b,
  a <> b ->
  remove E a (b :: l) = b :: remove E a l.
Proof.
(* original proof tokens: 51 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma remove_comm: forall T E x x' (l : list T),
  remove E x' (remove E x l) = remove E x (remove E x' l).
Proof.
(* original proof tokens: 30 *)
induction l; simpl; auto.
destruct (E x a); simpl; try congruence.
rewrite IHl.
destruct (E x' a); simpl; auto.
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
Proof.
(* original proof tokens: 18 *)

(* No more tactics to try *)
Admitted.

Lemma selN_cons_fold : forall A (a : A) l i def,
  match i with | O => a | S n' => selN l n' def end = selN (a :: l) i def.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma removeN_0_skipn : forall A n (l : list A),
  removeN (skipn n l) 0 = skipn (S n) l.
Proof.
(* original proof tokens: 17 *)
induction l; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma skipn_firstn_length_eq : forall A B (a : list A) (b : list B) n,
  length (firstn n a) = length (firstn n b) ->
  length (skipn n a) = length (skipn n b) ->
  length a = length b.
Proof.
(* original proof tokens: 128 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma Forall_map : forall A B (l : list A) P (f : A -> B),
  Forall (fun x => P (f x)) l <->
  Forall P (map f l).
Proof.
(* original proof tokens: 47 *)
(* generated proof tokens: 23 *)
split; intros; subst; try (apply Forall_map).
apply H.
auto.
Qed.

Lemma Forall_map_l : forall A B C P (l : list A) (b : B) (f : A -> C),
  Forall (fun a => P (f a) b) l <->
  Forall (fun a => P a b) (map f l).
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma Forall_map_r : forall A B C P (l : list A) (b : B) (f : A -> C),
  Forall (fun a => P b (f a)) l <->
  Forall (fun a => P b a) (map f l).
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Lemma Forall_remove : forall A (l : list A) a P EQ,
  Forall P l ->
  Forall P (remove EQ a l).
Proof.
(* original proof tokens: 33 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall2_length : forall A B (a : list A) (b : list B) P,
  Forall2 P a b -> length a = length b.
Proof.
(* original proof tokens: 14 *)

(* No more tactics to try *)
Admitted.

Lemma forall2_forall : forall A B (a : list A) (b : list B) P,
  Forall2 P a b -> Forall (fun x => P (fst x) (snd x)) (combine a b).
Proof.
(* original proof tokens: 14 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall_forall2 : forall A B (a : list A) (b : list B) P,
  Forall (fun x => P (fst x) (snd x)) (combine a b) ->
  length a = length b ->
  Forall2 P a b.
Proof.
(* original proof tokens: 40 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall2_forall_l' : forall A B (la : list A) (lb : list B) P,
  Forall2 P la lb -> Forall (fun a => exists b, P a b) la.
Proof.
(* original proof tokens: 31 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall2_forall_l : forall A B (la : list A) (lb : list B) P,
  Forall2 (fun a b => P a) la lb -> Forall P la.
Proof.
(* original proof tokens: 31 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall2_forall_r' : forall A B (la : list A) (lb : list B) P,
  Forall2 P la lb -> Forall (fun b => exists a, P a b) lb.
Proof.
(* original proof tokens: 31 *)
induction 1; auto.
(* No more tactics to try *)
Admitted.

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
intros.
(* No more tactics to try *)
Admitted.

Lemma forall_forall2_r : forall A B (la : list A) (lb : list B) P,
  length la = length lb -> Forall P lb -> Forall2 (fun a b => P b) la lb.
Proof.
(* original proof tokens: 39 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall2_impl : forall A B (la : list A) (lb : list B) (P Q : A -> B -> Prop),
  Forall2 P la lb ->
  Forall2 (fun a b => P a b -> Q a b) la lb ->
  Forall2 Q la lb.
Proof.
(* original proof tokens: 55 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma forall2_lift : forall A B (la : list A) (lb : list B) (P : A -> B -> Prop),
  (forall a b, P a b) ->
  length la = length lb ->
  Forall2 P la lb.
Proof.
(* original proof tokens: 34 *)
induction la; intros; auto.
inversion H0; subst; eauto.
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
Proof.
(* original proof tokens: 59 *)

(* No more tactics to try *)
Admitted.

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
(* No more tactics to try *)
Admitted.

Lemma forall2_map2_selN: forall  A (l1 : list A) B l2 T1 T2 (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) (f1 : A -> T1) (f2 : B -> T2) def1 def2,
    (forall a b n, n < Datatypes.length l1 -> selN l1 n def1 = a -> selN l2 n def2 = b -> q a b -> p (f1 a) (f2 b)) ->
    Forall2 q l1 l2 ->
    Forall2 p (map f1 l1) (map f2 l2).
Proof.
(* original proof tokens: 140 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma Forall2_eq : forall T (l l' : list T),
  Forall2 eq l l' -> l = l'.
Proof.
(* original proof tokens: 35 *)
(* generated proof tokens: 15 *)
induction 1; auto.
congruence.
Qed.

Lemma Forall2_to_map_eq : forall T U l l' (R : T -> T -> Prop) (f : T -> U),
  (forall a b, R a b -> f a = f b) ->
  Forall2 R l l' ->
  map f l = map f l'.
Proof.
(* original proof tokens: 27 *)
induction l' as [|x' l' IH]; auto.
intros.
apply f_equal.
inversion H0; auto.
intros.
apply f_equal.
inversion H0; subst; auto.
(* No more tactics to try *)
Admitted.

Definition cuttail A n (l : list A) := firstn (length l - n) l.
Lemma cuttail_length : forall A (l : list A) n,
  length (cuttail n l) = length l - n.
Proof.
(* original proof tokens: 26 *)
(* generated proof tokens: 20 *)
unfold cuttail.
intros.
apply firstn_length_l.
lia.
Qed.

Lemma cuttail_0 : forall A (l : list A),
  cuttail 0 l = l.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma cuttail_oob : forall A (l : list A) n,
  n >= length l -> cuttail n l = nil.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma last_selN : forall A (l : list A) def,
  last l def = selN l (length l - 1) def.
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Lemma last_cuttail_selN : forall A n (l : list A) def,
  n < length l ->
  last (cuttail n l) def = selN l (length l - n - 1) def.
Proof.
(* original proof tokens: 47 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma cuttail_cuttail : forall A (l : list A) m n,
  cuttail m (cuttail n l) = cuttail (n + m) l.
Proof.
(* original proof tokens: 59 *)
unfold cuttail.
intros.
rewrite <- cuttail_length.
(* No more tactics to try *)
Admitted.

Lemma cuttail_tail : forall A (l : list A) a n,
  cuttail (S n) (l ++ [a]) = cuttail n l.
Proof.
(* original proof tokens: 52 *)

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
intros.
(* No more tactics to try *)
Admitted.

Lemma cuttail_app_one: forall T (l : list T) n i d,
  n < length l ->
  i = length l - S n ->
  cuttail (S n) l ++ [selN l i d] = cuttail n l.
Proof.
(* original proof tokens: 56 *)

(* No more tactics to try *)
Admitted.

Lemma cuttail_concat_hom: forall T (l : list (list T)) n k,
  (Forall (fun x => length x = k) l) ->
  cuttail (n * k) (concat l) = concat (cuttail n l).
Proof.
(* original proof tokens: 48 *)
intros.
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
Proof.
(* original proof tokens: 9 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_in_nil : forall T (l : list T),
  incl l nil -> l = nil.
Proof.
(* original proof tokens: 33 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_remove : forall T dec (a : T) (l : list T),
  incl (remove dec a l) l.
Proof.
(* original proof tokens: 40 *)
intros.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 49 *)
induction len; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma upd_range_selN : forall T l start len (v : T) n d,
  start <= n < start + len ->
  n < length l ->
  selN (upd_range l start len v) n d = v.
Proof.
(* original proof tokens: 86 *)
induction len; simpl.
intros.
inversion H.
destruct n.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
(* No more tactics to try *)
Admitted.

Definition upd_range' T l start len (v : T) :=
  firstn start l ++ repeat v len ++ skipn (start + len) l.
Lemma upd_range_eq_upd_range' : forall T (l : list T) start len v,
  start + len <= length l ->
  upd_range l start len v = upd_range' l start len v.
Proof.
(* original proof tokens: 151 *)
induction len; auto.
intros.
(* No more tactics to try *)
Admitted.

Theorem upd_range_fast_eq_upd_range' : forall T (l: list T) start len v,
    start + len <= length l ->
    upd_range_fast l start len v = upd_range' l start len v.
Proof.
(* original proof tokens: 100 *)
induction l; intros; simpl.
case start; simpl.
(* No more tactics to try *)
Admitted.

Lemma upd_range_concat_hom_small : forall T l start len (v : T) k d,
  start + len <= length (concat l) ->
  Forall (fun l' => length l' = k) l ->
  start mod k + len <= k ->
  0 < k -> 0 < len ->
  upd_range (concat l) start len v =
  concat (updN l (start / k) (upd_range (selN l (start / k) d) (start mod k) len v)).
Proof.
(* original proof tokens: 446 *)
intros.
rewrite upd_range_eq_upd_range'.
(* No more tactics to try *)
Admitted.

Lemma upd_range_concat_hom_start_aligned : forall T l start len (v : T) k d,
  start + len <= length (concat l) ->
  Nat.divide k start ->
  Forall (fun l' => length l' = k) l ->
  0 < len <= k -> 0 < k ->
  upd_range (concat l) start len v =
  concat (updN l (start / k) (upd_range (selN l (start / k) d) 0 len v)).
Proof.
(* original proof tokens: 45 *)
intros.
rewrite upd_range_eq_upd_range' by lia.
rewrite upd_range_eq_upd_range'.
(* No more tactics to try *)
Admitted.

Lemma upd_range_nil : forall T start len (v : T),
  upd_range nil start len v = nil.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma upd_range_same : forall T start len n (v : T),
  upd_range (repeat v n) start len v = repeat v n.
Proof.
(* original proof tokens: 89 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite upd_range_0 upd_range_length upd_range_selN upd_range_nil upd_range_same : lists.
Lemma forall_upd_range : forall T l start len (v : T) f,
  Forall f l -> f v -> Forall f (upd_range l start len v).
Proof.
(* original proof tokens: 46 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_upd_range : forall T l n n' len (v : T),
  n <= n' -> firstn n (upd_range l n' len v) = firstn n l.
Proof.
(* original proof tokens: 55 *)
intros.
rewrite upd_range_eq_upd_range'; try lia.
(* No more tactics to try *)
Admitted.

Lemma upd_range_updN_oob : forall T l start len (v v2 : T) i,
  i < start \/ i >= start + len ->
  upd_range (updN l i v2) start len v = updN (upd_range l start len v) i v2.
Proof.
(* original proof tokens: 50 *)
intros.
destruct H.
(* No more tactics to try *)
Admitted.

Lemma upd_range_upd_range : forall T l start len1 len2 (v : T),
  upd_range (upd_range l start len1 v) (start + len1) len2 v = upd_range l start (len1 + len2) v.
Proof.
(* original proof tokens: 72 *)
intros.
revert l start len1 len2 v.
induction len2; auto.
unfold upd_range.
(* No more tactics to try *)
Admitted.

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
induction vs; simpl; auto; intros; try (case start; case len; simpl; auto); try congruence.
(* No more tactics to try *)
Admitted.

Hint Rewrite upd_range_upd_range upd_range_hd : lists.
Lemma upd_range_app_l : forall T l1 l2 start len (v : T),
  start + len <= length l1 ->
  upd_range (l1 ++ l2) start len v = upd_range l1 start len v ++ l2.
Proof.
(* original proof tokens: 67 *)
intros.
rewrite upd_range_eq_upd_range'.
(* No more tactics to try *)
Admitted.

Lemma upd_range_app_r : forall T l1 l2 start len (v : T),
  length l1 <= start ->
  upd_range (l1 ++ l2) start len v = l1 ++ upd_range l2 (start - length l1) len v.
Proof.
(* original proof tokens: 65 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma upd_range_selN_oob : forall T (l : list T) start len v i d,
  i < start \/ i >= start + len ->
  selN (upd_range l start len v) i d = selN l i d.
Proof.
(* original proof tokens: 51 *)
intros.
destruct H.
(* No more tactics to try *)
Admitted.

Lemma removeN_upd_range_l : forall T (l : list T) start len v,
  removeN (upd_range l (S start) len v) start = removeN (upd_range l start (S len) v) start.
Proof.
(* original proof tokens: 23 *)
intros.
rewrite upd_range_eq_upd_range'.
(* No more tactics to try *)
Admitted.

Lemma removeN_updN_lt : forall T (l : list T) i i' v,
  i < i' ->
  removeN (updN l i v) i' = updN (removeN l i') i v.
Proof.
(* original proof tokens: 93 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_upd_range_r : forall T (l : list T) start len v,
  removeN (upd_range l start len v) (start + len) = removeN (upd_range l start (S len) v) (start + len).
Proof.
(* original proof tokens: 79 *)
intros.
rewrite upd_range_eq_upd_range'.
(* No more tactics to try *)
Admitted.

Lemma upd_range_eq_app_firstn_repeat : forall T (l : list T) start len v,
  length l <= start + len ->
  upd_range l start len v = firstn start l ++ repeat v (length l - start).
Proof.
(* original proof tokens: 257 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma upd_range_oob : forall T (l : list T) start len v,
  length l <= start ->
  upd_range l start len v = l.
Proof.
(* original proof tokens: 54 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma removeN_upd_range_mid : forall T (l : list T) start len v i i',
  start <= i < start + len ->
  start <= i' < start + len ->
  i <= i' < length l ->
  removeN (upd_range l start len v) i = removeN (upd_range l start len v) i'.
Proof.
(* original proof tokens: 491 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma concat_hom_upd_range : forall T l start len (v : T) k,
  Forall (fun x => length x = k) l ->
  concat (upd_range l start len (repeat v k)) = upd_range (concat l) (start * k) (len * k) v.
Proof.
(* original proof tokens: 190 *)
intros.
induction l; simpl.
(* No more tactics to try *)
Admitted.

Lemma upd_range_start_0 : forall T l len (v : T),
  len <= length l ->
  upd_range l 0 len v = repeat v len ++ skipn len l.
Proof.
(* original proof tokens: 67 *)
induction len; simpl.
intros v H.
(* No more tactics to try *)
Admitted.

Lemma upd_range_all : forall T l len (v : T),
  length l <= len ->
  upd_range l 0 len v = repeat v (length l).
Proof.
(* original proof tokens: 47 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma upd_range_app : forall T l1 l2 start len (v : T),
  start <= length l1 < start + len ->
  start + len <= length (l1 ++ l2) ->
  upd_range (l1 ++ l2) start len v =
    upd_range l1 start len v ++ upd_range l2 0 (len - (length l1 - start)) v.
Proof.
(* original proof tokens: 193 *)
intros.
rewrite upd_range_app_r;eauto.
inversion H.
(* No more tactics to try *)
Admitted.

Lemma In_incl : forall A (x : A) (l1 l2 : list A),
  In x l1 -> incl l1 l2 -> In x l2.
Proof.
(* original proof tokens: 9 *)
intros.
(* No more tactics to try *)
Admitted.

Definition postfix A (a b : list A) :=
  exists n, a = skipn n b.
Lemma postfix_nil : forall A (l : list A),
  postfix nil l.
Proof.
(* original proof tokens: 26 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma postfix_refl : forall A (a : list A),
  postfix a a.
Proof.
(* original proof tokens: 18 *)
(* generated proof tokens: 12 *)

exists 0; auto.
Qed.

Lemma postfix_app : forall A (l a b: list A),
  postfix l b ->
  postfix l (a ++ b).
Proof.
(* original proof tokens: 30 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma postfix_tl : forall A x (l a: list A),
  postfix l a ->
  postfix l (x :: a).
Proof.
(* original proof tokens: 20 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma postfix_singular : forall A (a : A) l,
  postfix l [ a ] -> l <> nil -> l = [ a ].
Proof.
(* original proof tokens: 49 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem rev_injective :
  forall A (l1 l2 : list A), rev l1 = rev l2 -> l1 = l2.
Proof.
(* original proof tokens: 31 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma rev_eq_iff : forall T (l l' : list T),
  l = rev l' <-> rev l = l'.
Proof.
(* original proof tokens: 35 *)
split; intros; subst; auto.
apply rev_involutive.
(* No more tactics to try *)
Admitted.

Lemma NoDup_app_not_In : forall A (l : list A) (a : A),
  NoDup (l ++ [a]) -> ~ In a l.
Proof.
(* original proof tokens: 51 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDup_rev_1 : forall A (l : list A),
  NoDup l -> NoDup (rev l).
Proof.
(* original proof tokens: 70 *)
induction l; auto.
intros H.
(* No more tactics to try *)
Admitted.

Lemma NoDup_rev_2 : forall A (l : list A),
  NoDup (rev l) -> NoDup l.
Proof.
(* original proof tokens: 61 *)
intros.
(* No more tactics to try *)
Admitted.

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
intros.
(* No more tactics to try *)
Admitted.

Lemma firstn_rev: forall T (l : list T) n, firstn n (rev l) = rev (skipn (length l - n) l).
Proof.
(* original proof tokens: 126 *)
induction l; intros; try reflexivity.
simpl.
(* No more tactics to try *)
Admitted.

Lemma combine_rev: forall A B (a : list A) (b : list B),
  length a = length b ->
  rev (combine a b) = combine (rev a) (rev b).
Proof.
(* original proof tokens: 46 *)
induction a; intros; simpl.
inversion H; subst; clear H; auto.
case b; simpl; try apply IHa; auto; try rewrite rev_cons; auto.
(* No more tactics to try *)
Admitted.

Lemma list_isolate: forall T (l : list T) m n d,
  length l = m + 1 + n ->
  l = firstn m l ++ [selN l m d] ++ rev (firstn n (rev l)).
Proof.
(* original proof tokens: 66 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma filter_length : forall A f (l : list A),
  length (filter f l) <= length l.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Definition disjoint A (a b : list A) :=
  forall x, (In x a -> ~ In x b) /\ (In x b -> ~ In x a).
Lemma disjoint_sym : forall A (a b : list A),
  disjoint a b -> disjoint b a.
Proof.
(* original proof tokens: 13 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma disjoint_nil_l : forall A (a : list A),
  disjoint nil a.
Proof.
(* original proof tokens: 13 *)
(* generated proof tokens: 18 *)

intros. unfold disjoint. intros.  auto.
Qed.

Lemma disjoint_cons_l : forall A (a b : list A) x,
  disjoint a b ->
  ~ In x b ->
  disjoint (x :: a) b.
Proof.
(* original proof tokens: 48 *)
intros.
(* No more tactics to try *)
Admitted.

Definition enumerate A (l : list A) := combine (seq 0 (length l)) l.
Theorem selN_enumerate : forall A (l : list A) d i,
  i < length l -> selN (enumerate l) i d = (i, selN l i (snd d)).
Proof.
(* original proof tokens: 41 *)
unfold enumerate.
intros.
(* No more tactics to try *)
Admitted.

Fact length_enumerate : forall T (l : list T), length (enumerate l) = length l.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma firstn_seq : forall n a b, firstn n (seq a b) = seq a (min n b).
Proof.
(* original proof tokens: 28 *)
(* generated proof tokens: 47 *)
induction n; simpl.
simpl; intros; case b; simpl; auto; rewrite IHn; auto; try lia.
destruct b; simpl; auto; rewrite IHn; auto; try lia.
Qed.

Lemma firstn_enumerate : forall A (l : list A) n, firstn n (enumerate l) = enumerate (firstn n l).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Lemma enumerate_inj : forall A (l1 l2 : list A), enumerate l1 = enumerate l2 <-> l1 = l2.
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Hint Rewrite length_enumerate firstn_enumerate selN_enumerate enumerate_inj : lists.
Definition part {T} (l : list T) (k : nat) :=
  map (fun i => firstn k (skipn (i * k) l)) (seq 0 (length l / k)).
Definition part_nil : forall T k, part (@nil T) k = nil.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma part_length : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  length (part l k) = length l / k.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma part_forall_length : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  Forall (fun x => length x = k) (part l k).
Proof.
(* original proof tokens: 102 *)
intros.
apply Forall_map.
apply Forall_forall.
intros x H1.
apply firstn_length_l.
(* No more tactics to try *)
Admitted.

Lemma concat_hom_part : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  concat (part l k) = l.
Proof.
(* original proof tokens: 213 *)
induction l; intros; auto.
(* No more tactics to try *)
Admitted.

Lemma part_hom_concat : forall T (l : list (list T)) k, Forall (fun x => length x = k) l -> k <> 0 ->
  part (concat l) k = l.
Proof.
(* original proof tokens: 105 *)
unfold part; simpl.
intros.
(* No more tactics to try *)
Admitted.

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
induction vs; simpl; intros.
inversion H; subst; auto; try lia.
inversion H; subst; auto; try lia.
inversion H; subst; auto; try lia.
inversion H; subst; auto; try lia.
inversion H; subst; auto; try lia.
inversion H; subst; auto; try lia.
inversion H; subst; auto; try lia.
apply IHvs; auto.
inversion H; subst; auto; try lia.
rewrite H7.
(* No more tactics to try *)
Admitted.

Lemma ifind_list_ok_bound : forall cond vs start r,
    ifind_list cond vs start = Some r ->
    fst r < start + length vs.
Proof.
(* original proof tokens: 67 *)
induction vs; intros; simpl.
inversion H; subst.
(* No more tactics to try *)
Admitted.

Lemma ifind_list_ok_cond : forall cond vs start r,
    ifind_list cond vs start = Some r ->
    cond (snd r) (fst r) = true.
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Lemma ifind_list_ok_item : forall cond vs start r d,
    ifind_list cond vs start = Some r ->
    selN vs ((fst r) - start) d = (snd r).
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Lemma ifind_list_ok_facts : forall cond vs start r d,
    ifind_list cond vs start = Some r ->
    (fst r) >= start /\
    (fst r) < start + length vs /\
    cond (snd r) (fst r) = true /\
    selN vs ((fst r) - start) d = (snd r).
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma ifind_list_none : forall cond l start d,
    ifind_list cond l start = None ->
    forall ix, ix < length l ->
    cond (selN l ix d) (start + ix) = false.
Proof.
(* original proof tokens: 66 *)
intros.
(* No more tactics to try *)
Admitted.

End ifind_list.
Inductive list_same {T : Type} (v : T) : list T -> Prop :=
| ListSameNil : list_same v nil
| ListSameCons : forall l, list_same v l -> list_same v (v :: l).
Lemma list_same_app_l : forall T v (a b : list T),
  list_same v (a ++ b) -> list_same v a.
Proof.
(* original proof tokens: 29 *)
(* generated proof tokens: 42 *)
intros.
induction a; auto; simpl in H; inversion H; eauto.
constructor.
constructor; auto.
apply ListSameCons.
inversion H; subst; auto.
Qed.

Lemma list_same_app_r : forall T v (a b : list T),
  list_same v (a ++ b) -> list_same v b.
Proof.
(* original proof tokens: 25 *)
(* generated proof tokens: 24 *)

induction a; simpl; auto; intros;
  inversion H; subst; auto.
Qed.

Lemma list_same_app_both : forall T v (a b : list T),
  list_same v a -> list_same v b -> list_same v (a ++ b).
Proof.
(* original proof tokens: 28 *)
induction a; intros; auto.
(* No more tactics to try *)
Admitted.

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
intros.
(* No more tactics to try *)
Admitted.

Lemma list_same_skipn : forall T (v : T) n l,
  list_same v l -> list_same v (skipn n l).
Proof.
(* original proof tokens: 32 *)
induction l; auto.
(* No more tactics to try *)
Admitted.

Lemma list_same_firstn_le : forall T (v : T) n2 n1 l,
  n2 <= n1 -> list_same v (firstn n1 l) -> list_same v (firstn n2 l).
Proof.
(* original proof tokens: 64 *)
intros.
induction H; auto.
apply IHle.
inversion H0.
(* No more tactics to try *)
Admitted.

Lemma list_same_skipn_ge : forall T (v : T) n1 n2 l,
  n2 >= n1 -> list_same v (skipn n1 l) -> list_same v (skipn n2 l).
Proof.
(* original proof tokens: 59 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma list_same_skipn_upd_range_tail : forall T (v : T) l off,
  list_same v (skipn off (upd_range l off (length l - off) v)).
Proof.
(* original proof tokens: 157 *)
intros.
apply list_same_skipn.
(* No more tactics to try *)
Admitted.

Lemma list_same_skipn_upd_range_mid : forall T (v : T) l off count,
  list_same v (skipn (off + count) l) ->
  off + count <= length l ->
  list_same v (skipn off (upd_range l off count v)).
Proof.
(* original proof tokens: 87 *)
intros.
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

(* No more tactics to try *)
Admitted.

Lemma not_in_app: forall (A : Type) (x: A) l1 l2,
  ~In x (l1++l2) -> (~In x l1) /\ (~In x l2).
Proof.
(* original proof tokens: 14 *)
intros.
(* No more tactics to try *)
Admitted.

Hint Resolve incl_app incl_appl incl_appr incl_refl : incl_app.
Lemma incl_app2r : forall T (l1 l2 l2' : list T),
  incl l2 l2' ->
  incl (l1 ++ l2) (l1 ++ l2').
Proof.
(* original proof tokens: 12 *)
intros.
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
Proof.
(* original proof tokens: 27 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_appr' : forall (A : Type) (l m n : list A),
  incl (l ++ m) n -> incl m n.
Proof.
(* original proof tokens: 27 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDup_incl_l : forall T (l1 l2 l2' : list T),
  NoDup (l1 ++ l2) ->
  NoDup l2' ->
  incl l2' l2 ->
  NoDup (l1 ++ l2').
Proof.
(* original proof tokens: 56 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDup_remove_inverse : forall T a (l' l : list T),
  NoDup (l ++ l') -> ~ In a (l ++ l') -> NoDup (l ++ a :: l').
Proof.
(* original proof tokens: 107 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDup_incl_r : forall T (l2 l1 l1' : list T),
  NoDup (l1 ++ l2) ->
  NoDup l1' ->
  incl l1' l1 ->
  NoDup (l1' ++ l2).
Proof.
(* original proof tokens: 89 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_cons2_inv : forall T (l1 l2 : list T) a,
  ~ In a l1 ->
  incl (a :: l1) (a :: l2) ->
  incl l1 l2.
Proof.
(* original proof tokens: 82 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_cons_inv : forall T (a : T) l1 l2,
  incl (a :: l1) l2 -> incl l1 l2.
Proof.
(* original proof tokens: 17 *)
(* generated proof tokens: 11 *)

apply incl_cons_inv.
Qed.

Lemma incl_cons_inv' : forall T (a : T) l1 l2,
  incl (a :: l1) l2 -> In a l2 /\ incl l1 l2.
Proof.
(* original proof tokens: 14 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_tl_inv : forall T l1 l2 (a : T),
  incl l1 (a :: l2) ->
  ~ In a l1 ->
  incl l1 l2.
Proof.
(* original proof tokens: 70 *)
intros.
(* No more tactics to try *)
Admitted.

Definition incl_count T (E : forall (a b : T), {a=b}+{a<>b}) (l1 l2 : list T) :=
  forall x, count_occ E l1 x <= count_occ E l2 x.
Definition permutation T (E : forall (a b : T), {a=b}+{a<>b}) (l1 l2 : list T) :=
  forall x, count_occ E l1 x = count_occ E l2 x.
Lemma count_occ_app : forall T E (l1 l2 : list T) x,
  count_occ E (l1 ++ l2) x = count_occ E l1 x + count_occ E l2 x.
Proof.
(* original proof tokens: 33 *)
(* generated proof tokens: 11 *)

apply count_occ_app.
Qed.

Lemma count_occ_remove_ne : forall T E (l : list T) a b,
  a <> b ->
  count_occ E (remove E a l) b = count_occ E l b.
Proof.
(* original proof tokens: 93 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_In: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1: list T) n l2,
  incl_count E (n ::l2) l1 ->
  In n l1.
Proof.
(* original proof tokens: 75 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_not_In: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T) x,
    count_occ E l x <= 0 ->
    ~In x l.
Proof.
(* original proof tokens: 111 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma count_occ_NoDup: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T),
  NoDup l <->
  forall x, count_occ E l x <= 1.
Proof.
(* original proof tokens: 221 *)
split; intros.
(* No more tactics to try *)
Admitted.

Lemma count_occ_NoDup_dec: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T) x,
  NoDup l -> count_occ E l x = 0 \/ count_occ E l x = 1.
Proof.
(* original proof tokens: 79 *)

(* No more tactics to try *)
Admitted.

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
intros.
(* No more tactics to try *)
Admitted.

Lemma permutation_incl_count : forall T E (l1 l2 : list T),
  permutation E l1 l2 ->
  incl_count E l1 l2.
Proof.
(* original proof tokens: 23 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_tl : forall T E (l1 l2 : list T) x,
  incl_count E l1 l2 ->
  incl_count E l1 (x :: l2).
Proof.
(* original proof tokens: 32 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_cons : forall T E (l1 l2 : list T) x,
  incl_count E l1 l2 ->
  incl_count E (x :: l1) (x :: l2).
Proof.
(* original proof tokens: 32 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_cons': forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1 l2: list T) n,
  incl_count E (n::l1) (n::l2) ->
  incl_count E l1 l2.
Proof.
(* original proof tokens: 53 *)
intros.
unfold incl_count in *.
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
Proof.
(* original proof tokens: 31 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_rotate_one : forall T E (l1 l2 l2' : list T) x,
  incl_count E l1 (Hidden_App.app l2 (l2' ++ [x])) ->
  incl_count E l1 (Hidden_App.app (x :: l2) l2').
Proof.
(* original proof tokens: 49 *)
intros.
apply incl_count_rotate_start.
rewrite Hidden_App.app_is in H.
rewrite Hidden_App.app_is in *.
(* No more tactics to try *)
Admitted.

Lemma incl_count_rotate_cons : forall T E (l1 l2 l2' : list T) x,
  incl_count E l1 (l2 ++ l2') ->
  incl_count E (x :: l1) (Hidden_App.app (x :: l2) l2').
Proof.
(* original proof tokens: 39 *)
intros.
unfold incl_count.
(* No more tactics to try *)
Admitted.

Lemma incl_count_nil : forall T E (l : list T),
  incl_count E [] l.
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 19 *)

intros.
 unfold incl_count.
 intros.
 simpl.
 lia.
Qed.

Lemma incl_count_trans : forall T E (l1 l2 l3 : list T),
  incl_count E l1 l2 ->
  incl_count E l2 l3 ->
  incl_count E l1 l3.
Proof.
(* original proof tokens: 28 *)
intros.
unfold incl_count.
intros x.
(* No more tactics to try *)
Admitted.

Lemma incl_count_refl : forall T E (l : list T),
  incl_count E l l.
Proof.
(* original proof tokens: 15 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma count_occ_remove_eq: forall T E (l : list T) x,
  count_occ E (remove E x l) x = 0.
Proof.
(* original proof tokens: 35 *)
destruct l; simpl; auto; try lia.
intros.
simpl; case (E x t); intros; try lia.
(* No more tactics to try *)
Admitted.

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
(* No more tactics to try *)
Admitted.

Lemma incl_count_add: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1 l2: list T) x,
  incl_count E l1 l2 ->
  incl_count E (x::l1) (x::l2).
Proof.
(* original proof tokens: 45 *)
(* generated proof tokens: 14 *)
intros.
apply incl_count_cons; auto.
Qed.

Lemma permutation_trans : forall T E (l1 l2 l3 : list T),
  permutation E l1 l2 ->
  permutation E l2 l3 ->
  permutation E l1 l3.
Proof.
(* original proof tokens: 27 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma permutation_refl : forall T E (l : list T),
  permutation E l l.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma permutation_comm : forall T E (l1 l2 : list T),
  permutation E l1 l2 ->
  permutation E l2 l1.
Proof.
(* original proof tokens: 9 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma permutation_cons: forall T E (l l' : list T) x,
  permutation E l l' ->
  permutation E (x :: l) (x :: l').
Proof.
(* original proof tokens: 22 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_app_comm : forall T E (l1 l2 : list T),
  incl_count E (l1 ++ l2) (l2 ++ l1).
Proof.
(* original proof tokens: 22 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma permutation_app_comm : forall T E (l1 l2 : list T),
  permutation E (l1 ++ l2) (l2 ++ l1).
Proof.
(* original proof tokens: 21 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma permutation_app_split : forall T E (l1 l1' l2 l2' : list T),
  permutation E l1 l1' ->
  permutation E l2 l2' ->
  permutation E (l1 ++ l2) (l1' ++ l2').
Proof.
(* original proof tokens: 34 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma permutation_remove: forall T E (l l' : list T) x,
  permutation E l l' ->
  permutation E (remove E x l) (remove E x l').
Proof.
(* original proof tokens: 46 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma permutation_in: forall T E (l l' : list T) x,
  permutation E l l' -> In x l -> In x l'.
Proof.
(* original proof tokens: 28 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma incl_count_app_split : forall T E (l1 l1' l2 l2' : list T),
  incl_count E l1 l1' ->
  incl_count E l2 l2' ->
  incl_count E (l1 ++ l2) (l1' ++ l2').
Proof.
(* original proof tokens: 35 *)
intros.
(* No more tactics to try *)
Admitted.

Hint Resolve incl_count_trans incl_count_refl incl_count_app_comm incl_count_app_split : incl_count_app.
Hint Resolve permutation_trans permutation_refl permutation_app_comm permutation_app_split : permutation_app.
Definition NoDupApp (T : Type) (l : list (list T)) := NoDup (concat l).
Lemma NoDupApp_pick : forall T (l1 l2 l3 : list (list T)),
  NoDupApp (l1 ++ l2 ++ l3) -> NoDupApp (l2 ++ l1 ++ l3).
Proof.
(* original proof tokens: 44 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDupApp_cons_nil : forall T (l : list (list T)),
  NoDupApp ([] :: l) <-> NoDupApp l.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 18 *)

split; intros; subst; simpl in *; auto.
Qed.

Lemma NoDupApp_cons : forall T a (l : list (list T)),
  NoDupApp l ->
  NoDup a ->
  (forall x, In x a -> ~ In x (concat l)) ->
  NoDupApp (a :: l).
Proof.
(* original proof tokens: 78 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma NoDupApp_In : forall T a (l : list (list T)),
  NoDupApp l ->
  In a l ->
  NoDup a.
Proof.
(* original proof tokens: 76 *)
intros.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 47 *)
intros.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 50 *)
intros.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 13 *)
(* generated proof tokens: 22 *)

intros.
unfold NoDupApp.
rewrite H.
reflexivity.
Qed.

Lemma concat_build_app : forall T (a b : list T) la lb,
  a = concat la ->
  b = concat lb ->
  a ++ b = concat (la ++ lb).
Proof.
(* original proof tokens: 17 *)
intros.
rewrite H.
rewrite H0.
(* No more tactics to try *)
Admitted.

Lemma concat_build_cons : forall T a (b : list T) lb,
  b = concat lb ->
  a :: b = concat ([[a]] ++ lb).
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Lemma concat_build_nil : forall T,
  @nil T = concat nil.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 10 *)

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
Proof.
(* original proof tokens: 27 *)
intros.
apply NoDup_app_comm.
(* No more tactics to try *)
Admitted.

Example nodupapp_3_5 : forall (a : list nat) b c d e,
  NoDup (a ++ b ++ c ++ d :: e) ->
  NoDup (b ++ d :: c).
Proof.
(* original proof tokens: 27 *)
intros.
eapply NoDup_app_r.
eapply NoDup_app_r.
eapply NoDup_app_l.
eapply NoDup_app_r.
eapply NoDup_app_l.
eapply NoDup_app_r.
eapply NoDup_app_l.
eapply NoDup_app_r.
eapply NoDup_app_r.
apply NoDup_3app_rev.
(* Reached max number of model calls *)
Admitted.

Definition selN_each {T} (l : list (list T)) n (def : T) : list T :=
  map (fun l => selN l n def) l.
Lemma selN_each_S: forall T (l : list (list T)) n def,
  selN_each l (S n) def = selN_each (map (skipn 1) l) n def.
Proof.
(* original proof tokens: 41 *)
unfold selN_each.
simpl.
(* No more tactics to try *)
Admitted.

Lemma NoDup_NoDupA_eq: forall T E,
  (forall x y, E x y <-> x = y) ->
  forall (l : list T),
  NoDupA E l <-> NoDup l.
Proof.
(* original proof tokens: 137 *)
intros.
apply iff_sym.
split.
(* No more tactics to try *)
Admitted.

Lemma NoDup_filter: forall T f (l : list T),
  NoDup l -> NoDup (filter f l).
Proof.
(* original proof tokens: 43 *)
(* generated proof tokens: 11 *)

apply NoDup_filter.
Qed.

Lemma combine_no_dup: forall A B (a : list A) (b : list B),
  NoDup a \/ NoDup b -> NoDup (List.combine a b).
Proof.
(* original proof tokens: 68 *)
intros.
destruct H.
(* No more tactics to try *)
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
apply filter_ext; assumption.
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
Proof.
(* original proof tokens: 70 *)

(* No more tactics to try *)
Admitted.

Lemma index_of_inb: forall T (l : list T) f,
  (exists x, In x l /\ f x = true) ->
  index_of f l < length l.
Proof.
(* original proof tokens: 119 *)

(* No more tactics to try *)
Admitted.

Lemma inb_spec: forall T E l x,
  In x l <-> @inb T E l x = true.
Proof.
(* original proof tokens: 23 *)
unfold inb.
(* No more tactics to try *)
Admitted.

Lemma sort_by_index_length: forall S T t f (l : list (S * T)) s0 t0,
  length (sort_by_index f l t s0 t0) = length t.
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 14 *)

induction t; simpl; auto.
Qed.

Lemma sort_by_index_spec: forall S T (ls : list (S * T)) f lt s0 t0,
  (forall x, In x lt -> In x (snd (split ls))) ->
  (forall a b, f a b = true <-> a = b) ->
  snd (split (sort_by_index f ls lt s0 t0)) = lt.
Proof.
(* original proof tokens: 301 *)
induction lt; simpl.
intros.
auto.
(* No more tactics to try *)
Admitted.

Lemma index_of_in_sort_by_index: forall T V (fn : T -> V) f (l : list T) d x,
  In x l ->
  NoDup (map fn l) ->
  (forall x y, f x y = true <-> x = y) ->
  selN l (index_of (fun a => f (fn x) (fn a)) l) d = x.
Proof.
(* original proof tokens: 210 *)

(* No more tactics to try *)
Admitted.

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

(* No more tactics to try *)
Admitted.

Lemma in_sort_by_index: forall S T f t (l : list (S * T)) (x : S * T) s0 t0,
  NoDup t -> NoDup l ->
  (forall x, In x t -> exists y, In (y, x) l) ->
  (forall x y, f x y = true <-> x = y) ->
  In x (sort_by_index f l t s0 t0) -> In x l /\ In (snd x) t.
Proof.
(* original proof tokens: 216 *)
intros.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Lemma sort_by_index_combine: forall A B f (la : list A) (lb : list B) t a0 b0,
  length la = length lb ->
  incl t lb ->
  (forall x y, f x y = true <-> x = y) ->
  let s := sort_by_index f (List.combine la lb) t a0 b0 in
  s = List.combine (fst (split s)) t.
Proof.
(* original proof tokens: 100 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma partition_eq_filter: forall T (l : list T) f,
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma filter_map_ext: forall T T' f f' (g : T -> T') l,
  (forall x, In x l -> f x = f' (g x)) ->
  filter f' (map g l) = map g (filter f l).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 65 *)

(* No more tactics to try *)
Admitted.

Lemma filter_selN_length: forall T f (l : list T) d,
  length (filter f l) = length (filter (fun i => f (selN l i d)) (seq 0 (length l))).
Proof.
(* original proof tokens: 52 *)
unfold selN.
(* No more tactics to try *)
Admitted.

Lemma permutation_filter: forall T E (l l' : list T),
  NoDup l -> NoDup l' ->
  incl l' l ->
  Permutation.Permutation (filter (@inb _ E l') l) l'.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

