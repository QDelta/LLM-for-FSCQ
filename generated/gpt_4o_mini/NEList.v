Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import List.
Require Import ListUtils.
Require Import Word.
Import ListNotations.
Set Implicit Arguments.
Section ListRevSel.
Variable T : Type.
Variable l : (list T).
Definition selR n def :=
    if lt_dec n (length l) then selN l (length l - n - 1) def else def.
Lemma selR_oob : forall n def,
    n >= length l -> selR n def = def.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma selR_inb : forall n def,
    n < length l -> selR n def = selN l (length l - n - 1) def.
Proof.
(* original proof tokens: 30 *)
replace selR with (fun n def => if lt_dec n (length l) then selN l (length l - n - 1) def else def).
replace selR with (fun n def => if lt_dec n (length l) then selN l (length l - n - 1) def else def).
(* No more tactics to try *)
Admitted.

End ListRevSel.
Section NonEmptyList.
Variable T : Type.
Definition nelist  := (T * list T)%type.
Definition singular x : nelist := (x, nil).
Definition latest (ds : nelist) := hd (fst ds) (snd ds).
Definition latest_cons : forall d0 d ds, latest (d0, d :: ds) = d.
Proof.
(* original proof tokens: 11 *)
(* generated proof tokens: 11 *)

simpl. reflexivity.
Qed.

Definition nthd n (ds : nelist) := selN (snd ds) (length (snd ds) - n) (fst ds).
Lemma nthd_0 : forall ds, nthd 0 ds = fst ds.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_oob : forall ds n, n >= length (snd ds) -> nthd n ds = latest ds.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Definition pushd (d : T) (ds : nelist) : nelist :=
      (fst ds, d :: snd ds).
Theorem latest_pushd : forall d ds,
    latest (pushd d ds) = d.
Proof.
(* original proof tokens: 18 *)

(* No more tactics to try *)
Admitted.

Fixpoint pushdlist (dlist : list T) (ds : nelist) : nelist :=
      match dlist with
      | nil => ds
      | d :: dlist' => pushdlist dlist' (pushd d ds)
      end.
Definition popn (n : nat) (ds : nelist) : nelist :=
      (nthd n ds, cuttail n (snd ds)).
Lemma popn_0 : forall ds,
    popn 0 ds = ds.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma popn_oob : forall ds n,
    n >= length (snd ds) -> popn n ds = (latest ds, nil).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma singular_latest : forall ds, snd ds = nil -> latest ds = fst ds.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma singular_nthd : forall ds n, snd ds = nil -> nthd n ds = fst ds.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma popn_oob_singular' : forall ds n,
    n >= length (snd ds) -> snd (popn n ds) = nil.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Lemma popn_oob_singular : forall ds n,
    n >= length (snd ds) -> popn n ds = singular (latest ds).
Proof.
(* original proof tokens: 34 *)
(* generated proof tokens: 12 *)

apply popn_oob.
Qed.

Lemma popn_popn : forall ds m n,
    popn m (popn n ds) = popn (n + m) ds.
Proof.
(* original proof tokens: 178 *)
simpl; induction m; auto.
(* No more tactics to try *)
Admitted.

Lemma popn_tail : forall n d0 d ds,
    popn (S n) (d0, ds ++ [d]) = popn n (d, ds).
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Lemma pushdlist_app : forall d l' l,
    pushdlist l' (d, l) = (d, (rev l') ++ l)%list.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_popn : forall m n ds,
    nthd n (popn m ds) = nthd (m + n) ds.
Proof.
(* original proof tokens: 152 *)

(* No more tactics to try *)
Admitted.

Definition d_in d (l : nelist) := d = fst l \/ In d (snd l).
Theorem d_in_pushdlist : forall dlist ds d,
    d_in d (pushdlist dlist ds) ->
    In d dlist \/ d_in d ds.
Proof.
(* original proof tokens: 64 *)

(* No more tactics to try *)
Admitted.

Theorem d_in_app : forall d a l1 l2,
    d_in d (a, (l1 ++ l2)) ->
    In d l1 \/ d_in d (a, l2).
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

Theorem nthd_in_ds : forall ds n,
    d_in (nthd n ds) ds.
Proof.
(* original proof tokens: 64 *)

(* No more tactics to try *)
Admitted.

Theorem latest_in_ds : forall ds,
    d_in (latest ds) ds.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Theorem d_in_In : forall d d' l,
    d_in d (d', l) -> In d (d' :: l).
Proof.
(* original proof tokens: 16 *)
(* generated proof tokens: 35 *)

intros d d' l H. destruct H as [H | H].
- subst. left. reflexivity.
- right. assumption.
Qed.

Theorem d_in_In' : forall d d' l,
    In d (d' :: l) -> d_in d (d', l).
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma d_in_pushd : forall ds d d',
    d_in d (pushd d' ds) ->
    d = d' \/ d_in d ds.
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

Lemma d_in_nthd: forall l d,
    d_in d l ->
    exists n, d = nthd n l.
Proof.
(* original proof tokens: 101 *)

(* No more tactics to try *)
Admitted.

Lemma latest_nthd: forall l,
    latest l = nthd (Datatypes.length (snd l)) l.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Lemma pushd_latest: forall l d,
    latest (pushd d l)  = d.
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma length_popn : forall n ds,
    length (snd (popn n ds)) = length (snd ds) - n.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma latest_popn : forall n ds,
    latest (popn n ds) = latest ds.
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Inductive NEListSubset : nelist -> nelist -> Prop :=
  | NESubsetNil : forall d, NEListSubset (d, nil) (d, nil)
  | NESubsetHead : forall ds d',
      NEListSubset (pushd d' ds) (d', nil)
  | NESubsetIn : forall ds ds' d,
      NEListSubset ds ds'
      -> NEListSubset (pushd d ds) (pushd d ds')
  | NESubsetNotIn : forall ds ds' d,
      NEListSubset ds ds'
      -> NEListSubset (pushd d ds) ds'.
Inductive ListSubset (T : Type) : list T -> list T -> Prop :=
  | SubsetNil : ListSubset nil nil
  | SubsetIn : forall l1 l2 a, ListSubset l1 l2 -> ListSubset (a :: l1) (a :: l2)
  | SubsetNotIn : forall l1 l2 a, ListSubset l1 l2 -> ListSubset (a :: l1) l2.
Hint Constructors ListSubset.
Lemma list_subset_nil : forall T (l : list T),
    ListSubset l nil.
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 54 *)

induction l as [| a l' IH].
- (* Case: l = nil *) 
  apply SubsetNil.
- (* Case: l = a :: l' *)
  apply SubsetNotIn.
  apply IH.
Qed.

Lemma nelist_list_subset : forall ds ds',
    NEListSubset ds ds' <-> ListSubset (snd ds ++ [fst ds]) (snd ds' ++ [fst ds']).
Proof.
(* original proof tokens: 473 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_equal : forall ds,
    NEListSubset ds ds.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_oldest : forall l t,
    NEListSubset (t, l) (t, nil).
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_latest : forall ds,
    NEListSubset ds (latest ds, nil).
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_oldest_latest' : forall l t,
    length l > 0
    -> NEListSubset (t, l) (t, hd t l :: nil).
Proof.
(* original proof tokens: 103 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_oldest_latest : forall ds,
    length (snd ds) > 0
    -> NEListSubset ds (fst ds, latest ds :: nil).
Proof.
(* original proof tokens: 23 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_popn1 : forall ds ds',
    NEListSubset (popn 1 ds) ds' ->
    NEListSubset ds ds'.
Proof.
(* original proof tokens: 386 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_popn : forall n ds ds',
    NEListSubset (popn n ds) ds' ->
    NEListSubset ds ds'.
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_nthd_latest : forall n ds,
    n < length (snd ds) ->
    NEListSubset ds (nthd n ds, latest ds :: nil).
Proof.
(* original proof tokens: 89 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_popn1' : forall ds ds',
    NEListSubset ds ds' ->
    NEListSubset ds (popn 1 ds').
Proof.
(* original proof tokens: 326 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_popn' : forall n ds ds',
    NEListSubset ds ds' ->
    NEListSubset ds (popn n ds').
Proof.
(* original proof tokens: 65 *)
induction n as [| n IH].
(* No more tactics to try *)
Admitted.

Lemma pushd_length : forall ds d,
    length (snd (pushd d ds)) = S (length (snd ds)).
Proof.
(* original proof tokens: 18 *)
(* generated proof tokens: 8 *)

auto.
Qed.

Lemma pushdlist_length: forall dlist ds,
    length (snd (pushdlist dlist ds)) =
    length dlist + length (snd ds).
Proof.
(* original proof tokens: 37 *)
simpl; induction dlist as [|d dlist' IHdlist']; simpl; auto.
(* No more tactics to try *)
Admitted.

Lemma nthd_pushd : forall l t n d,
    n <= length l
    -> nthd n (pushd d (t, l)) = nthd n (t, l).
Proof.
(* original proof tokens: 81 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_pushd' : forall ds n d,
    n <= length (snd ds)
    -> nthd n (pushd d ds) = nthd n ds.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_pushd_latest : forall l t d n,
    n = S (length l)
    -> nthd n (pushd d (t, l)) = d.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma nthd_pushd_latest' : forall ds d n,
    n = S (length (snd ds))
    -> nthd n (pushd d ds) = d.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma popn_pushd_comm : forall d ds n,
    n <= length (snd ds) ->
    popn n (pushd d ds) = pushd d (popn n ds).
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma nelist_subset_nthd : forall ds ds',
    NEListSubset ds ds'
    -> forall n' d,
        n' <= length (snd ds')
        -> nthd n' ds' = d
        -> exists n, n <= length (snd ds) /\ nthd n ds = d.
Proof.
(* original proof tokens: 260 *)

(* No more tactics to try *)
Admitted.

End NonEmptyList.
Notation " ds '!!'" := (latest ds) (at level 1).
Definition d_map A B (f : A -> B) (ds : nelist A) :=
  (f (fst ds), map f (snd ds)).
Lemma d_map_latest : forall A B (f : A -> B) ds,
  latest (d_map f ds) = f (latest ds).
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma d_map_fst : forall A B (f : A -> B) ds,
  fst (d_map f ds) = f (fst ds).
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 21 *)

intros A B f ds. 
simpl. 
reflexivity.
Qed.

Lemma d_map_nthd : forall A B (f : A -> B) ds n,
  nthd n (d_map f ds) = f (nthd n ds).
Proof.
(* original proof tokens: 98 *)

(* No more tactics to try *)
Admitted.

Lemma d_in_d_map : forall A B ds (f : A -> B) d,
  d_in d (d_map f ds) ->
  exists d', d_in d' ds /\ d = f d'.
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Lemma dmap_popn_comm : forall A B n f (ds : nelist A),
  @popn B n (d_map f ds) = d_map f (popn n ds).
Proof.
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Definition NEforall T (p : T -> Prop) (l : nelist T) :=
  p (fst l) /\ Forall p (snd l).
Definition NEforall2 T1 T2 (p : T1 -> T2 -> Prop) (l1 : nelist T1) (l2 : nelist T2) :=
  p (fst l1) (fst l2) /\ Forall2 p (snd l1) (snd l2).
Theorem NEforall2_pushd : forall T1 T2 (p : T1 -> T2 -> _) l1 l2 e1 e2,
  NEforall2 p l1 l2 ->
  p e1 e2 ->
  NEforall2 p (pushd e1 l1) (pushd e2 l2).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Theorem NEforall_impl : forall T (p1 p2 : T -> Prop) l,
  NEforall p1 l ->
  (forall a, p1 a -> p2 a) ->
  NEforall p2 l.
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Theorem NEforall2_impl : forall T1 T2 (p1 p2 : T1 -> T2 -> Prop) l1 l2,
  NEforall2 p1 l1 l2 ->
  (forall a b, p1 a b -> p2 a b) ->
  NEforall2 p2 l1 l2.
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Theorem NEforall2_exists : forall T1 T2 (p p' : T1 -> T2 -> Prop) (f2 : T2 -> T2) l1 l2,
  NEforall2 p l1 l2 ->
  (forall e1 e2, p e1 e2 -> exists e1', p' e1' (f2 e2)) ->
  exists l1',
  NEforall2 p' l1' (d_map f2 l2).
Proof.
(* original proof tokens: 120 *)

(* No more tactics to try *)
Admitted.

Theorem NEforall2_d_map : forall T1 T2 A B (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) l1 (f1 : A -> T1) l2 (f2 : B -> T2),
  (forall a b n, a = nthd n l1 -> b = nthd n l2 -> q a b -> p (f1 a) (f2 b)) ->
  NEforall2 q l1 l2 ->
  NEforall2 p (d_map f1 l1) (d_map f2 l2).
Proof.
(* original proof tokens: 253 *)

(* No more tactics to try *)
Admitted.

Lemma NEforall_d_in : forall T (p : T -> Prop) l x,
  NEforall p l ->
  d_in x l ->
  p x.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma NEforall_d_in':
  forall T (p : T -> Prop) l, (forall x, d_in x l -> p x) -> NEforall p l.
Proof.
(* original proof tokens: 68 *)

(* No more tactics to try *)
Admitted.

Lemma NEforall2_length : forall T1 T2 (p : T1 -> T2 -> Prop) l1 l2,
  NEforall2 p l1 l2 ->
  Datatypes.length (snd l1) = Datatypes.length (snd l2).
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma NEforall2_d_in : forall T1 T2 (p : T1 -> T2 -> Prop) l1 l2 x y n,
  NEforall2 p l1 l2 ->
  x = nthd n l1 ->
  y = nthd n l2 ->
  p x y.
Proof.
(* original proof tokens: 104 *)

(* No more tactics to try *)
Admitted.

Lemma NEforall2_latest: forall (T1 T2 : Type) (p : T1 -> T2 -> Prop) (l1 : nelist T1)
    (l2 : nelist T2),
  NEforall2 p l1 l2 -> p (l1 !!) (l2 !!).
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Definition list2nelist A def (l: list A) : nelist A :=
  match l with
  | nil => def
  | h::t => pushdlist (rev t) (singular h)
  end.
Definition nelist2list A (nel: nelist A) : list A := (fst nel)::(snd nel).
Lemma nelist2list2nelist: forall A (l: nelist A) def, 
  list2nelist def (nelist2list l) = l.
Proof.
(* original proof tokens: 53 *)

(* No more tactics to try *)
Admitted.

Lemma list2nelist2list: forall A (l: list A) def, 
  l<>nil -> nelist2list (list2nelist def l) = l.
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

