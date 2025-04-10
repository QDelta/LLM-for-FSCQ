Require Import Mem.
Require Import Prog.
Require Import List.
Require Import Array.
Require Import Pred.
Require Import FunctionalExtensionality.
Require Import Word.
Require Import WordAuto.
Require Import Lia.
Require Import Ring.
Require Import SepAuto.
Require Import ListUtils.
Require Import ListPred.
Import PeanoNat.
Set Implicit Arguments.
Definition list2nmem (A: Type) (l: list A) : (@mem nat Peano_dec.eq_nat_dec A) :=
  fun a => selN (map (@Some A) l) a None.
Notation "[[[ NS ':::' P ]]]" := [[ (P)%pred (list2nmem NS) ]]%pred : pred_scope.
Notation "【 NS '‣‣' P 】" := [[ (P)%pred (list2nmem NS) ]]%pred : pred_scope.
Theorem list2nmem_oob : forall A (l : list A) i,
  i >= length l
  -> (list2nmem l) i = None.
Proof.
(* original proof tokens: 30 *)
unfold list2nmem. intros A l i H. rewrite selN_oob. auto.
apply Nat.le_trans with (length l).
rewrite map_length.
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
apply Nat.le_trans with (length l).
(* Reached max number of model calls *)
Admitted.

Theorem list2nmem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2nmem l)
  -> i < length l.
Proof.
(* original proof tokens: 65 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2nmem l)
  -> x = selN l i def.
Proof.
(* original proof tokens: 65 *)

(* No more tactics to try *)
Admitted.

Lemma listupd_memupd: forall A l i (v : A),
  i < length l
  -> list2nmem (updN l i v) = Mem.upd (list2nmem l) i v.
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_updN: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2nmem l)
  -> (F * i |-> y)%pred (list2nmem (updN l i y)).
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_updN_selN : forall A F (l : list A) a v1 def,
  (F * a |-> v1)%pred (list2nmem (updN l a v1)) ->
  (F * a |-> selN l a def)%pred (list2nmem l).
Proof.
(* original proof tokens: 90 *)

(* No more tactics to try *)
Admitted.

Theorem listapp_memupd: forall A l (a : A),
  list2nmem (l ++ a :: nil) = Mem.upd (list2nmem l) (length l) a.
Proof.
(* original proof tokens: 195 *)

(* No more tactics to try *)
Admitted.

Theorem listapp_meminsert: forall A l (a : A),
  list2nmem (l ++ a :: nil) = Mem.insert (list2nmem l) (length l) a.
Proof.
(* original proof tokens: 225 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_app: forall A (F : @pred _ _ A) l a,
  F (list2nmem l)
  -> (F * (length l) |-> a)%pred (list2nmem (l ++ a :: nil)).
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_arrayN_app: forall A (F : @pred _ _ A) l l',
  F (list2nmem l) ->
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) (length l) l') %pred (list2nmem (l ++ l')).
Proof.
(* original proof tokens: 176 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_removelast_is : forall A l (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (Compare_dec.lt_dec i (length l - 1)) then Some (selN l i def) else None.
Proof.
(* original proof tokens: 100 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_removelast_list2nmem : forall A (l : list A) (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (Peano_dec.eq_nat_dec i (length l - 1)) then None else (list2nmem l) i.
Proof.
(* original proof tokens: 119 *)

(* No more tactics to try *)
Admitted.

Lemma mem_disjoint_either: forall AT AEQ V (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2
  -> m1 a = Some v -> m2 a = None.
Proof.
(* original proof tokens: 58 *)
(* generated proof tokens: 13 *)

apply mem_disjoint_either.
Qed.

Theorem list2nmem_removelast: forall A F (l : list A) v,
  l <> nil
  -> (F * (length l - 1) |-> v)%pred (list2nmem l)
  -> F (list2nmem (removelast l)).
Proof.
(* original proof tokens: 140 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_except_last : forall T (l : list T) x,
  mem_except (list2nmem (l ++ x::nil)) (length l) = list2nmem l.
Proof.
(* original proof tokens: 116 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array: forall  A (l : list A),
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l (list2nmem l).
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array': forall  A (l l' : list A),
  l = l' ->
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l' (list2nmem l).
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_arrayN_firstn_skipn: forall A (l:list A) n,
  (arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 (firstn n l) *
   arrayN (@ptsto _ Peano_dec.eq_nat_dec A) n (skipn n l))%pred (list2nmem l).
Proof.
(* original proof tokens: 126 *)

(* No more tactics to try *)
Admitted.

Lemma listpred_ptsto_list2nmem: forall T t (l : list T),
  listpred (fun a => a |->?)%pred t (list2nmem l) ->
  Permutation.Permutation t (seq 0 (length l)).
Proof.
(* original proof tokens: 271 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_ptsto_linked: forall S V t l,
  arrayN (ptsto (V:=S)) 0 l =p=> listpred (fun a => exists v, a |-> v) t ->
  @listpred _ _ Nat.eq_dec V (fun a => a |->?) (seq 0 (length l)) =p=> listpred (fun a => a |->?) t.
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Definition list2nmem_off (A: Type) (start : nat) (l: list A) : (nat -> option A) :=
  fun a => if Compare_dec.lt_dec a start then None
                             else selN (map (@Some A) l) (a - start) None.
Theorem list2nmem_off_eq : forall A (l : list A), list2nmem l = list2nmem_off 0 l.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Fixpoint list2nmem_fix (A : Type) (start : nat) (l : list A) : (nat -> option A) :=
  match l with
  | nil => fun a => None
  | h :: l' => fun a => if Peano_dec.eq_nat_dec a start then Some h else list2nmem_fix (S start) l' a
  end.
Lemma list2nmem_fix_below : forall (A : Type) (l : list A) start a,
  a < start -> list2nmem_fix start l a = None.
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_fix_off_eq : forall A (l : list A) n,
  list2nmem_off n l = list2nmem_fix n l.
Proof.
(* original proof tokens: 187 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_fix_eq : forall A (l : list A),
  list2nmem l = list2nmem_fix 0 l.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_off_app_union : forall A (a b : list A) start,
  list2nmem_off start (a ++ b) = @mem_union _ Peano_dec.eq_nat_dec A (list2nmem_off start a)
                                                           (list2nmem_off (start + length a) b).
Proof.
(* original proof tokens: 115 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_off_disjoint : forall A (a b : list A) sa sb,
  (sb >= sa + length a \/ sa >= sb + length b) ->
  @mem_disjoint _ Peano_dec.eq_nat_dec A (list2nmem_off sa a) (list2nmem_off sb b).
Proof.
(* original proof tokens: 76 *)
firstorder.
(* No more tactics to try *)
Admitted.

Lemma list2nmem_nil_array : forall A (l : list A) start,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) start l (list2nmem nil) -> l = nil.
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_array_nil : forall A (l : list A) start,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) start nil (list2nmem_fix start l) -> l = nil.
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_eq': forall A (l' l : list A) start,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) start l (list2nmem_fix start l')
  -> l' = l.
Proof.
(* original proof tokens: 276 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_eq: forall A (l' l : list A),
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l (list2nmem l')
  -> l' = l.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_mem_eq : forall V (l : list V) m,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec V) 0 l m ->
  m = list2nmem l.
Proof.
(* original proof tokens: 205 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_app_eq: forall A (l l' : list A) a,
  (arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l * (length l) |-> a)%pred (list2nmem l')
  -> l' = (l ++ a :: nil).
Proof.
(* original proof tokens: 140 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_some_bound' : forall A (m : list A) start off a,
  list2nmem_fix start m off = Some a
  -> off + 1 <= start + length m.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_some_bound : forall A (m : list A) off a,
  list2nmem m off = Some a
  -> off + 1 <= length m.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_arrayN_bound : forall A (l m : list A) off F,
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off l)%pred (list2nmem m)
  -> l = nil \/ off + length l <= length m.
Proof.
(* original proof tokens: 82 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_arrayN_length : forall A (l m : list A) F,
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) 0 l)%pred (list2nmem m)
  -> length l <= length m.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_ptsto_bound : forall A (l : list A) off v F,
  (F * off |-> v)%pred (list2nmem l)
  -> off < length l.
Proof.
(* original proof tokens: 75 *)

(* No more tactics to try *)
Admitted.

Definition arrayN_ex A VP pts (vs : list A) i : @pred _ _ VP :=
  (arrayN pts 0 (firstn i vs) *
   arrayN pts (i + 1) (skipn (S i) vs))%pred.
Lemma arrayN_ex_one: forall V VP (pts : _ -> _ -> @pred _ _ VP) (l : list V),
    List.length l = 1 ->
    arrayN_ex pts l 0 <=p=> emp.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_except : forall T V (vs : list T) (def : T) i (pts: _ -> _ -> @pred _ _ V),
  i < length vs
  -> arrayN pts 0 vs <=p=>
    (arrayN_ex pts vs i) * (pts i (selN vs i def)).
Proof.
(* original proof tokens: 40 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_except_upd : forall V T vs (v : T) i (pts : nat -> T -> @pred _ _ V),
  i < length vs
  -> arrayN pts 0 (updN vs i v) <=p=>
    (arrayN_ex pts vs i) * (pts i v).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_ex_updN_eq : forall T A l i (v : A) (pts : _ -> _ -> @pred _ _ T),
  arrayN_ex pts (updN l i v) i <=p=>
  arrayN_ex pts l i.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_mem_upd_none : forall V vs i m (v d : V) (p : nat -> V -> pred),
  m i = None ->
  i < length vs ->
  arrayN_ex p vs i m ->
  p i (selN vs i d) (fun a => if Peano_dec.eq_nat_dec a i then Some v else None) ->
  arrayN p 0 vs (Mem.upd m i v).
Proof.
(* original proof tokens: 109 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_pick : forall V l (def : V) i,
  i < length l
  -> (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l).
Proof.
(* original proof tokens: 30 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_updN : forall V ol nl (v : V) i,
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) ol i * i |-> v)%pred (list2nmem nl)
  -> i < length ol
  -> nl = updN ol i v.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_removelast_eq : forall V (nl ol : list V),
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) ol (length ol - 1))%pred (list2nmem nl)
  -> length ol > 0
  -> nl = removelast ol.
Proof.
(* original proof tokens: 79 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_array_exis : forall V l (def : V) i,
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l)
  -> (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |->?)%pred (list2nmem l).
Proof.
(* original proof tokens: 13 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_ptsto_cancel : forall V i (def : V) l, i < length l ->
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l).
Proof.
(* original proof tokens: 60 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_ptsto_cancel_pair : forall A B i (def : A * B) l,
  i < length l ->
  (arrayN_ex (@ptsto _ Peano_dec.eq_nat_dec (A * B)) l i * 
    i |-> (fst (selN l i def), snd (selN l i def)))%pred (list2nmem l).
Proof.
(* original proof tokens: 74 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_sel_for_eauto : forall V A i (v v' : V) l def,
  (A * i |-> v)%pred (list2nmem l)
  -> v' = selN l i def
  -> v' = v.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_combine' : forall A VP (pts : _ -> _ -> @pred _ _ VP) (a b : list A) start,
  arrayN pts start a * arrayN pts (start + length a) b <=p=> arrayN pts start (a ++ b).
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_combine : forall A VP (pts : _ -> _ -> @pred _ _ VP) (a b : list A) start off,
  off = start + length a ->
  arrayN pts start a * arrayN pts off b <=p=> arrayN pts start (a ++ b).
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_list2nmem : forall A (def : A) (a b : list A) F off,
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off a)%pred (list2nmem b) ->
  a = firstn (length a) (skipn off b).
Proof.
(* original proof tokens: 77 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_ptsto_end_eq : forall A (F : @pred _ _ A) l a a',
  (F * (length l) |-> a)%pred (list2nmem (l ++ a' :: nil)) ->
  a = a'.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_arrayN_end_eq : forall A (F : @pred _ _ A) l l' l'' (def:A),
  length l' = length l'' ->
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) (length l) l')%pred (list2nmem (l ++ l'')) ->
  l' = l''.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_off_arrayN: forall A (l : list A) off,
  arrayN (@ptsto _ Peano_dec.eq_nat_dec A) off l (list2nmem_off off l).
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

Theorem list2nmem_arrayN_app_iff : forall A (F : @pred _ _ A) l l',
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec A) (length l) l')%pred (list2nmem (l ++ l')) ->
  F (list2nmem l).
Proof.
(* original proof tokens: 102 *)

(* No more tactics to try *)
Admitted.

Lemma mem_except_list2nmem_oob : forall A (l : list A) a,
  a >= length l ->
  mem_except (list2nmem l) a = list2nmem l.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_sel_inb : forall A (l : list A) a def,
  a < length l ->
  list2nmem l a = Some (selN l a def).
Proof.
(* original proof tokens: 90 *)

(* No more tactics to try *)
Admitted.

Lemma sep_star_reorder_helper1 : forall AT AEQ V (a b c d : @pred AT AEQ V),
  (a * ((b * c) * d)) <=p=> (a * b * d) * c.
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_arrayN_updN : forall V F a vl l i (v : V),
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec V) a vl)%pred (list2nmem l) ->
  i < length vl ->
  (F * arrayN (@ptsto _ Peano_dec.eq_nat_dec V) a (updN vl i v))%pred (list2nmem (updN l (a + i) v)).
Proof.
(* original proof tokens: 117 *)

(* No more tactics to try *)
Admitted.

Lemma listmatch_ptsto_list2nmem_inbound : forall VT al vl (F : @pred _ _ VT) m ,
  (F * listmatch (fun a v => a |-> v) al vl)%pred (list2nmem m) ->
  Forall (fun a => a < length m) al.
Proof.
(* original proof tokens: 82 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_inj' : forall A (a b : list A) n,
  list2nmem_off n a = list2nmem_off n b ->
  a = b.
Proof.
(* original proof tokens: 206 *)

(* No more tactics to try *)
Admitted.

Lemma list2nmem_inj : forall A (a b : list A),
  list2nmem a = list2nmem b ->  a = b.
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Require Import PredCrash AsyncDisk.
Import ListNotations.
Lemma list2nmem_crash_xform : forall vl vsl (F : rawpred),
  possible_crash_list vsl vl ->
  F (list2nmem vsl) ->
  crash_xform F (list2nmem (synced_list vl)).
Proof.
(* original proof tokens: 495 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_list2nmem_possible_crash_list : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  exists vsl, F (list2nmem vsl) /\ possible_crash_list vsl (map fst vl).
Proof.
(* original proof tokens: 498 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_list2nmem_synced : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  map snd vl = repeat (@nil valu) (length vl).
Proof.
(* original proof tokens: 225 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_list2nmem_list_eq : forall F vsl vl,
  crash_xform F (list2nmem vsl) ->
  possible_crash_list vsl vl ->
  vsl = synced_list vl.
Proof.
(* original proof tokens: 151 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list2nmem_cons : forall l l' x y,
  possible_crash (list2nmem (x :: l)) (list2nmem (y :: l'))
  -> possible_crash (list2nmem l) (list2nmem l').
Proof.
(* original proof tokens: 113 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list2nmem_length : forall l l',
  possible_crash (list2nmem l) (list2nmem l')
  -> length l = length l'.
Proof.
(* original proof tokens: 104 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list2nmem_vssync : forall a d m,
  possible_crash (list2nmem (vssync d a)) m ->
  possible_crash (list2nmem d) m.
Proof.
(* original proof tokens: 74 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list2nmem_vssync_vecs : forall al d m,
  possible_crash (list2nmem (vssync_vecs d al)) m ->
  possible_crash (list2nmem d) m.
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_diskIs_vssync_vecs : forall al d,
  crash_xform (diskIs (list2nmem (vssync_vecs d al))) =p=>
  crash_xform (diskIs (list2nmem d)).
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma setlen_singleton : forall T l (v : T),
  setlen l 1 v = [ selN (setlen l 1 v) 0 v ].
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma setlen_singleton_ptsto : forall (l : list valuset),
  let l' := setlen l 1 ($0, nil) in
  (0 |-> selN l' 0 ($0, nil))%pred (list2nmem l').
Proof.
(* original proof tokens: 34 *)
firstorder.
(* No more tactics to try *)
Admitted.

Lemma ptsto_0_list2nmem_mem_eq : forall V v (d : list V),
  (0 |-> v)%pred (list2nmem d) -> d = [v].
Proof.
(* original proof tokens: 50 *)
simpl; intros; unfold list2nmem; destruct d; simpl in *; intuition.
intros; destruct H; simpl in *; intuition.
destruct H; simpl in *.
unfold list2nmem in *; simpl in *; intuition.
(* No more tactics to try *)
Admitted.

Lemma ptsto_a_list2nmem_a0 : forall V v (d : list V) a,
  (a |-> v)%pred (list2nmem d) -> a = 0.
Proof.
(* original proof tokens: 87 *)
unfold list2nmem in *; destruct d; simpl in *; intro H; inversion H.
destruct H.
auto.
intros.
(* No more tactics to try *)
Admitted.

Lemma ptsto_a_list2nmem_mem_eq : forall V v (d : list V) a,
  (a |-> v)%pred (list2nmem d) -> d = [v].
Proof.
(* original proof tokens: 44 *)
destruct d; simpl in *; intros; subst; auto.
destruct H.
simpl in H; destruct H; subst; auto.
(* No more tactics to try *)
Admitted.

Theorem arrayN_pimpl : forall V m (F : @pred addr addr_eq_dec V) l,
  F m ->
  arrayN (@ptsto _ _ _) 0 l m ->
  arrayN (@ptsto _ _ _) 0 l =p=> F.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma pred_except_ptsto_pimpl : forall V (l : list V) off v F,
  (F * off |-> v)%pred (list2nmem l) ->
  pred_except (arrayN (@ptsto _ _ _) 0 l) off v =p=> F.
Proof.
(* original proof tokens: 68 *)
eapply pred_except_ptsto_pimpl.
(* No more tactics to try *)
Admitted.

Lemma arrayN_notindomain_before : forall V (l : list V) start off,
  off < start ->
  arrayN (@ptsto _ _ V) start l =p=> notindomain off.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_notindomain_after : forall V (l : list V) start off,
  start + length l <= off ->
  arrayN (@ptsto _ _ V) start l =p=> notindomain off.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_ex_notindomain : forall V (l : list V) off,
  arrayN_ex (@ptsto _ _ V) l off ⇨⇨ notindomain off.
Proof.
(* original proof tokens: 56 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_ex_pred_except : forall V (l : list V) off def,
  off < length l ->
  arrayN_ex (@ptsto _ _ _) l off =p=>
  pred_except (arrayN (@ptsto _ _ _) 0 l) off (selN l off def).
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_ex_frame_pimpl : forall V (l : list V) off v F,
  (F * off |-> v)%pred (list2nmem l) ->
  arrayN_ex (@ptsto _ _ _) l off =p=> F.
Proof.
(* original proof tokens: 74 *)

(* No more tactics to try *)
Admitted.

