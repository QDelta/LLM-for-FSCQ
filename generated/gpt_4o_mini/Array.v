Require Import Mem.
Require Import ListUtils.
Require Import List Lia Ring Word Pred PredCrash.
Require Import Prog Hoare SepAuto BasicProg.
Require Import FunctionalExtensionality.
Require Import WordAuto.
Require Import AsyncDisk.
Import PeanoNat ListNotations.
Set Implicit Arguments.
Set Default Proof Using "Type".
Section GenArray.
Variable V VP : Type.
Variable pts : addr -> V -> @pred addr addr_eq_dec VP.
Infix "|-?->" := pts (at level 35) : pred_scope.
Fixpoint arrayN (a : addr) (vs : list V) : @pred _ addr_eq_dec _ :=
    match vs with
      | nil => emp
      | v :: vs' => a |-?-> v * arrayN (S a) vs'
    end%pred.
Lemma arrayN_unify : forall (a b : list V) s,
    a = b -> arrayN s a =p=> arrayN s b.
Proof.
(* original proof tokens: 14 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_one: forall v,
      0 |-?-> v <=p=> arrayN 0 [v].
Proof.
(* original proof tokens: 12 *)

(* No more tactics to try *)
Admitted.

Lemma isolateN_fwd' : forall vs i a (default : V),
    i < length vs
    -> arrayN a vs =p=> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
(* original proof tokens: 157 *)

(* No more tactics to try *)
Admitted.

Theorem isolateN_fwd : forall (default : V) a i vs,
    i < length vs
    -> arrayN a vs =p=> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Lemma isolateN_bwd' : forall vs i a (default : V),
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs)
    =p=> arrayN a vs.
Proof.
(* original proof tokens: 133 *)

(* No more tactics to try *)
Admitted.

Theorem isolateN_bwd : forall (default : V) a i vs,
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs)
    =p=> arrayN a vs.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_isolate : forall (default : V) a i vs,
    i < length vs
    -> arrayN a vs <=p=>
       arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Theorem isolate_fwd_upd : forall (v : V) a i vs,
    i < length vs
    -> arrayN a (updN vs i v) <=p=>
       arrayN a (firstn i vs)
       * (a + i) |-?-> v
       * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Theorem isolateN_bwd_upd : forall (v : V) a i vs,
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> v
       * arrayN (a + i + 1) (skipn (S i) vs)
       =p=> arrayN a (updN vs i v).
Proof.
(* original proof tokens: 85 *)
let a := fresh "a" in
let v := fresh "v" in
let vs := fresh "vs" in
let i := fresh "i" in
intros;
repeat match goal with
| [ H : i < length vs |- _ ] => 
    apply isolateN_bwd; auto
end.
(* No more tactics to try *)
Admitted.

Theorem arrayN_app : forall (a b : list V) st,
    arrayN st (a ++ b) <=p=>
    arrayN st a * arrayN (st + length a) b.
Proof.
(* original proof tokens: 99 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_split : forall i (a : list V) st,
    arrayN st a <=p=>
    arrayN st (firstn i a) * arrayN (st + i) (skipn i a).
Proof.
(* original proof tokens: 165 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_ptsto_selN_0 : forall l (def : V) a,
    length l = 1 ->
    arrayN a l <=p=> (a |-?-> selN l 0 def)%pred.
Proof.
(* original proof tokens: 48 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_isolate_hd : forall l (def : V) a,
    length l >= 1 ->
    arrayN a l <=p=> (a |-?-> selN l 0 def * arrayN (a + 1) (skipn 1 l) )%pred.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

End GenArray.
Section PtstoArray.
Variable V : Type.
Notation pts := (@ptsto addr addr_eq_dec V).
Lemma arrayN_oob': forall (l : list V) a i m,
    i >= length l
    -> arrayN pts a l m
    -> m (a + i) = None.
Proof.
(* original proof tokens: 150 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_oob: forall (l : list V) i m,
    i >= length l
    -> arrayN pts 0 l m
    -> m i = None.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_oob_lt: forall (l : list V) i a m,
    arrayN pts a l m ->
    i < a ->
    m i = None.
Proof.
(* original proof tokens: 78 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_updN_memupd : forall F l a i (v : V) m,
    (F * arrayN pts a l)%pred m ->
    i < length l ->
    (F * arrayN pts a (updN l i v))%pred (Mem.upd m (a + i) v).
Proof.
(* original proof tokens: 117 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_app_memupd : forall l (v : V) m,
    arrayN pts 0 l m
    -> arrayN pts 0 (l ++ v :: nil) (Mem.upd m (length l) v).
Proof.
(* original proof tokens: 114 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_list_eq : forall (vs1 vs2 : list V) s m,
    arrayN pts s vs1 m -> arrayN pts s vs2 m -> vs1 = vs2.
Proof.
(* original proof tokens: 118 *)

(* No more tactics to try *)
Admitted.

Theorem arrayN_strictly_exact : forall (vs : list V) base,
    strictly_exact (arrayN pts base vs).
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_selN : forall F a st l m (def : V),
    (F * arrayN pts st l)%pred m ->
    a >= st ->
    a < st + length l ->
    m a = Some (selN l (a - st) def).
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_selN_exis : forall F a st (l : list V) m,
    (F * arrayN pts st l)%pred m ->
    a >= st ->
    a < st + length l ->
    exists v, m a = Some v.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_unify' : forall a b s m (F1 F2 : pred), length a = length b ->
    (F1 * arrayN pts s a)%pred m -> (F2 * arrayN pts s b)%pred m -> a = b.
Proof.
(* original proof tokens: 238 *)

(* No more tactics to try *)
Admitted.

End PtstoArray.
Lemma arrayN_piff_replace: forall T V (l : list T) n (p q : _ -> _ -> @pred _ _ V),
  (forall i d x, i < length l -> selN l i d = x -> p (i + n) x <=p=> q (i + n) x) ->
  arrayN p n l <=p=> arrayN q n l.
Proof.
(* original proof tokens: 65 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_map: forall V T T' (l : list T) n (p : addr -> T' -> @pred _ _ V) (f : T -> T'),
  arrayN p n (map f l) <=p=> arrayN (fun i x => p i (f x)) n l.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Definition vsupd (vs : list valuset) (i : addr) (v : valu) : list valuset :=
  updN vs i (v, vsmerge (selN vs i ($0, nil))).
Definition vssync (vs : list valuset) (i : addr) : list valuset :=
  updN vs i (fst (selN vs i ($0, nil)), nil).
Definition vsupd_range (vsl : list valuset) (vl : list valu) :=
  let n := length vl in
  (List.combine vl (map vsmerge (firstn n vsl))) ++ skipn n vsl.
Definition vs_synced a (vl : list valuset) :=
  snd (selN vl a ($0, nil)) = nil.
Lemma vsupd_length : forall vsl a v,
  length (vsupd vsl a v) = length vsl.
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_length : forall vsl l,
  length l <= length vsl ->
  length (vsupd_range vsl l) = length vsl.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_nil : forall vsl,
  vsupd_range vsl nil = vsl.
Proof.
(* original proof tokens: 23 *)
(* generated proof tokens: 12 *)

simpl.  
 reflexivity.
Qed.

Lemma vsupd_range_progress : forall i vsl l,
  length l <= length vsl -> i < length l ->
    (vsupd (vsupd_range vsl (firstn i l)) i (selN l i $0))
  = (vsupd_range vsl ((firstn i l) ++ [ selN l i $0 ])).
Proof.
(* original proof tokens: 261 *)

(* No more tactics to try *)
Admitted.

Lemma forall_incl_refl : forall vs,
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs vs.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_incl : forall l vs,
  length l <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs (vsupd_range vs l).
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_selN_oob : forall vs n l,
  n >= length l ->
  length l <= length vs ->
  selN (vsupd_range vs l) n ($0, nil) = selN vs n ($0, nil).
Proof.
(* original proof tokens: 71 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_selN_inb : forall vs n l,
  n < length l ->
  length l <= length vs ->
  selN (vsupd_range vs l) n ($0, nil) = (selN l n $0, vsmerge (selN vs n ($0, nil))).
Proof.
(* original proof tokens: 84 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_firstn_incl : forall n l vs,
  length l <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) 
            (vsupd_range vs (firstn n l)) (vsupd_range vs l).
Proof.
(* original proof tokens: 157 *)

(* No more tactics to try *)
Admitted.

Definition vssync_range (vsl : list valuset) n :=
  (List.combine (map fst (firstn n vsl)) (repeat nil n)) ++ skipn n vsl.
Lemma vssync_range_length : forall vsl n,
  n <= length vsl ->
  length (vssync_range vsl n) = length vsl.
Proof.
(* original proof tokens: 67 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_range_progress : forall vs m,
  m < length vs ->
  vssync (vssync_range vs m) m = vssync_range vs (S m).
Proof.
(* original proof tokens: 229 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_range_incl : forall n vs,
  n <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) (vssync_range vs n) vs.
Proof.
(* original proof tokens: 194 *)

(* No more tactics to try *)
Admitted.

Definition vsupsyn_range (vsl : list valuset) (vl : list valu) :=
  let n := length vl in
  (List.combine vl (repeat nil n)) ++ skipn n vsl.
Lemma vsupsyn_range_length : forall vsl l,
  length l <= length vsl ->
  length (vsupsyn_range vsl l) = length vsl.
Proof.
(* original proof tokens: 46 *)

(* No more tactics to try *)
Admitted.

Lemma vsupsyn_range_selN : forall vsl vl i def,
  i < length vl ->
  selN (vsupsyn_range vsl vl) i (def, nil) = (selN vl i def, nil).
Proof.
(* original proof tokens: 56 *)

(* No more tactics to try *)
Admitted.

Lemma vsupsyn_range_selN_oob : forall vsl vl i def,
  i >= length vl ->
  selN (vsupsyn_range vsl vl) i def = selN vsl i def.
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_range_app_tl : forall l vs v,
  length l + 1 <= length vs ->
  vsupd_range vs (l ++ [v]) = vsupd (vsupd_range vs l) (length l) v.
Proof.
(* original proof tokens: 154 *)

(* No more tactics to try *)
Admitted.

Definition vsupd_vecs (vsl : list valuset) (l : list (addr * valu)) : list valuset :=
  fold_left (fun vs e => (vsupd vs (fst e) (snd e))) l vsl.
Lemma vsupd_vecs_length : forall l vs,
  length (vsupd_vecs vs l) = length vs.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_length_ok : forall l m def vs,
  Forall (fun e => fst e < length vs) l ->
  m < length l ->
  fst (selN l m def) < length (vsupd_vecs vs (firstn m l)).
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_progress : forall l m vs,
  m < length l ->
  let e := selN l m (0, $0) in
  vsupd (vsupd_vecs vs (firstn m l)) (fst e) (snd e) =
  vsupd_vecs vs (firstn (S m) l).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_comm : forall l a1 v1 a2 v2,
  a1 <> a2 ->
  vsupd (vsupd l a1 v1) a2 v2 = vsupd (vsupd l a2 v2) a1 v1.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_vsupd_notin : forall av l a v,
  ~ In a (map fst av) ->
  vsupd_vecs (vsupd l a v) av = vsupd (vsupd_vecs l av) a v.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_selN_not_in : forall l a d,
  ~ In a (map fst l) ->
  selN (vsupd_vecs d l) a ($0, nil) = selN d a ($0, nil).
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_app : forall d a b,
  vsupd_vecs d (a ++ b) = vsupd_vecs (vsupd_vecs d a) b.
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_cons : forall l a v avl,
  vsupd_vecs l ((a, v) :: avl) = vsupd_vecs (vsupd l a v) avl.
Proof.
(* original proof tokens: 8 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_selN_vsmerge_in' : forall a v avl l,
  In v (vsmerge (selN l a ($0, nil))) ->
  a < length l ->
  In v (vsmerge (selN (vsupd_vecs l avl) a ($0, nil))).
Proof.
(* original proof tokens: 264 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_selN_vsmerge_in : forall a v avl l,
  In v (vsmerge (selN l a ($0, nil))) ->
  In v (vsmerge (selN (vsupd_vecs l avl) a ($0, nil))).
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_incl : forall l vs,
  Forall (fun e => fst e < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs (vsupd_vecs vs l).
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma vsupd_vecs_firstn_incl : forall n l vs,
  Forall (fun e => fst e < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) 
            (vsupd_vecs vs (firstn n l)) (vsupd_vecs vs l).
Proof.
(* original proof tokens: 197 *)

(* No more tactics to try *)
Admitted.

Definition vssync_vecs (vsl : list valuset) (l : list addr) : list valuset :=
  fold_left vssync l vsl.
Definition vssync_vecs_rev (vsl : list valuset) (l : list addr) : list valuset :=
  fold_right (fun a m => vssync m a) vsl (rev l).
Theorem vssync_vecs_rev_eq : forall l vsl,
  vssync_vecs vsl l = vssync_vecs_rev vsl l.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_app : forall m l a,
  vssync_vecs m (l ++ [a]) = vssync (vssync_vecs m l) a.
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_length : forall l vs,
  length (vssync_vecs vs l) = length vs.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_length_ok : forall l m def vs,
  Forall (fun e => e < length vs) l ->
  m < length l ->
  selN l m def < length (vssync_vecs vs (firstn m l)).
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_progress : forall l m vs,
  m < length l ->
  vssync (vssync_vecs vs (firstn m l)) (selN l m 0) =
  vssync_vecs vs (firstn (S m) l).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_cons: forall a d x,
  vssync_vecs d (x :: a) = vssync_vecs (vssync d x) a.
Proof.
(* original proof tokens: 8 *)
simpl.
(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_vssync_comm : forall l d a,
  vssync_vecs (vssync d a) l = vssync (vssync_vecs d l) a.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_comm: forall l l' vs,
  vssync_vecs (vssync_vecs vs l) l' = vssync_vecs (vssync_vecs vs l') l.
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_app_comm: forall l l' vs,
  vssync_vecs vs (l ++ l') = vssync_vecs vs (l' ++ l).
Proof.
(* original proof tokens: 90 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_app': forall l l' vs,
  vssync_vecs (vssync_vecs vs l) l' = vssync_vecs vs (l ++ l').
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_synced : forall l a,
  vs_synced a l ->
  vssync l a = l.
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma vs_synced_vssync_nop: forall vs a,
  vs_synced a vs -> vssync vs a = vs.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_nop: forall vs l,
  Forall (fun a => vs_synced a vs) l ->
  vssync_vecs vs l = vs.
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_nil: forall vs,
  vssync_vecs vs nil = vs.
Proof.
(* original proof tokens: 20 *)
(* generated proof tokens: 10 *)

reflexivity.
Qed.

Lemma vssync_comm: forall vs a b,
  vssync (vssync vs a) b = vssync (vssync vs b) a.
Proof.
(* original proof tokens: 47 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vsupd_eq : forall l a v,
  vssync (vsupd l a v) a = updN l a (v, nil).
Proof.
(* original proof tokens: 78 *)

(* No more tactics to try *)
Admitted.

Lemma updN_vsupd_vecs_notin : forall av l a v,
  ~ In a (map fst av) ->
  updN (vsupd_vecs l av) a v = vsupd_vecs (updN l a v) av.
Proof.
(* original proof tokens: 59 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_selN_not_in : forall l i d,
  ~ In i l ->
  selN (vssync_vecs d l) i ($0, nil) = selN d i ($0, nil).
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_selN_In : forall l i d,
  In i l ->
  i < length d ->
  selN (vssync_vecs d l) i ($0, nil) = (fst (selN d i ($0, nil)), nil).
Proof.
(* original proof tokens: 148 *)

(* No more tactics to try *)
Admitted.

Lemma vssync_vecs_incl : forall l vs,
  Forall (fun a => a < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) (vssync_vecs vs l) vs.
Proof.
(* original proof tokens: 167 *)

(* No more tactics to try *)
Admitted.

Definition synced_list m: list valuset := List.combine m (repeat nil (length m)).
Definition possible_crash_list (l: list valuset) (l': list valu) :=
  length l = length l' /\
  forall i, i < length l -> In (selN l' i $0) (vsmerge (selN l i ($0, nil))).
Lemma synced_list_selN : forall l i def,
  selN (synced_list l) i (def, nil) = (selN l i def, nil).
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma synced_list_map_fst : forall l,
  map fst (synced_list l) = l.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma synced_list_map_fst_map : forall (vsl : list valuset),
  synced_list (map fst vsl) = map (fun x => (fst x, nil)) vsl.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma vsupsyn_range_synced_list : forall a b,
  length a = length b ->
  vsupsyn_range a b = synced_list b.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list_length : forall l l',
  possible_crash_list l l' -> length l = length l'.
Proof.
(* original proof tokens: 15 *)
(* generated proof tokens: 26 *)

intros l l' H.
destruct H as [Hlen _].
apply Hlen.
Qed.

Lemma synced_list_length : forall l,
  length (synced_list l) = length l.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Lemma synced_list_updN : forall l a v,
  updN (synced_list l) a (v, nil) = synced_list (updN l a v).
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Lemma synced_list_app : forall a b,
  synced_list (a ++ b) = synced_list a ++ synced_list b.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma synced_list_inj : forall a b, synced_list a = synced_list b -> a = b.
Proof.
(* original proof tokens: 83 *)

(* No more tactics to try *)
Admitted.

Lemma map_snd_synced_list_eq : forall a b,
  length a = length b ->
  map snd (synced_list a) = map snd (synced_list b).
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma map_snd_vsupd_vecs_not_in : forall l d a v,
  ~ In a (map fst l) ->
  NoDup (map fst l) ->
  map snd (vsupd_vecs (synced_list (updN d a v)) l) = map snd (vsupd_vecs (synced_list d) l).
Proof.
(* original proof tokens: 140 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list_updN : forall l l' a v vs,
  possible_crash_list l l' ->
  possible_crash_list (updN l a (v, vs)) (updN l' a v).
Proof.
(* original proof tokens: 64 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list_unique : forall a b,
  (forall n, snd (selN a n ($0, nil)) = nil) ->
  possible_crash_list a b ->
  b = map fst a.
Proof.
(* original proof tokens: 78 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list_synced_list_eq : forall a b,
  possible_crash_list (synced_list a) b -> a = b.
Proof.
(* original proof tokens: 117 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list_synced_list : forall l,
  possible_crash_list (synced_list l) l.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_list_cons : forall vsl vl v vs,
  possible_crash_list vsl vl ->
  In v (vsmerge vs) ->
  possible_crash_list (vs :: vsl) (v :: vl).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Theorem possible_crash_list_vssync : forall l l' a,
  possible_crash_list (vssync l a) l' ->
  possible_crash_list l l'.
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Section ArrayCrashXform.
Notation pts := (@ptsto addr addr_eq_dec valuset).
Lemma crash_xform_arrayN: forall l st,
    crash_xform (arrayN pts st l) =p=>
      exists l', [[ possible_crash_list l l' ]] *
      arrayN pts st (synced_list l').
Proof.
(* original proof tokens: 93 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_arrayN_r: forall l l' st,
    possible_crash_list l' l ->
    arrayN pts st (synced_list l) =p=> crash_xform (arrayN pts st l').
Proof.
(* original proof tokens: 149 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_synced_arrayN: forall l st,
    Forall (fun x => snd x = nil) l ->
    crash_xform (arrayN pts st l) =p=> arrayN pts st l.
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_arrayN_combine_nils: forall (l : list valu) st,
    crash_xform (arrayN pts st (List.combine l (repeat nil (length l)))) =p=>
    arrayN pts st (List.combine l (repeat nil (length l))).
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_arrayN_synced: forall (l : list valu) st,
    crash_xform (arrayN pts st (synced_list l)) =p=>
    arrayN pts st (List.combine l (repeat nil (length l))).
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

End ArrayCrashXform.
Section SubsetArray.
Theorem sync_invariant_arrayN_subset : forall vs a,
    sync_invariant (arrayN ptsto_subset a vs).
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_subset_oob': forall l a i m,
    i >= length l
    -> arrayN ptsto_subset a l m
    -> m (a + i) = None.
Proof.
(* original proof tokens: 192 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_subset_oob: forall l i m,
    i >= length l
    -> arrayN ptsto_subset 0 l m
    -> m i = None.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_selN_subset : forall F a st l m def,
    (F * arrayN ptsto_subset st l)%pred m ->
    a >= st ->
    a < st + length l ->
    let vs0 := (selN l (a - st) def) in
    exists vs, m a = Some vs /\ fst vs = fst vs0 /\ incl (snd vs) (snd vs0).
Proof.
(* original proof tokens: 96 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_subset_memupd : forall F l a i v vs vs' m,
    (F * arrayN ptsto_subset a l)%pred m ->
    incl vs' vs ->
    i < length l ->
    (F * arrayN ptsto_subset a (updN l i (v, vs)))%pred (Mem.upd m (a + i) (v, vs')).
Proof.
(* original proof tokens: 170 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_arrayN_subset: forall l st,
    crash_xform (arrayN ptsto_subset st l) =p=>
      exists l', [[ possible_crash_list l l' ]] *
      arrayN ptsto_subset st (synced_list l').
Proof.
(* original proof tokens: 110 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_arrayN_subset_r: forall l l' st,
    possible_crash_list l' l ->
    arrayN ptsto_subset st (synced_list l) =p=>
     crash_xform (arrayN ptsto_subset st l').
Proof.
(* original proof tokens: 160 *)

(* No more tactics to try *)
Admitted.

Hint Resolve incl_refl.
Lemma crash_xform_synced_arrayN_subset: forall l st,
    Forall (fun x => snd x = nil) l ->
    crash_xform (arrayN ptsto_subset st l) =p=> arrayN ptsto_subset st l.
Proof.
(* original proof tokens: 86 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_arrayN_subset_combine_nils: forall (l : list valu) st,
    crash_xform (arrayN ptsto_subset st (List.combine l (repeat nil (length l)))) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_arrayN_subset_synced: forall (l : list valu) st,
    crash_xform (arrayN ptsto_subset st (synced_list l)) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
Proof.
(* original proof tokens: 52 *)

(* No more tactics to try *)
Admitted.

End SubsetArray.
Hint Resolve sync_invariant_arrayN_subset.
Notation arrayS := (arrayN ptsto_subset).
Section ListUpd.
Variable V : Type.
Notation pts := (@ptsto addr addr_eq_dec V).
Fixpoint listupd (m : @mem _ addr_eq_dec V) base (vs : list V) :=
    match vs with
    | nil => m
    | v :: tl => listupd (upd m base v) (S base) tl
    end.
Lemma arrayN_listupd: forall l (m : @mem _ _ V) l0 base F,
    (F * arrayN pts base l0 )%pred m ->
    length l0 = length l ->
    (F * arrayN pts base l)%pred (listupd m base l).
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Lemma arrayN_listupd_eq : forall (l : list V) F st d,
    (F * arrayN pts st l)%pred d ->
    d = listupd d st l.
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Lemma listupd_sel_oob : forall (l : list V) a off m,
    a < off \/ a >= off + (length l) ->
    listupd m off l a = m a.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma listupd_sel_inb : forall (l : list V) a off m def,
    a >= off ->
    a < off + (length l) ->
    listupd m off l a = Some (selN l (a - off) def).
Proof.
(* original proof tokens: 84 *)

(* No more tactics to try *)
Admitted.

Lemma listupd_sel_cases : forall (l : list V) a off m def,
    ((a < off \/ a >= off + (length l)) /\ listupd m off l a = m a ) \/
    (a >= off /\ a < off + (length l) /\ listupd m off l a = Some (selN l (a - off) def) ).
Proof.
(* original proof tokens: 66 *)

(* No more tactics to try *)
Admitted.

End ListUpd.
Section ListUpdSubset.
Lemma arrayN_listupd_subset : forall l m l0 base F,
    (F * arrayN ptsto_subset base l0 )%pred m ->
    length l0 = length l ->
    (F * arrayN ptsto_subset base l)%pred (listupd m base l).
Proof.
(* original proof tokens: 98 *)

(* No more tactics to try *)
Admitted.

End ListUpdSubset.
