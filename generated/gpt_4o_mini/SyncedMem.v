Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Lia.
Require Import List.
Require Import Pred.
Require Import Mem.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import Array.
Require Import ListUtils.
Require Import LogReplay.
Require Import GenSepN.
Require Import ListPred.
Import ListNotations.
Definition syncedmem := @Mem.mem _ addr_eq_dec bool.
Definition sm_vs_valid (sm : @Mem.mem _ addr_eq_dec _) vs :=
  forall a, a < length vs -> sm a <> None /\ (sm a = Some true -> vs_synced a vs).
Definition sm_ds_valid (sm : @Mem.mem _ addr_eq_dec _) ds :=
  Forall (sm_vs_valid sm) (fst ds :: snd ds).
Lemma sm_ds_valid_pushd_iff: forall sm ds d,
  sm_ds_valid sm ds /\ sm_vs_valid sm d <-> sm_ds_valid sm (pushd d ds).
Proof.
(* original proof tokens: 93 *)
destruct ds as [ds_fst ds_snd]. split; intros; [| split].
destruct H as [H1 H2].
(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_pushd: forall sm ds d,
  sm_vs_valid sm d ->
  sm_ds_valid sm ds -> sm_ds_valid sm (pushd d ds).
Proof.
(* original proof tokens: 21 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_pushd_r: forall sm ds d,
  sm_ds_valid sm (pushd d ds) ->
  sm_ds_valid sm ds.
Proof.
(* original proof tokens: 24 *)
simpl. unfold sm_ds_valid, pushd. intuition.
apply Forall_cons.
destruct ds as [hd tl].
simpl in *.
apply Forall_inv in H.
apply H.
destruct ds as [hd tl]. simpl in *; clear H.
destruct (tl) as [|hd' tl']; [constructor |].
destruct tl' as [|hd'' tl''].
apply Forall_cons.
repeat constructor.
destruct H.
(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_pushd_l: forall sm ds d,
  sm_ds_valid sm (pushd d ds) ->
  sm_vs_valid sm d.
Proof.
(* original proof tokens: 24 *)
destruct ds.
(* No more tactics to try *)
Admitted.

Lemma vs_synced_updN_synced: forall a d i v,
  vs_synced a d ->
  vs_synced a (updN d i (v, nil)).
Proof.
(* original proof tokens: 72 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_upd_unsynced: forall sm d a v,
  sm_vs_valid sm d ->
  sm_vs_valid (Mem.upd sm a false) (updN d a v).
Proof.
(* original proof tokens: 90 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_upd_synced: forall sm i d v,
  sm_vs_valid sm d ->
  sm_vs_valid (Mem.upd sm i true) (updN d i (v, nil)).
Proof.
(* original proof tokens: 98 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_same_upd_synced: forall sm i d v,
  sm_vs_valid sm d ->
  sm_vs_valid sm (updN d i (v, nil)).
Proof.
(* original proof tokens: 92 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_vssync': forall sm vs a,
  sm_vs_valid sm vs -> sm_vs_valid sm (vssync vs a).
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_vs_synced: forall sm vs a,
  sm_vs_valid sm vs -> sm a = Some true ->
  vs_synced a vs.
Proof.
(* original proof tokens: 54 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_dsupd: forall sm ds a v,
  a < length (ds!!) ->
  sm_ds_valid sm ds ->
  sm_ds_valid (Mem.upd sm a false) (dsupd ds a v).
Proof.
(* original proof tokens: 93 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_latest: forall sm ds,
  sm_ds_valid sm ds ->
  sm_vs_valid sm ds!!.
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_synced: forall sm d,
  sm_vs_valid sm d ->
  sm_ds_valid sm (d, nil).
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_dssync: forall sm ds a,
  sm_ds_valid sm ds ->
  sm_ds_valid (Mem.upd sm a true) (dssync ds a).
Proof.
(* original proof tokens: 113 *)
unfold sm_ds_valid, dssync.
(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_dssync': forall sm ds a,
  sm_ds_valid sm ds -> sm_ds_valid sm (dssync ds a).
Proof.
(* original proof tokens: 75 *)
unfold sm_ds_valid, dssync; intros; simpl in *; auto.
apply Forall_map.
apply Forall_map.
apply Forall_map.
apply Forall_map.
simpl.
destruct ds as [fst_ds snd_ds].
simpl.
apply Forall_map.
apply Forall_map.
destruct H as [H1 | H2].
apply Forall_map.
(* Reached max number of model calls *)
Admitted.

Lemma sm_ds_valid_dssync_vecs': forall sm ds al,
  sm_ds_valid sm ds -> sm_ds_valid sm (dssync_vecs ds al).
Proof.
(* original proof tokens: 62 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_ds_synced: forall sm ds a,
  sm_ds_valid sm ds -> sm a = Some true ->
  ds_synced a ds.
Proof.
(* original proof tokens: 51 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_pushd_latest: forall sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid sm (pushd ds!! ds).
Proof.
(* original proof tokens: 22 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_d_in: forall sm ds d,
  sm_ds_valid sm ds ->
  d_in d ds ->
  sm_vs_valid sm d.
Proof.
(* original proof tokens: 42 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_nthd: forall n sm ds,
  sm_ds_valid sm ds ->
  sm_vs_valid sm (nthd n ds).
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_all_synced: forall sm d d',
  sm_vs_valid sm d ->
  length d = length d' ->
  Forall (fun v => snd v = []) d' ->
  sm_vs_valid sm d'.
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Definition sm_disk_exact (d : diskstate) :=
  list2nmem (map (fun v => match (snd v) with [] => true | _ => false end) d).
Lemma sm_vs_valid_disk_exact: forall d,
  sm_vs_valid (sm_disk_exact d) d.
Proof.
(* original proof tokens: 88 *)

(* No more tactics to try *)
Admitted.

Definition sm_unsynced : syncedmem := fun _ => Some false.
Definition sm_synced : syncedmem := fun _ => Some true.
Definition sm_sync_all (sm : syncedmem) : syncedmem := fun a =>
  match sm a with
  | None => None
  | Some _ => Some true
  end.
Definition sm_sync_invariant (p : pred) : Prop := forall sm, p sm -> p (sm_sync_all sm).
Lemma sm_vs_valid_sm_unsynced: forall d,
  sm_vs_valid sm_unsynced d.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Local Hint Resolve sm_vs_valid_sm_unsynced.
Lemma sm_ds_valid_sm_unsynced: forall ds,
  sm_ds_valid sm_unsynced ds.
Proof.
(* original proof tokens: 26 *)

(* No more tactics to try *)
Admitted.

Definition sm_set_vecs (b : bool) (sm : syncedmem) (a : list addr) :=
  fold_left (fun sm a => @Mem.upd _ _ addr_eq_dec sm a b) a sm.
Definition sm_upd_vecs sm (a : list (_ * valu)) := sm_set_vecs false sm (map fst a).
Definition sm_sync_vecs := sm_set_vecs true.
Lemma sm_set_vecs_cons: forall a sm x b,
  sm_set_vecs b sm (x :: a) = Mem.upd (sm_set_vecs b sm a) x b.
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Lemma sm_set_vecs_cons_inside: forall a sm x b,
  sm_set_vecs b sm (x :: a) = sm_set_vecs b (Mem.upd sm x b) a.
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Lemma sm_upd_vecs_cons: forall a sm x,
  sm_upd_vecs sm (x :: a) = Mem.upd (sm_upd_vecs sm a) (fst x) false.
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_vecs_cons: forall a sm x,
  sm_sync_vecs sm (x :: a) = Mem.upd (sm_sync_vecs sm a) x true.
Proof.
(* original proof tokens: 15 *)

(* No more tactics to try *)
Admitted.

Lemma sm_upd_vecs_cons_inside: forall a sm x,
  sm_upd_vecs sm (x :: a) = sm_upd_vecs (Mem.upd sm (fst x) false) a.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_vecs_cons_inside: forall a sm x,
  sm_sync_vecs sm (x :: a) = sm_sync_vecs (Mem.upd sm x true) a.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_vsupd_vecs: forall a sm v,
  sm_vs_valid sm v ->
  sm_vs_valid (sm_upd_vecs sm a) (vsupd_vecs v a).
Proof.
(* original proof tokens: 59 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_vssync_vecs: forall a sm v,
  sm_vs_valid sm v ->
  sm_vs_valid (sm_sync_vecs sm a) (vssync_vecs v a).
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Lemma sm_vs_valid_ds_valid: forall sm ds,
  Forall (sm_vs_valid sm) (fst ds :: snd ds) ->
  sm_ds_valid sm ds.
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_dsupd_vecs: forall a sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid (sm_upd_vecs sm a) (dsupd_vecs ds a).
Proof.
(* original proof tokens: 108 *)

(* No more tactics to try *)
Admitted.

Lemma sm_ds_valid_dssync_vecs: forall a sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid (sm_sync_vecs sm a) (dssync_vecs ds a).
Proof.
(* original proof tokens: 109 *)
unfold sm_ds_valid, sm_sync_vecs, dssync_vecs.
(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_mem_union: forall AEQ m1 m2,
  @mem_union _ AEQ _ (sm_sync_all m1) (sm_sync_all m2) = sm_sync_all (mem_union m1 m2).
Proof.
(* original proof tokens: 37 *)
unfold sm_sync_all, mem_union.
(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_mem_disjoint: forall m1 m2 AEQ,
  mem_disjoint m1 m2 -> @mem_disjoint _ AEQ _ (sm_sync_all m1) (sm_sync_all m2).
Proof.
(* original proof tokens: 47 *)
unfold sm_sync_all, mem_disjoint.
(* No more tactics to try *)
Admitted.

Lemma sm_sync_invariant_sep_star: forall (p q : pred),
  sm_sync_invariant p -> sm_sync_invariant q ->
  sm_sync_invariant (p * q).
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_sep_star_swap: forall AEQ (p p' q q' : @pred _ AEQ _) sm,
  (p * q)%pred sm ->
  (forall m, p m -> p' (sm_sync_all m)) ->
  (forall m, q m -> q' (sm_sync_all m)) ->
  (p' * q')%pred (sm_sync_all sm).
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_sep_star_swap_l: forall (p p' q : pred) sm,
  (p * q)%pred sm ->
  (forall m, p m -> p' (sm_sync_all m)) ->
  sm_sync_invariant q ->
  (p' * q)%pred (sm_sync_all sm).
Proof.
(* original proof tokens: 16 *)
unfold_sep_star.
(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_sep_star_swap_r: forall (p q q' : pred) sm,
  (p * q)%pred sm ->
  (forall m, q m -> q' (sm_sync_all m)) ->
  sm_sync_invariant p ->
  (p * q')%pred (sm_sync_all sm).
Proof.
(* original proof tokens: 16 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_invariant_lift_empty: forall P,
  sm_sync_invariant (lift_empty P).
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_ptsto: forall AEQ a b (m : syncedmem),
  (@ptsto _ AEQ _ a b)%pred m ->
  (@ptsto _ AEQ _ a true)%pred (sm_sync_all m).
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_invariant_exis_ptsto: forall a,
  sm_sync_invariant (a |->?)%pred.
Proof.
(* original proof tokens: 56 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_invariant_emp:
  sm_sync_invariant emp.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_invariant_listpred: forall T prd (l : list T),
  (forall x, In x l -> sm_sync_invariant (prd x)) ->
  sm_sync_invariant (listpred prd l).
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_listpred_swap: forall T AEQ (prd prd' : T -> @pred _ AEQ _) (l : list T) sm,
  (forall sm x, In x l -> prd x sm -> prd' x (sm_sync_all sm)) ->
  listpred prd l sm ->
  listpred prd' l (sm_sync_all sm).
Proof.
(* original proof tokens: 37 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_arrayN_swap: forall T AEQ (prd prd' : nat -> T -> @pred _ AEQ _) d (l : list T) i sm,
  (forall sm  i' x, i' < length l -> selN l i' d = x -> prd (i + i') x sm -> prd' (i + i') x (sm_sync_all sm)) ->
  arrayN prd i l sm ->
  arrayN prd' i l (sm_sync_all sm).
Proof.
(* original proof tokens: 100 *)

(* No more tactics to try *)
Admitted.

Lemma sm_sync_invariant_piff: forall (p q : pred),
  piff p q -> sm_sync_invariant p <-> sm_sync_invariant q.
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Hint Resolve sm_sync_invariant_sep_star.
Hint Resolve sm_sync_invariant_exis_ptsto.
Hint Resolve sm_sync_invariant_emp.
Hint Resolve sm_sync_invariant_lift_empty.
Hint Resolve sm_sync_invariant_listpred.
Hint Resolve sm_sync_all_ptsto.
Definition mem_except_mem {AT AEQ V} (m ex : @Mem.mem AT AEQ V) : @Mem.mem AT AEQ V := fun a =>
  match ex a with
  | Some _ => None
  | None => m a
  end.
Lemma mem_except_mem_disjoint: forall AT AEQ V (m ex : @Mem.mem AT AEQ V),
  mem_disjoint (mem_except_mem m ex) ex.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Lemma mem_except_mem_union: forall AT AEQ V (m ex : @Mem.mem AT AEQ V),
  mem_union (mem_except_mem m ex) ex = (mem_union ex m).
Proof.
(* original proof tokens: 40 *)
unfold mem_except_mem, mem_union.
(* No more tactics to try *)
Admitted.

Lemma sm_sync_all_mem_union_sm_synced: forall m m1 m2,
  sm_sync_all m = mem_union m1 m2 ->
  mem_disjoint m1 m2 ->
  sm_synced = mem_union m2 sm_synced.
Proof.
(* original proof tokens: 110 *)
unfold sm_sync_all, sm_synced.
simpl. intros; subst. rewrite mem_union_comm. reflexivity.
destruct H0.
(* No more tactics to try *)
Admitted.

Lemma sm_synced_sep_star_l: forall AEQ (p q : @pred _ AEQ _) m,
  (p * q)%pred (sm_sync_all m) ->
  (any * q)%pred sm_synced.
Proof.
(* original proof tokens: 62 *)
unfold_sep_star.
(* No more tactics to try *)
Admitted.

Lemma sm_synced_sep_star_r: forall AEQ (p q : @pred _ AEQ _) m,
  (p * q)%pred (sm_sync_all m) ->
  (p * any)%pred sm_synced.
Proof.
(* original proof tokens: 33 *)
unfold_sep_star.
destruct 1 as (m1 & m2 & Hsync & Hdisj & Hp & Hq).
destruct Hsync as [Hsync1 Hsync2].
(* No more tactics to try *)
Admitted.

