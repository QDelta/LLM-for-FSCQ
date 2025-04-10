Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classes.SetoidTactics.
Require Import FunctionalExtensionality.
Require Import Lia.
Require Import Eqdep_dec.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import Pred.
Require Import SepAuto.
Require Import GenSepN.
Require Import MapUtils.
Require Import FMapFacts.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Array.
Require Import DiskLogHash.
Require Import Word.
Require Import PredCrash.
Require Import Prog.
Import AddrMap.
Import ListNotations.
Definition valumap := Map.t valu.
Definition vmap0 := map0 valu.
Definition diskstate := list valuset.
Lemma map_empty_vmap0 : Map.Empty vmap0.
Proof.
(* skipped proof tokens: 12 *)
Admitted.
Module LogReplay.
Definition replay_mem (log : DLog.contents) init : valumap :=
    fold_left (fun m e => Map.add (fst e) (snd e) m) log init.
Definition replay_disk (log : DLog.contents) (m : diskstate) : diskstate:=
    fold_left (fun m' e => updN m' (fst e) (snd e, nil)) log m.
Definition map_merge (m1 m2 : valumap) :=
    replay_mem (Map.elements m2) m1.
Definition map_replay ms old cur : Prop :=
    cur = replay_disk (Map.elements ms) old.
Hint Resolve MapProperties.eqke_equiv.
Hint Resolve KNoDup_map_elements.
Lemma replay_disk_length : forall l m,
    length (replay_disk l m) = length m.
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Lemma replay_disk_updN_comm : forall l d a v,
    ~ In a (map fst l)
    -> replay_disk l (updN d a v) = updN (replay_disk l d) a v.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma replay_disk_selN_other : forall l d a def,
    ~ In a (map fst l)
    -> selN (replay_disk l d) a def = selN d a def.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma replay_disk_selN_In : forall l m a v def,
    In (a, v) l -> NoDup (map fst l) -> a < length m ->
    selN (replay_disk l m) a def = (v, nil).
Proof.
(* skipped proof tokens: 95 *)
Admitted.
Lemma replay_disk_selN_In_KNoDup : forall a v l m def,
    In (a, v) l -> KNoDup l -> a < length m ->
    selN (replay_disk l m) a def = (v, nil).
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Lemma replay_disk_selN_MapsTo : forall a v ms m def,
    Map.MapsTo a v ms -> a < length m ->
    selN (replay_disk (Map.elements ms) m) a def = (v, nil).
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Lemma replay_disk_selN_not_In : forall a ms m def,
    ~ Map.In a ms
    -> selN (replay_disk (Map.elements ms) m) a def = selN m a def.
Proof.
(* skipped proof tokens: 61 *)
Admitted.
Hint Rewrite replay_disk_length : lists.
Lemma replay_disk_add : forall a v ds m,
    replay_disk (Map.elements (Map.add a v ds)) m = updN (replay_disk (Map.elements ds) m) a (v, nil).
Proof.
(* skipped proof tokens: 233 *)
Admitted.
Lemma replay_disk_eq : forall a v v' ms d vs,
    Map.find a ms = Some v ->
    (exists F, F * a |-> (v', vs))%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    v = v'.
Proof.
(* skipped proof tokens: 93 *)
Admitted.
Lemma replay_disk_none_selN : forall a v ms d def,
    Map.find a ms = None ->
    (exists F, F * a |-> v)%pred
      (list2nmem (replay_disk (Map.elements ms) d)) ->
    selN d a def = v.
Proof.
(* skipped proof tokens: 59 *)
Admitted.
Lemma synced_data_replay_inb : forall a v c1 d,
    (exists F, F * a |-> v)%pred (list2nmem (replay_disk c1 d))
    -> a < length d.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma replay_disk_is_empty : forall d ms,
    Map.is_empty ms = true -> replay_disk (Map.elements ms) d = d.
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma replay_mem_map0 : forall m,
    Map.Equal (replay_mem (Map.elements m) vmap0) m.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Local Hint Resolve MapFacts.Equal_refl.
Lemma replay_mem_app' : forall l m,
    Map.Equal (replay_mem ((Map.elements m) ++ l) vmap0) (replay_mem l m).
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Lemma replay_mem_app : forall l2 l m,
    Map.Equal m (replay_mem l vmap0) ->
    Map.Equal (replay_mem (l ++ l2) vmap0) (replay_mem l2 m).
Proof.
(* skipped proof tokens: 56 *)
Admitted.
Lemma replay_mem_equal : forall l m1 m2,
    Map.Equal m1 m2 ->
    Map.Equal (replay_mem l m1) (replay_mem l m2).
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Instance replay_mem_proper :
    Proper (eq ==> Map.Equal ==> Map.Equal) replay_mem.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Lemma replay_mem_add : forall l k v m,
    ~ KIn (k, v) l -> KNoDup l ->
    Map.Equal (replay_mem l (Map.add k v m)) (Map.add k v (replay_mem l m)).
Proof.
(* skipped proof tokens: 83 *)
Admitted.
Lemma In_replay_mem_mem0 : forall l k,
    KNoDup l ->
    In k (map fst (Map.elements (replay_mem l vmap0))) ->
    In k (map fst l).
Proof.
(* skipped proof tokens: 106 *)
Admitted.
Lemma replay_disk_replay_mem0 : forall l d,
    KNoDup l ->
    replay_disk l d = replay_disk (Map.elements (elt:=valu) (replay_mem l vmap0)) d.
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Lemma replay_disk_merge' : forall l1 l2 d,
    KNoDup l1 -> KNoDup l2 ->
    replay_disk l2 (replay_disk l1 d) =
    replay_disk (Map.elements (replay_mem l2 (replay_mem l1 vmap0))) d.
Proof.
(* original proof tokens: 263 *)

(* No more tactics to try *)
Admitted.

Lemma replay_disk_merge : forall m1 m2 d,
    replay_disk (Map.elements m2) (replay_disk (Map.elements m1) d) =
    replay_disk (Map.elements (map_merge m1 m2)) d.
Proof.
(* skipped proof tokens: 80 *)
Admitted.
Lemma replay_mem_not_in' : forall l a v ms,
    KNoDup l ->
    ~ In a (map fst l) ->
    Map.MapsTo a v (replay_mem l ms) ->
    Map.MapsTo a v ms.
Proof.
(* skipped proof tokens: 73 *)
Admitted.
Lemma replay_mem_not_in : forall a v ms m,
    Map.MapsTo a v (replay_mem (Map.elements m) ms) ->
    ~ Map.In a m ->
    Map.MapsTo a v ms.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma map_merge_repeat' : forall l m,
    KNoDup l ->
    Map.Equal (replay_mem l (replay_mem l m)) (replay_mem l m).
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma map_merge_repeat : forall a b,
    Map.Equal (map_merge (map_merge a b) b) (map_merge a b).
Proof.
(* skipped proof tokens: 22 *)
Admitted.
Lemma map_merge_id: forall m,
    Map.Equal (map_merge m m) m.
Proof.
(* skipped proof tokens: 146 *)
Admitted.
Lemma replay_disk_updN_absorb : forall l a v d,
    In a (map fst l) -> KNoDup l ->
    replay_disk l (updN d a v) = replay_disk l d.
Proof.
(* skipped proof tokens: 89 *)
Admitted.
Lemma replay_disk_twice : forall l d,
    KNoDup l ->
    replay_disk l (replay_disk l d) = replay_disk l d.
Proof.
(* skipped proof tokens: 69 *)
Admitted.
Lemma replay_disk_eq_length_eq : forall l l' a b,
    replay_disk l a = replay_disk l' b ->
    length a = length b.
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Lemma ptsto_replay_disk_not_in' : forall l F a v d,
    ~ In a (map fst l) ->
    KNoDup l ->
    (F * a |-> v)%pred (list2nmem (replay_disk l d)) ->
    ((arrayN_ex (@ptsto _ addr_eq_dec valuset) d a) * a |-> v)%pred (list2nmem d).
Proof.
(* skipped proof tokens: 175 *)
Admitted.
Lemma ptsto_replay_disk_not_in : forall F a v d m,
    ~ Map.In a m ->
    (F * a |-> v)%pred (list2nmem (replay_disk (Map.elements m) d)) ->
    ((arrayN_ex (@ptsto _ addr_eq_dec valuset) d a) * a |-> v)%pred (list2nmem d).
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Lemma replay_disk_updN_eq_not_in : forall Fd a v vs d ms,
    ~ Map.In a ms ->
    (Fd * a |-> vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    updN (replay_disk (Map.elements ms) d) a (v, (vsmerge vs)) =
      replay_disk (Map.elements ms) (vsupd d a v).
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Lemma replay_disk_updN_eq_empty : forall Fd a v vs d ms,
    Map.Empty ms ->
    (Fd * a |-> vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    updN (replay_disk (Map.elements ms) d) a (v, (vsmerge vs)) =
      replay_disk (Map.elements ms) (vsupd d a v).
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma replay_disk_selN_snd_nil : forall l a d,
    In a (map fst l) ->
    snd (selN (replay_disk l d) a ($0, nil)) = nil.
Proof.
(* skipped proof tokens: 110 *)
Admitted.
Lemma replay_disk_vssync_comm_list : forall l d a,
    vssync (replay_disk l d) a =
    replay_disk l (vssync d a).
Proof.
(* skipped proof tokens: 117 *)
Admitted.
Lemma replay_disk_vssync_vecs_comm_list : forall l ents d,
    vssync_vecs (replay_disk ents d) l =
    replay_disk ents (vssync_vecs d l).
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma replay_disk_vssync_comm : forall m d a,
    vssync (replay_disk (Map.elements m) d) a =
    replay_disk (Map.elements m) (vssync d a).
Proof.
(* skipped proof tokens: 19 *)
Admitted.
Lemma replay_disk_vssync_vecs_comm : forall l m d,
    vssync_vecs (replay_disk (Map.elements m) d) l =
    replay_disk (Map.elements m) (vssync_vecs d l).
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma replay_disk_empty : forall m d,
    Map.Empty m ->
    replay_disk (Map.elements m) d = d.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Lemma replay_disk_remove_updN_eq : forall F m d a v,
    (F * a |-> v)%pred (list2nmem (replay_disk (Map.elements m) d)) ->
    replay_disk (Map.elements m) d =
    replay_disk (Map.elements (Map.remove a m)) (updN d a v).
Proof.
(* skipped proof tokens: 223 *)
Admitted.
Lemma list2nmem_replay_disk_remove_updN_ptsto : forall F a vs vs' d ms,
    (F * a |-> vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    (F * a |-> vs')%pred
      (list2nmem (replay_disk (Map.elements (Map.remove a ms)) (updN d a vs'))).
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Set Regular Subst Tactic.
Lemma updN_replay_disk_remove_eq : forall m d a v,
    d = replay_disk (Map.elements m) d ->
    updN d a v = replay_disk (Map.elements (Map.remove a m)) (updN d a v).
Proof.
(* skipped proof tokens: 217 *)
Admitted.
Lemma replay_mem_add_find_none : forall l a v m,
    ~ Map.find a (replay_mem l (Map.add a v m)) = None.
Proof.
(* original proof tokens: 69 *)

(* No more tactics to try *)
Admitted.

Lemma map_find_replay_mem_not_in : forall a l m,
    Map.find a (replay_mem l m) = None ->
    ~ In a (map fst l).
Proof.
(* skipped proof tokens: 50 *)
Admitted.
Lemma replay_mem_find_none_mono : forall l a m,
    Map.find a (replay_mem l m) = None ->
    Map.find a m = None.
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Definition ents_remove a (ents : DLog.contents) := 
    filter (fun e => if (addr_eq_dec (fst e) a) then false else true) ents.
Lemma ents_remove_not_in : forall ents a,
    ~ In a (map fst (ents_remove a ents)).
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Local Hint Resolve ents_remove_not_in.
Lemma replay_disk_ents_remove_updN : forall ents d a v,
    updN (replay_disk (ents_remove a ents) d) a v =  updN (replay_disk ents d) a v.
Proof.
(* skipped proof tokens: 78 *)
Admitted.
Definition ents_remove_list (al : list addr) (ents: DLog.contents) := 
    filter (fun e => if (In_dec addr_eq_dec (fst e) al) then false else true) ents.
Definition map_valid (ms : valumap) (m : diskstate) :=
     forall a v, Map.MapsTo a v ms -> a <> 0 /\ a < length m.
Definition log_valid (ents : DLog.contents) (m : diskstate) :=
     KNoDup ents /\ forall a v, KIn (a, v) ents -> a <> 0 /\ a < length m.
Lemma map_valid_map0 : forall m,
    map_valid vmap0 m.
Proof.
(* skipped proof tokens: 35 *)
Admitted.
Lemma map_valid_empty : forall l m,
    Map.Empty m -> map_valid m l.
Proof.
(* skipped proof tokens: 41 *)
Admitted.
Lemma map_valid_add : forall d a v ms,
    map_valid ms d ->
    a < length d -> a <> 0 ->
    map_valid (Map.add a v ms) d.
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Lemma map_valid_updN : forall m d a v,
    map_valid m d -> map_valid m (updN d a v).
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma map_valid_remove : forall a ms d1 d2,
    map_valid ms d1 ->
    length d1 = length d2 ->
    map_valid (Map.remove a ms) d2.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma map_valid_equal : forall d m1 m2,
    Map.Equal m1 m2 -> map_valid m1 d -> map_valid m2 d.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Lemma length_eq_map_valid : forall m a b,
    map_valid m a -> length b = length a -> map_valid m b.
Proof.
(* skipped proof tokens: 41 *)
Admitted.
Lemma map_valid_vsupd_vecs : forall l d m,
    map_valid m d ->
    map_valid m (vsupd_vecs d l).
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Lemma map_valid_vssync_vecs : forall l d m,
    map_valid m d ->
    map_valid m (vssync_vecs d l).
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Lemma map_valid_Forall_fst_synced : forall d ms,
    map_valid ms d ->
    Forall (fun e => fst e < length d) (Map.elements ms).
Proof.
(* skipped proof tokens: 57 *)
Admitted.
Hint Resolve map_valid_Forall_fst_synced.
Lemma map_valid_Forall_synced_map_fst : forall d ms,
    map_valid ms d ->
    Forall (fun e => e < length d) (map fst (Map.elements ms)).
Proof.
(* skipped proof tokens: 75 *)
Admitted.
Lemma map_valid_replay : forall d ms1 ms2,
    map_valid ms1 d ->
    map_valid ms2 d ->
    map_valid ms1 (replay_disk (Map.elements ms2) d).
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma map_valid_replay_mem : forall d ms1 ms2,
    map_valid ms1 d ->
    map_valid ms2 d ->
    map_valid (replay_mem (Map.elements ms1) ms2) d.
Proof.
(* skipped proof tokens: 88 *)
Admitted.
Lemma map_valid_replay_disk : forall l m d,
    map_valid m d ->
    map_valid m (replay_disk l d).
Proof.
(* skipped proof tokens: 55 *)
Admitted.
Lemma log_valid_nodup : forall l d,
    log_valid l d -> KNoDup l.
Proof.
(* skipped proof tokens: 14 *)
Admitted.
Lemma map_valid_log_valid : forall ms d,
    map_valid ms d ->
    log_valid (Map.elements ms) d.
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Lemma log_valid_entries_valid : forall ents d l raw,
    goodSize addrlen (length raw) ->
    d = replay_disk l raw ->
    log_valid ents d -> DLog.entries_valid ents.
Proof.
(* skipped proof tokens: 132 *)
Admitted.
Lemma log_vaild_filter : forall ents d f,
    log_valid ents d ->
    log_valid (filter f ents) d.
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Local Hint Resolve Map.is_empty_1 Map.is_empty_2.
Lemma map_valid_replay_mem' : forall ents d ms,
    log_valid ents d ->
    map_valid ms d ->
    map_valid (replay_mem ents ms) d.
Proof.
(* skipped proof tokens: 84 *)
Admitted.
Lemma log_valid_replay : forall ents d ms,
    map_valid ms d ->
    log_valid ents (replay_disk (Map.elements ms) d) ->
    log_valid ents d.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Lemma log_valid_length_eq : forall ents d d',
    log_valid ents d ->
    length d = length d' ->
    log_valid ents d'.
Proof.
(* skipped proof tokens: 39 *)
Admitted.
Lemma replay_disk_replay_mem : forall l m d,
    log_valid l (replay_disk (Map.elements m) d) ->
    replay_disk l (replay_disk (Map.elements m) d) =
    replay_disk (Map.elements (replay_mem l m)) d.
Proof.
(* skipped proof tokens: 118 *)
Admitted.
Instance map_valid_iff_proper :
    Proper (Map.Equal ==> eq ==> iff) map_valid.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Instance map_valid_impl_proper :
    Proper (Map.Equal ==> eq ==> Basics.impl) map_valid.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Instance map_valid_impl_proper2 :
    Proper (Map.Equal ==> eq ==> flip Basics.impl) map_valid.
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma possible_crash_log_valid : forall l l' ents,
    possible_crash (list2nmem l) (list2nmem l')
    -> log_valid ents l'
    -> log_valid ents l.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Lemma possible_crash_replay_disk : forall ents d d',
    log_valid ents d'
    -> possible_crash (list2nmem d)
           (list2nmem d')
    -> possible_crash (list2nmem (replay_disk ents d))
      (list2nmem (replay_disk ents d')).
Proof.
(* skipped proof tokens: 227 *)
Admitted.
Lemma crash_xform_replay_disk : forall ents d d',
    log_valid ents d'
    -> crash_xform (diskIs (list2nmem d))
     (list2nmem d')
    -> crash_xform (diskIs (list2nmem (replay_disk ents d)))
     (list2nmem (replay_disk ents d')).
Proof.
(* skipped proof tokens: 67 *)
Admitted.
Lemma replay_disk_vsupd_vecs : forall l d,
    KNoDup l
    -> replay_disk l d = replay_disk l (vsupd_vecs d l).
Proof.
(* original proof tokens: 150 *)

(* No more tactics to try *)
Admitted.

Set Implicit Arguments.
Fixpoint overlap V (l : list addr) (m : Map.t V) : bool :=
  match l with
  | nil => false
  | a :: rest => if (Map.mem a m) then true else overlap rest m
  end.
Lemma overlap_firstn_overlap : forall V n l (m : Map.t V),
    overlap (firstn n l) m = true ->
    overlap l m = true.
Proof.
(* skipped proof tokens: 67 *)
Admitted.
Lemma In_MapIn_overlap : forall V l a (ms : Map.t V),
    In a l ->
    Map.In a ms ->
    overlap l ms = true.
Proof.
(* skipped proof tokens: 81 *)
Admitted.
Lemma overlap_empty : forall V al (m : Map.t V),
    Map.Empty m ->
    overlap al m = false.
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Lemma replay_disk_vsupd_vecs_nonoverlap : forall l m d,
    overlap (map fst l) m = false ->
    vsupd_vecs (replay_disk (Map.elements m) d) l =
    replay_disk (Map.elements m) (vsupd_vecs d l).
Proof.
(* skipped proof tokens: 123 *)
Admitted.
Lemma overlap_equal : forall T l (m1 m2 : Map.t T),
    Map.Equal m1 m2 ->
    overlap l m1 = overlap l m2.
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Instance overlap_proper : forall T,
    Proper (eq ==> Map.Equal ==> eq) (@overlap T).
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Lemma nonoverlap_replay_mem_disjoint : forall al ents d,
    overlap al (replay_mem ents d) = false ->
    disjoint al (map fst ents).
Proof.
(* skipped proof tokens: 110 *)
Admitted.
Lemma replay_mem_nonoverlap_mono : forall al ents m,
    overlap al (replay_mem ents m) = false ->
    overlap al m = false.
Proof.
(* skipped proof tokens: 127 *)
Admitted.
Lemma replay_disk_vsupd_vecs_disjoint : forall l ents d,
    disjoint (map fst l) (map fst ents) ->
    vsupd_vecs (replay_disk ents d) l =
    replay_disk ents (vsupd_vecs d l).
Proof.
(* skipped proof tokens: 98 *)
Admitted.
Lemma replay_disk_vssync_vecs_disjoint : forall l ents d,
    disjoint l (map fst ents) ->
    vssync_vecs (replay_disk ents d) l =
    replay_disk ents (vssync_vecs d l).
Proof.
(* skipped proof tokens: 94 *)
Admitted.
End LogReplay.
