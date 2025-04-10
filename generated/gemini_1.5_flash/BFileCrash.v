Require Import BFile.
Require Import SepAuto.
Require Import Pred.
Require Import Array.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.
Require Import Morphisms.
Require Import GenSepN.
Require Import Arith.
Require Import Lia.
Require Import List.
Require Import ListUtils.
Import BFILE.
Theorem file_crash_trans : forall f1 f2 f3,
  file_crash f1 f2 ->
  file_crash f2 f3 ->
  file_crash f1 f3.
Proof.
(* original proof tokens: 41 *)
intros.
destruct H as [vs0 H1].
destruct H0 as [vs1 H2].
(* No more tactics to try *)
Admitted.

Definition possible_fmem_crash (m m' : @Mem.mem addr addr_eq_dec BFILE.bfile) :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists f f', m a = Some f /\ m' a = Some f' /\ file_crash f f').
Definition flist_crash_xform (p : @pred addr addr_eq_dec BFILE.bfile) : @pred addr addr_eq_dec BFILE.bfile :=
  fun mf => exists mf', p mf' /\ possible_fmem_crash mf' mf.
Theorem possible_fmem_crash_mem_union : forall ma mb m', possible_fmem_crash (mem_union ma mb) m'
  -> @mem_disjoint _ addr_eq_dec _ ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_fmem_crash ma ma' /\ possible_fmem_crash mb mb'.
Proof.
(* original proof tokens: 396 *)
intros ma mb m' Hpfmc Hdmj.
eexists.
eexists.
apply conj.
(* No more tactics to try *)
Admitted.

Theorem possible_fmem_crash_disjoint : forall ma mb ma' mb',
  @mem_disjoint _ addr_eq_dec _ ma' mb'
  -> possible_fmem_crash ma ma'
  -> possible_fmem_crash mb mb'
  -> @mem_disjoint _ addr_eq_dec _ ma mb.
Proof.
(* original proof tokens: 67 *)
intros.
unfold mem_disjoint in *.
intros Hcontra.
destruct Hcontra.
destruct H2.
(* No more tactics to try *)
Admitted.

Theorem possible_fmem_crash_union : forall ma mb ma' mb', possible_fmem_crash ma ma'
  -> possible_fmem_crash mb mb'
  -> possible_fmem_crash (mem_union ma mb) (mem_union ma' mb').
Proof.
(* original proof tokens: 180 *)
intros.
unfold possible_fmem_crash.
intros a.
destruct (H a); destruct (H0 a).
(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_sep_star : forall p q,
  flist_crash_xform (p * q) <=p=> flist_crash_xform p * flist_crash_xform q.
Proof.
(* original proof tokens: 122 *)
intros p q.
split.
(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_ptsto : forall a f,
  flist_crash_xform (a |-> f) =p=> exists f', a |-> f' * [[ file_crash f f' ]].
Proof.
(* original proof tokens: 131 *)

(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_lift_empty : forall P,
  flist_crash_xform [[ P ]] <=p=> [[ P ]].
Proof.
(* original proof tokens: 63 *)
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_emp :
  flist_crash_xform emp <=p=> emp.
Proof.
(* original proof tokens: 62 *)
unfold flist_crash_xform.
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Lemma flist_crash_xform_exists : forall T p,
  flist_crash_xform (exists (x : T), p x) =p=> exists x, flist_crash_xform (p x).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma flist_crash_flist_crash_xform : forall f f' (P : @pred _ _ _),
  flist_crash f f' ->
  P (list2nmem f) ->
  (flist_crash_xform P) (list2nmem f').
Proof.
(* original proof tokens: 166 *)
intros.
(* No more tactics to try *)
Admitted.

Instance flist_crash_xform_pimpl_proper :
  Proper (pimpl ==> pimpl) flist_crash_xform.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

