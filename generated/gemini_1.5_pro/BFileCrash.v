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
(* skipped proof tokens: 41 *)
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

(* No more tactics to try *)
Admitted.

Theorem possible_fmem_crash_disjoint : forall ma mb ma' mb',
  @mem_disjoint _ addr_eq_dec _ ma' mb'
  -> possible_fmem_crash ma ma'
  -> possible_fmem_crash mb mb'
  -> @mem_disjoint _ addr_eq_dec _ ma mb.
Proof.
(* skipped proof tokens: 67 *)
Admitted.
Theorem possible_fmem_crash_union : forall ma mb ma' mb', possible_fmem_crash ma ma'
  -> possible_fmem_crash mb mb'
  -> possible_fmem_crash (mem_union ma mb) (mem_union ma' mb').
Proof.
(* skipped proof tokens: 180 *)
Admitted.
Lemma flist_crash_xform_sep_star : forall p q,
  flist_crash_xform (p * q) <=p=> flist_crash_xform p * flist_crash_xform q.
Proof.
(* skipped proof tokens: 122 *)
Admitted.
Lemma flist_crash_xform_ptsto : forall a f,
  flist_crash_xform (a |-> f) =p=> exists f', a |-> f' * [[ file_crash f f' ]].
Proof.
(* skipped proof tokens: 131 *)
Admitted.
Lemma flist_crash_xform_lift_empty : forall P,
  flist_crash_xform [[ P ]] <=p=> [[ P ]].
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma flist_crash_xform_emp :
  flist_crash_xform emp <=p=> emp.
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Lemma flist_crash_xform_exists : forall T p,
  flist_crash_xform (exists (x : T), p x) =p=> exists x, flist_crash_xform (p x).
Proof.
(* skipped proof tokens: 9 *)
Admitted.
Lemma flist_crash_flist_crash_xform : forall f f' (P : @pred _ _ _),
  flist_crash f f' ->
  P (list2nmem f) ->
  (flist_crash_xform P) (list2nmem f').
Proof.
(* skipped proof tokens: 166 *)
Admitted.
Instance flist_crash_xform_pimpl_proper :
  Proper (pimpl ==> pimpl) flist_crash_xform.
Proof.
(* skipped proof tokens: 9 *)
Admitted.
