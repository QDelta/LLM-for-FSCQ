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
Require Import DirSep.
Require Import TreeCrash.
Require Import String.
Require Import DirTree DirTreeDef.
Inductive flatmem_entry_crash : flatmem_entry -> flatmem_entry -> Prop :=
| FMCNothing : flatmem_entry_crash Nothing Nothing
| FMCDir : forall dnum, flatmem_entry_crash (Dir dnum) (Dir dnum)
| FMCFile : forall inum f f',
  DTCrash.file_crash f f' ->
  flatmem_entry_crash (File inum f) (File inum f').
Definition possible_flatmem_crash (m m' : @Mem.mem (list string) (list_eq_dec string_dec) flatmem_entry) :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists f f', m a = Some f /\ m' a = Some f' /\ flatmem_entry_crash f f').
Definition flatmem_crash_xform p :=
  fun mf => exists mf', p mf' /\ possible_flatmem_crash mf' mf.
Theorem possible_flatmem_crash_mem_union : forall ma mb m', possible_flatmem_crash (mem_union ma mb) m'
  -> @mem_disjoint _ (list_eq_dec string_dec) _ ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_flatmem_crash ma ma' /\ possible_flatmem_crash mb mb'.
Proof.
(* skipped proof tokens: 396 *)
Admitted.
Theorem possible_flatmem_crash_disjoint : forall ma mb ma' mb',
  @mem_disjoint _ (list_eq_dec string_dec) _ ma' mb'
  -> possible_flatmem_crash ma ma'
  -> possible_flatmem_crash mb mb'
  -> @mem_disjoint _ (list_eq_dec string_dec) _ ma mb.
Proof.
(* skipped proof tokens: 67 *)
Admitted.
Theorem possible_flatmem_crash_union : forall ma mb ma' mb', possible_flatmem_crash ma ma'
  -> possible_flatmem_crash mb mb'
  -> possible_flatmem_crash (mem_union ma mb) (mem_union ma' mb').
Proof.
(* skipped proof tokens: 180 *)
Admitted.
Lemma flatmem_crash_xform_sep_star : forall p q,
  flatmem_crash_xform (p * q) <=p=> flatmem_crash_xform p * flatmem_crash_xform q.
Proof.
(* skipped proof tokens: 122 *)
Admitted.
Theorem flatmem_crash_xform_or_dist : forall p q,
  flatmem_crash_xform (p \/ q) <=p=> flatmem_crash_xform p \/ flatmem_crash_xform q.
Proof.
(* skipped proof tokens: 9 *)
Admitted.
Lemma flatmem_crash_xform_ptsto : forall a f,
  flatmem_crash_xform (a |-> f) =p=> exists f', a |-> f' * [[ flatmem_entry_crash f f' ]].
Proof.
(* skipped proof tokens: 131 *)
Admitted.
Lemma flatmem_crash_xform_lift_empty : forall P,
  flatmem_crash_xform [[ P ]] <=p=> [[ P ]].
Proof.
(* skipped proof tokens: 63 *)
Admitted.
Lemma flatmem_crash_xform_emp :
  flatmem_crash_xform emp <=p=> emp.
Proof.
(* skipped proof tokens: 62 *)
Admitted.
Lemma flatmem_crash_xform_exists : forall T p,
  flatmem_crash_xform (exists (x : T), p x) =p=> exists x, flatmem_crash_xform (p x).
Proof.
(* skipped proof tokens: 9 *)
Admitted.
Transparent dir2flatmem2.
Lemma tree_crash_flatmem_crash_xform : forall f f' (P : @pred _ _ _),
  DTCrash.tree_crash f f' ->
  P (dir2flatmem2 f) ->
  (flatmem_crash_xform P) (dir2flatmem2 f').
Proof.
(* skipped proof tokens: 180 *)
Admitted.
Theorem flatmem_crash_xform_nothing : forall pn,
  flatmem_crash_xform (pn |-> Nothing) =p=> pn |-> Nothing.
Proof.
(* skipped proof tokens: 111 *)
Admitted.
Theorem flatmem_crash_xform_dir : forall pn dnum,
  flatmem_crash_xform (pn |-> Dir dnum) =p=> pn |-> Dir dnum.
Proof.
(* skipped proof tokens: 111 *)
Admitted.
Theorem flatmem_crash_xform_file : forall pn inum f,
  flatmem_crash_xform (pn |-> File inum f) =p=>
    exists f', pn |-> File inum f' * [[ DTCrash.file_crash f f' ]].
Proof.
(* original proof tokens: 125 *)

(* No more tactics to try *)
Admitted.

Instance flatmem_crash_xform_pimpl_proper :
  Proper (pimpl ==> pimpl) flatmem_crash_xform.
Proof.
(* skipped proof tokens: 9 *)
Admitted.
