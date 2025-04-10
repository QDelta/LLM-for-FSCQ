Require Import Bool.
Require Import Word.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Import ListNotations.
Set Implicit Arguments.
Theorem pathname_decide_prefix : forall (base pn : list string),
    (exists suffix, pn = base ++ suffix) \/
    (~ exists suffix, pn = base ++ suffix).
Proof.
(* skipped proof tokens: 96 *)
Admitted.
Definition pathname_prefix p1 p2 :=
    (exists suffix : list string, p1 ++ suffix = p2).
Lemma pathname_prefix_nil: forall suffix,
    pathname_prefix [] suffix.
Proof.
(* skipped proof tokens: 29 *)
Admitted.
Lemma pathname_prefix_head: forall n suffix,
    pathname_prefix [n] ([n]++suffix).
Proof.
(* skipped proof tokens: 24 *)
Admitted.
Lemma pathname_prefix_head_neq: forall a s suffix,
    a <> s ->
    ~pathname_prefix [a] (s::suffix).
Proof.
(* skipped proof tokens: 51 *)
Admitted.
Lemma pathname_prefix_ex_falso: forall name suffix,
    ~ pathname_prefix [name] suffix ->
    (exists suffix0 : list string, suffix = [name] ++ suffix0) -> False.
Proof.
(* skipped proof tokens: 36 *)
Admitted.
Lemma pathname_prefix_neq: forall path path',
    ~ (exists suffix : list string, path = path' ++ suffix) ->
    ~ pathname_prefix path' path.
Proof.
(* skipped proof tokens: 40 *)
Admitted.
Lemma pathname_prefix_head_neq': forall path name name',
    ~ pathname_prefix [name] (name' :: path) ->
    name <> name'.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Lemma pathname_prefix_trim : forall a b c,
    pathname_prefix a b <-> pathname_prefix (c ++ a) (c ++ b).
Proof.
(* skipped proof tokens: 56 *)
Admitted.
