Require Import Prog.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import Word.
Require Import FSLayout.
Require Import BasicProg.
Require Import Cache.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Mem.
Require Import SepAuto.
Require Import List.
Require Import Array.
Require Import EqdepFacts.
Require Import Arith.
Require Import ListUtils.
Require Import Lia.
Set Implicit Arguments.
Definition hash_list h values :=
  let^ (hash) <- ForEach item items_rest values
  Hashmap hm'
  Ghost [ l crash ]
  Loopvar [ hash ]
  Invariant
    exists items_prefix,
    [[ values = items_prefix ++ items_rest ]] *
    [[ hash_list_rep (rev items_prefix ++ l) hash hm' ]]
  OnCrash crash
  Begin
    hash <- Hash2 item hash;
    Ret ^(hash)
  Rof ^(h);
  Ret hash.
Theorem hash_list_ok : forall h values,
  {< l,
  PRE:hm
    emp * [[ hash_list_rep l h hm ]]
  POST:hm' RET:h'
    emp * [[ hash_list_rep (rev values ++ l) h' hm' ]]
  CRASH:hm'
    emp * [[ exists i hash, hash_list_rep (rev (firstn i values) ++ l) hash hm' ]]
  >} hash_list h values.
Proof.
(* original proof tokens: 178 *)

(* No more tactics to try *)
Admitted.

Hint Extern 1 ({{_}} Bind (hash_list _ _) _) => apply hash_list_ok : prog.
