Require Import Word.
Require Import Prog.
Require Import EqdepFacts.
Require Import Arith.
Require Import AsyncDisk.
Require Import ListUtils.
Require Import List.
Set Implicit Arguments.
Definition hash2 sz1 sz2 (a : word sz1) (b : word sz2) :=
  hash_fwd (Word.combine a b).
Inductive hash_list_rep : (list valu) -> word hashlen -> hashmap -> Prop :=
  | HL_nil : forall hl hm,
      hl = hash_fwd default_valu ->
      hash_list_rep nil hl hm
  | HL_cons : forall l hl hl' x hm,
      hash_list_rep l hl hm ->
      hl' = hash2 x hl ->
      hashmap_get hm hl' = Some (existT _ _ (Word.combine x hl)) ->
      hash_list_rep (x :: l) hl' hm.
Inductive hash_list_prefixes : list valu -> list (word hashlen) -> hashmap -> Prop :=
  | HLP_default : forall hm,
    hash_list_prefixes nil nil hm
  | HLP_cons : forall v h vl hl hm,
    hash_list_rep (v :: vl) h hm ->
    hash_list_prefixes vl hl hm ->
    hash_list_prefixes (v :: vl) (h :: hl) hm.
Inductive hashmap_subset : list (word hashlen * {sz : nat & word sz}) -> hashmap -> hashmap -> Prop  :=
  | HS_nil : forall hm,
      hashmap_subset nil hm hm
  | HS_cons : forall h sz (k : word sz) l hm hm',
      hashmap_subset l hm hm' ->
      hash_safe hm' h k ->
      hashmap_subset ((h, (existT _ _ k)) :: l) hm (upd_hashmap' hm' h k).
Ltac existT_wordsz_neq H :=
  let Hx := fresh in
  inversion H as [ Hx ];
  try (rewrite <- plus_0_r in Hx at 1;
      apply plus_reg_l in Hx);
  try (rewrite <- plus_0_r in Hx;
      apply plus_reg_l in Hx);
  inversion Hx.
Ltac existT_wordsz_eq H :=
  let Hx := fresh in
  pose proof (eq_sigT_snd H) as Hx;
  autorewrite with core in Hx;
  try apply combine_inj in Hx.
Ltac contradict_hashmap_get_default H hm :=
  let Hx := fresh in
  contradict H;
  destruct hm; unfold hashmap_get, default_hash;
  destruct (weq (hash_fwd default_valu) (hash_fwd default_valu));
  intro Hx; try existT_wordsz_neq Hx;
  intuition.
Lemma hashmap_hashes_neq : forall hm h1 h2 sz1 sz2 (k1 : word sz1) (k2 : word sz2),
  hashmap_get hm h2 = Some (existT _ _ k2) ->
  hash_safe hm h1 k1 ->
  Some (existT _ _ k1) <> Some (existT _ _ k2) ->
  h1 <> h2.
Proof.
(* skipped proof tokens: 37 *)
Admitted.
Theorem hashmap_get_default : forall hm,
  hashmap_get hm default_hash = Some (existT _ _ default_valu).
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Theorem hash_list_rep_upd : forall l hl hm h sz (k : word sz),
  hash_list_rep l hl hm ->
  hash_safe hm h k ->
  hash_list_rep l hl (upd_hashmap' hm h k).
Proof.
(* skipped proof tokens: 129 *)
Admitted.
Theorem hash_list_rep_subset : forall hkl l hl hm hm',
  hashmap_subset hkl hm hm' ->
  hash_list_rep l hl hm ->
  hash_list_rep l hl hm'.
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Lemma hashmap_get_fwd_safe_eq: forall hm sz (x : word sz),
  hash_safe hm (hash_fwd x) x ->
  hashmap_get (upd_hashmap' hm (hash_fwd x) x) (hash_fwd x) = Some (existT _ _ x).
Proof.
(* skipped proof tokens: 54 *)
Admitted.
Theorem hash_list_injective : forall l1 l2 hv hm,
  hash_list_rep l1 hv hm -> hash_list_rep l2 hv hm -> l1 = l2.
Proof.
(* skipped proof tokens: 101 *)
Admitted.
Theorem hash_list_injective2 : forall l h1 h2 hm,
  hash_list_rep l h1 hm -> hash_list_rep l h2 hm -> h1 = h2.
Proof.
(* skipped proof tokens: 58 *)
Admitted.
Theorem hash_safe_eq : forall hm h1 h2 sz (k1 k2 : word sz),
  hash_safe hm h1 k1 ->
  hash_safe (upd_hashmap' hm h1 k1) h2 k2 ->
  h1 = h2 ->
  k1 = k2.
Proof.
(* skipped proof tokens: 165 *)
Admitted.
Lemma hashmap_subset_safe : forall hm2 l h k hm1,
  hashmap_subset l hm1 hm2 ->
  In (h, k) l ->
  hashmap_get hm2 h = Some k.
Proof.
(* skipped proof tokens: 190 *)
Admitted.
Theorem hashmap_subset_trans : forall hm3 l1 l2 hm1 hm2,
  hashmap_subset l1 hm1 hm2 ->
  hashmap_subset l2 hm2 hm3 ->
  hashmap_subset (l2 ++ l1) hm1 hm3.
Proof.
(* skipped proof tokens: 34 *)
Admitted.
Theorem hashmap_get_subset : forall hm2 hm1 h k l,
  hashmap_get hm1 h = Some k ->
  hashmap_subset l hm1 hm2 ->
  hashmap_get hm2 h = Some k.
Proof.
(* skipped proof tokens: 138 *)
Admitted.
Theorem hash_list_prefixes_upd : forall vl hl hm h sz (k : word sz),
  hash_list_prefixes vl hl hm ->
  hash_safe hm h k ->
  hash_list_prefixes vl hl (upd_hashmap' hm h k).
Proof.
(* skipped proof tokens: 46 *)
Admitted.
Theorem hash_list_prefixes_subset : forall l hm1 hm2 vl hl,
  hashmap_subset l hm1 hm2 ->
  hash_list_prefixes vl hl hm1 ->
  hash_list_prefixes vl hl hm2.
Proof.
(* original proof tokens: 45 *)

(* No more tactics to try *)
Admitted.

Lemma upd_hashmap_neq : forall hm h k,
  hm <> upd_hashmap hm h k.
Proof.
(* skipped proof tokens: 25 *)
Admitted.
Ltac solve_hashmap_subset_trans_step :=
  match goal with
  | [ H: hashmap_subset _ ?hm ?hm |- _] =>
    clear H 
  | [ H: hashmap_subset _ ?hm ?hm2, H2: hashmap_subset _ ?hm2 _ |- hashmap_subset _ ?hm _ ]
    => eapply hashmap_subset_trans; [ exact H | ]
  | [ |- hashmap_subset _ _ _ ]
    => eauto
  end.
Ltac solve_hashmap_subset_trans :=
  repeat solve_hashmap_subset_trans_step.
Ltac solve_hashmap_subset_step :=
  match goal with
  | [ H: exists l, hashmap_subset l _ _ |- _ ]
    => inversion H; clear H
  | [ |- exists _, hashmap_subset _ _ _ ]
    => eexists
  | [ |- hashmap_subset _ _ _ ]
    => try subst; solve [ solve_hashmap_subset_trans | repeat (eauto; econstructor) ]
  end.
Ltac solve_hashmap_subset :=
  repeat solve_hashmap_subset_step.
Ltac solve_hashmap_subset' :=
  repeat match goal with
  | [ H: exists _, hashmap_subset _ _ _ |- _ ]
    => destruct H
  end; eauto.
Ltac solve_hash_list_rep :=
  try match goal with
  | [ H: hash_list_rep _ ?h ?hm, Htrans: hashmap_subset _ ?hm _ |-
      hash_list_rep _ ?h _ ]
    => eapply hash_list_rep_subset; [ | exact H ];
        try solve_hashmap_subset
  | [ H: hash_list_rep ?l _ ?hm, Htrans: hashmap_subset _ ?hm _ |-
      hash_list_rep ?l _ _ ]
    => eapply hash_list_rep_subset; [ | exact H ];
        try solve_hashmap_subset
  | [ |- hash_list_rep _ _ _ ]
    => try (repeat eauto; econstructor)
  end.
