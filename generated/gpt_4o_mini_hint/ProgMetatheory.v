Require Import Prog.
Require Import Mem Pred.
Require Import Word.
Require Import PredCrash.
Require Import AsyncDisk.
Set Implicit Arguments.
Hint Constructors fail_step step exec.
Definition buf_ne sz1 (buf1: word sz1) sz2 (buf2: word sz2)
  := forall (H: sz1 = sz2), eq_rect _ _ buf1 _ H <> buf2.
Lemma buf_ne_sz_same : forall sz (buf1 buf2: word sz),
    buf1 <> buf2 ->
    buf_ne buf1 buf2.
(* hint proof tokens: 31 *)
Proof.
  unfold buf_ne; intros.
  rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
  apply addr_eq_dec.
Qed.
Lemma buf_ne_sz_neq : forall sz1 sz2 (buf1: word sz1) (buf2: word sz2),
    sz1 <> sz2 ->
    buf_ne buf1 buf2.
(* hint proof tokens: 17 *)
Proof.
  unfold buf_ne; intros.
  congruence.
Qed.
Hint Resolve buf_ne_sz_same buf_ne_sz_neq.
Lemma possible_sync_refl : forall A AEQ (m: @mem A AEQ valuset),
    possible_sync m m.
(* hint proof tokens: 51 *)
Proof.
  unfold possible_sync; intros.
  destruct (m a).
  - right.
    destruct p.
    exists w, l, l; intuition auto.
    apply List.incl_refl.
  - left; auto.
Qed.
Hint Resolve possible_sync_refl.
Definition hash_safe_dec hm h sz (buf: word sz) : {hash_safe hm h buf} + {~hash_safe hm h buf}.
Proof.
  unfold hash_safe.
  case_eq (hashmap_get hm h); intros.
  destruct s.
  destruct (addr_eq_dec sz x); subst.
  destruct (weq buf w); subst.
  - 
    eauto.
  - 
    right; intro.
    intuition (try congruence).
    inversion H1.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; eauto.
    apply addr_eq_dec.
  - 
    right; intro.
    intuition (try congruence).
  - 
    left; eauto.
Qed.
Inductive hashmap_wf : hashmap -> Prop :=
| empty_hashmap_wf : hashmap_wf empty_hashmap
| upd_hashmap_wf : forall hm sz (buf: word sz),
    hashmap_wf hm ->
    hashmap_wf (upd_hashmap hm (hash_fwd buf) (existT _ _ buf)).
Lemma hashmap_wf_get : forall hm sz1 (buf1: word sz1) sz2 (buf2: word sz2),
    hashmap_wf hm ->
    hashmap_get hm (hash_fwd buf1) = Some (existT _ _ buf2) ->
    hash_fwd buf1 = hash_fwd buf2.
Proof.
(* original proof tokens: 215 *)

(* No more tactics to try *)
Admitted.

Lemma de_morgan : forall (P Q:Prop),
    ~(P \/ Q) ->
    ~P /\ ~Q.
Proof.
(* original proof tokens: 9 *)
(* generated proof tokens: 36 *)

intros P Q H.
split.
- intro HP. apply H. left. assumption.
- intro HQ. apply H. right. assumption.
Qed.

Theorem not_hash_safe_conflict : forall hm sz (buf: word sz),
    hashmap_wf hm ->
    ~hash_safe hm (hash_fwd buf) buf ->
    exists sz' (buf': word sz'),
      buf_ne buf buf' /\
      hash_fwd buf = hash_fwd buf'.
(* hint proof tokens: 120 *)
Proof.
  unfold hash_safe; intros.
  apply de_morgan in H0; intuition.
  case_eq (hashmap_get hm (hash_fwd buf)); intros;
    try solve [ exfalso; eauto ].
  destruct s.
  destruct (addr_eq_dec sz x); subst.
  destruct (weq buf w); subst.
  exfalso; eauto.
  exists _, w.
  apply hashmap_wf_get in H0; auto.
  exists _,  w.
  apply hashmap_wf_get in H0; eauto.
Qed.
Hint Constructors hashmap_wf.
Theorem exec_preserves_hashmap_wf : forall T (p: prog T) d vm hm d' vm' hm' v,
    hashmap_wf hm ->
    exec d vm hm p (Finished d' vm' hm' v) ->
    hashmap_wf hm'.
Proof.
(* original proof tokens: 142 *)

(* No more tactics to try *)
Admitted.

Hint Resolve exec_preserves_hashmap_wf.
Hint Resolve tt.
