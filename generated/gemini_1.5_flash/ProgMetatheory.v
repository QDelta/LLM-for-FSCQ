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
Proof.
(* original proof tokens: 31 *)
intros sz buf1 buf2 H.
(* No more tactics to try *)
Admitted.

Lemma buf_ne_sz_neq : forall sz1 sz2 (buf1: word sz1) (buf2: word sz2),
    sz1 <> sz2 ->
    buf_ne buf1 buf2.
Proof.
(* original proof tokens: 17 *)

(* No more tactics to try *)
Admitted.

Hint Resolve buf_ne_sz_same buf_ne_sz_neq.
Lemma possible_sync_refl : forall A AEQ (m: @mem A AEQ valuset),
    possible_sync m m.
Proof.
(* original proof tokens: 51 *)
intros. unfold possible_sync. intros.
destruct (m a); auto.
elimtype False.
(* No more tactics to try *)
Admitted.

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
(* generated proof tokens: 40 *)

intros P Q H.
split.
intro H1.
apply H.
left.
exact H1.
intro H2.
apply H.
right.
exact H2.
Qed.

Theorem not_hash_safe_conflict : forall hm sz (buf: word sz),
    hashmap_wf hm ->
    ~hash_safe hm (hash_fwd buf) buf ->
    exists sz' (buf': word sz'),
      buf_ne buf buf' /\
      hash_fwd buf = hash_fwd buf'.
Proof.
(* original proof tokens: 120 *)
intros hm sz buf Hwf Hnotsafe.
unfold hash_safe in Hnotsafe.
apply de_morgan in Hnotsafe.
destruct Hnotsafe as [Hget ?].
inversion Hwf; subst.
eexists; eexists; split.
eapply buf_ne_sz_neq.
intro.
apply Hget.
(* No more tactics to try *)
Admitted.

Hint Constructors hashmap_wf.
Theorem exec_preserves_hashmap_wf : forall T (p: prog T) d vm hm d' vm' hm' v,
    hashmap_wf hm ->
    exec d vm hm p (Finished d' vm' hm' v) ->
    hashmap_wf hm'.
Proof.
(* original proof tokens: 142 *)
induction 1; auto.
(* No more tactics to try *)
Admitted.

Hint Resolve exec_preserves_hashmap_wf.
Hint Resolve tt.
