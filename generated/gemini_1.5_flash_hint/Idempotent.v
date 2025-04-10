Require Import Hoare.
Require Import Prog ProgMonad.
Require Import Pred PredCrash.
Require Import SepAuto.
Require Import AsyncDisk.
Require Import Hashmap.
Lemma step_hashmap_subset : forall T m vm hm p m' vm' hm' (v: T),
    step m vm hm p m' vm' hm' v ->
    exists l, hashmap_subset l hm hm'.
(* hint proof tokens: 13 *)
Proof.
  inversion 1; eauto.
Qed.
Hint Resolve step_hashmap_subset.
Lemma hashmap_subset_some_list_trans : forall hm hm' hm'',
    (exists l, hashmap_subset l hm hm') ->
    (exists l, hashmap_subset l hm' hm'') ->
    exists l, hashmap_subset l hm hm''.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma finished_val_eq : forall T m vm hm (v:T),
    exists v', Finished m vm hm v = Finished m vm hm v'.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Hint Resolve finished_val_eq.
Lemma exec_crashed_hashmap_subset' : forall T m m' vm vm' hm hm' p out,
  exec m vm hm p out
  -> (out = Crashed T m' hm' \/ exists v, out = Finished m' vm' hm' v)
  -> exists l, hashmap_subset l hm hm'.
(* hint proof tokens: 113 *)
Proof.
  intros.
  generalize dependent vm'.
  generalize dependent hm'.
  generalize dependent m'.
  induction H; subst; intuition; repeat deex; try congruence;
    try match goal with
        | [ H: @eq (outcome _) _ _ |- _ ] =>
          inversion H; subst
        end;
    eauto.

  eauto 7 using hashmap_subset_some_list_trans.
  eauto 7 using hashmap_subset_some_list_trans.

Unshelve.
  all: eauto.
Qed.
Lemma exec_crashed_hashmap_subset : forall T m m' vm hm hm' p out,
  exec m vm hm p out
  -> out = Crashed T m' hm'
  -> exists l, hashmap_subset l hm hm'.
(* hint proof tokens: 31 *)
Proof.
  intros.
  eapply exec_crashed_hashmap_subset'; eauto.

Unshelve.
  all: eauto.
Qed.
Ltac solve_hashmap_subset' :=
  match goal with
  | [ H: exec _ _ _ _ (Crashed _ _ _), Hpre: forall (_ : hashmap), _ =p=> ?pre _ _ _
      |- forall (_ : hashmap), _ =p=> ?pre _ _ _ ]
    => eapply exec_crashed_hashmap_subset in H as H'; eauto;
        intros;
        eapply pimpl_trans; try apply Hpre;
        autorewrite with crash_xform; cancel
  | [ |- context[hashmap_subset] ]
        => pred_apply; cancel
  end; try solve [
    repeat match goal with
    | [ H: forall (_ : hashmap), _ =p=> _ |- _ ] => clear H
    end; solve_hashmap_subset
  ].
Lemma corr3_from_corr2_failed:
  forall (TF TR: Type) m mr vmr hmr (p: prog TF) (r: prog TR) out
         (crash: hashmap -> pred) ppre rpre crashdone_p crashdone_r,
  exec_recover mr vmr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash hmr m
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre vmr hm' crashdone_p crash)
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre Mem.empty_mem hm' crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out <> RFailed TF TR.
(* hint proof tokens: 214 *)
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - edestruct H5; eauto.
    apply H3. eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    repeat (destruct H7; try congruence).
    repeat (destruct H7; try congruence).
  - rewrite H0. eapply IHexec_recover; eauto.
    + eapply exec_crashed_hashmap_subset with (hm':=hm') in H as H'.
      intros.
      eapply pimpl_trans; try apply H4.
      autorewrite with crash_xform; cancel.
      eauto.
    + solve_hashmap_subset'.
    + edestruct H5; eauto.
      apply H3. eapply crash_xform_apply; eauto.
      solve_hashmap_subset'.
      repeat (destruct H9; try congruence).
      repeat (destruct H9; try congruence).
Qed.
Lemma corr3_from_corr2_finished:
  forall (TF TR: Type) m mr vmr hmr (p: prog TF) (r: prog TR) out
         (crash: hashmap -> pred) ppre rpre crashdone_p crashdone_r m' vm' hm' v,
  exec_recover mr vmr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash hmr m
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre vmr hm' crashdone_p crash)
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre Mem.empty_mem hm' crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RFinished TR m' vm' hm' v
  -> crashdone_p vm' hm' v m'.
Proof.
(* original proof tokens: 89 *)

(* No more tactics to try *)
Admitted.

Lemma corr3_from_corr2_recovered:
  forall (TF TR: Type) m mr vmr hmr (p: prog TF) (r: prog TR) out
         (crash: hashmap -> pred) ppre rpre crashdone_p crashdone_r m' vm' hm' v,
  exec_recover mr vmr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash hmr m
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre vmr hm' crashdone_p crash)
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre Mem.empty_mem hm' crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RRecovered TF m' vm' hm' v
  -> crashdone_r vm' hm' v m'.
Proof.
(* original proof tokens: 240 *)

(* No more tactics to try *)
Admitted.

Theorem corr3_from_corr2: forall TF TR (p: prog TF) (r: prog TR) ppre rpre, {{ ppre }} p
  -> {{ rpre }} r
  -> {{ fun vm hm done crashdone => exists crash,
        ppre vm hm done crash
        * [[ forall hm',
          crash_xform (crash hm'
          * [[ exists l, hashmap_subset l hm hm' ]])
          =p=> rpre Mem.empty_mem hm' crashdone crash ]] }} p >> r.
Proof.
(* original proof tokens: 288 *)

(* No more tactics to try *)
Admitted.

Theorem corr3_from_corr2_rx :
  forall TF TR RF RR (p: prog TF) (r:  prog TR)
         (rxp : TF -> prog RF) (rxr : TR -> prog RR)
         ppre rpre,
  {{ ppre }} Bind p rxp
  -> {{ rpre }} Bind r rxr
  -> {{ fun vm hm done crashdone => exists crash,
        ppre vm hm done crash
        * [[ forall hm',
          crash_xform (crash hm'
          * [[ exists l, hashmap_subset l hm hm' ]])
          =p=> rpre Mem.empty_mem hm' crashdone crash ]] }} Bind p rxp >> Bind r rxr.
(* hint proof tokens: 19 *)
Proof.
  intros.
  apply corr3_from_corr2; eauto.
Qed.
Ltac eassign_idempred :=
  match goal with
  | [ H : crash_xform ?realcrash =p=> crash_xform ?body |- ?realcrash =p=> (_ ?hm') ] =>
    let t := eval pattern hm' in body in
    match eval pattern hm' in body with
    | ?bodyf hm' =>
      instantiate (1 := (fun hm => (exists p, p * [[ crash_xform p =p=> crash_xform (bodyf hm) ]])%pred))
    end
  | [ |- ?body =p=> (_ ?hm) ] =>
    let t := eval pattern hm in body in
    match eval pattern hm in body with
    | ?bodyf hm =>
      instantiate (1 := (fun hm' => (exists p, p * [[ crash_xform p =p=> crash_xform (bodyf hm') ]])%pred));
      try (cancel; xform_norm; cancel)
    end
  end.
