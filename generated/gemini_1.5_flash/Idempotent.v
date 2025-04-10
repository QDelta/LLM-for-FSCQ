Require Import Hoare.
Require Import Prog ProgMonad.
Require Import Pred PredCrash.
Require Import SepAuto.
Require Import AsyncDisk.
Require Import Hashmap.
Lemma step_hashmap_subset : forall T m vm hm p m' vm' hm' (v: T),
    step m vm hm p m' vm' hm' v ->
    exists l, hashmap_subset l hm hm'.
Proof.
(* original proof tokens: 13 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 113 *)
destruct 1.
(* No more tactics to try *)
Admitted.

Lemma exec_crashed_hashmap_subset : forall T m m' vm hm hm' p out,
  exec m vm hm p out
  -> out = Crashed T m' hm'
  -> exists l, hashmap_subset l hm hm'.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 214 *)
intros.
inversion H; subst; clear H; try congruence.
apply False_ind; auto.
(* No more tactics to try *)
Admitted.

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
Proof.
(* original proof tokens: 19 *)

(* No more tactics to try *)
Admitted.

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
