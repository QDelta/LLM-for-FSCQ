Require Import Prog.
Require Import Word AsyncDisk.
Require Import Mem Pred PredCrash.
Require Import FunctionalExtensionality.
Require Import List.
Require Import Arith.PeanoNat.
Require Import RelationClasses.
Require Import ListUtils.
Set Implicit Arguments.
Arguments possible_sync {AT AEQ} _ _.
Hint Resolve possible_sync_refl.
Hint Resolve possible_sync_trans.
Ltac inv_opt :=
  repeat match goal with
         | [ H: Some _ = Some _ |- _ ] =>
           inversion H; subst; clear H
         | [ H: Some _ = None |- _ ] =>
           solve [ inversion H ]
         | [ H: None = Some _ |- _ ] =>
           solve [ inversion H ]
         end.
Ltac sigT_eq :=
  match goal with
  | [ H: @eq (sigT _) _ _ |- _ ] =>
    apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H;
    subst
  end.
Section StepPreSync.
Arguments possible_sync {AT AEQ} _ _.
Hint Constructors step.
Hint Resolve ListUtils.incl_cons2.
Lemma possible_sync_respects_upd : forall A AEQ (m m': @mem A AEQ _)
                                       a v l l',
      possible_sync m m' ->
      incl l' l ->
      possible_sync (upd m a (v, l)) (upd m' a (v,l')).
Proof.
(* skipped proof tokens: 70 *)
Admitted.
Hint Resolve incl_refl.
Lemma possible_sync_respects_sync_mem : forall A AEQ (m m': @mem A AEQ _),
      possible_sync m m' ->
      possible_sync (sync_mem m) (sync_mem m').
(* hint proof tokens: 82 *)
Proof.
    unfold possible_sync, sync_mem; intros.
    specialize (H a).
    destruct (m a) as [ [] | ];
    destruct (m' a) as [ [] | ];
      subst; intuition eauto;
      try congruence;
      repeat deex;
      inv_opt;
      right.
    do 3 eexists; intuition eauto.
  Qed.
Hint Resolve possible_sync_respects_upd.
Hint Resolve possible_sync_respects_sync_mem.
Theorem step_presync : forall T (m m' m'' m''': rawdisk) vm hm (p: prog T) vm' hm' v,
      possible_sync (AEQ:=Nat.eq_dec) m m' ->
      step m' vm hm p m'' vm' hm' v ->
      possible_sync (AEQ:=Nat.eq_dec) m'' m''' ->
      exists (m'2: rawdisk),
        step m vm hm p m'2 vm' hm' v /\
        possible_sync (AEQ:=Nat.eq_dec) m'2 m'''.
Proof.
(* original proof tokens: 182 *)
intros.
inversion H0; subst.
(* No more tactics to try *)
Admitted.

End StepPreSync.
Module Exec.
Inductive R {sync_R: rawdisk -> rawdisk -> Prop} : forall T, rawdisk -> varmem -> hashmap -> prog T -> outcome T -> Prop :=
  | XRet : forall T m vm hm (v: T),
      R m vm hm (Ret v) (Finished m vm hm v)
  | XAlertModified : forall m vm hm,
      R m vm hm (AlertModified) (Finished m vm hm tt)
  | XDebug : forall m vm hm s a,
      R m vm hm (Debug s a) (Finished m vm hm tt)
  | XRdtsc : forall m vm hm t,
      R m vm hm (Rdtsc) (Finished m vm hm t)
  | XStep : forall T m vm hm (p: prog T) m' m'' vm' hm' v,
      step m vm hm p m' vm' hm' v ->
      sync_R m' m'' ->
      R m vm hm p (Finished m'' vm' hm' v)
  | XBindFinish : forall m vm hm T (p1: prog T) m' vm' hm' (v: T)
                    T' (p2: T -> prog T') out,
      R m vm hm p1 (Finished m' vm' hm' v) ->
      R m' vm' hm' (p2 v) out ->
      R m vm hm (Bind p1 p2) out
  | XBindFail : forall m vm hm T (p1: prog T)
                  T' (p2: T -> prog T'),
      R m vm hm p1 (Failed T) ->
      R m vm hm (Bind p1 p2) (Failed T')
  | XBindCrash : forall m vm hm T (p1: prog T) m' hm'
                   T' (p2: T -> prog T'),
      R m vm hm p1 (Crashed T m' hm') ->
      R m vm hm (Bind p1 p2) (Crashed T' m' hm')
  | XFail : forall m vm hm T (p: prog T),
      fail_step m vm p ->
      R m vm hm p (Failed T)
  | XCrash : forall m vm hm T (p: prog T),
      crash_step p ->
      R m vm hm p (Crashed T m hm).
Arguments R sync_R {T} _ _ _ _.
End Exec.
Hint Constructors Exec.R.
Hint Constructors exec.
Theorem exec_is_exec_possible_sync : forall T (p: prog T) m vm hm out,
    exec m vm hm p out <->
    Exec.R possible_sync m vm hm p out.
(* hint proof tokens: 15 *)
Proof.
  split; induction 1; eauto.
Qed.
Definition outcome_obs_le T (out out': outcome T) : Prop :=
  match out with
  | Failed _ => out' = Failed T
  | Finished d vm hm v => exists d', out' = Finished d' vm hm v /\
                            possible_sync (AEQ:=addr_eq_dec) d d'
  | Crashed _ d hm => exists d', out' = Crashed T d' hm /\
                         possible_sync (AEQ:=addr_eq_dec) d d'
  end.
Definition outcome_obs_ge T (out' out: outcome T) : Prop :=
  match out' with
  | Failed _ => out = Failed T
  | Finished d' vm hm v => exists d, out = Finished d vm hm v /\
                             possible_sync (AEQ:=addr_eq_dec) d d'
  | Crashed _ d' hm => exists d, out = Crashed T d hm /\
                           possible_sync (AEQ:=addr_eq_dec) d d'
  end.
Theorem outcome_obs_ge_ok : forall T (out out': outcome T),
    outcome_obs_le out out' <->
    outcome_obs_ge out' out.
(* hint proof tokens: 56 *)
Proof.
  destruct out, out'; simpl; intuition idtac;
    repeat deex;
    match goal with
    | [ H: @eq (outcome _) _ _ |- _ ] => inversion H; subst
    end; eauto.
Qed.
Theorem outcome_obs_le_refl : forall T (out: outcome T),
    outcome_obs_le out out.
(* hint proof tokens: 14 *)
Proof.
  destruct out; simpl; eauto.
Qed.
Theorem outcome_obs_le_trans : forall T (out out' out'': outcome T),
    outcome_obs_le out out' ->
    outcome_obs_le out' out'' ->
    outcome_obs_le out out''.
Proof.
(* skipped proof tokens: 49 *)
Admitted.
Instance outcome_obs_le_preorder {T} : PreOrder (outcome_obs_le (T:=T)).
(* hint proof tokens: 27 *)
Proof.
  constructor; hnf; intros; eauto using outcome_obs_le_refl, outcome_obs_le_trans.
Qed.
Hint Resolve outcome_obs_le_refl outcome_obs_le_trans.
Lemma possible_sync_in_domain : forall AT AEQ (d d': @mem AT AEQ _) a v vs',
    possible_sync d d' ->
    d' a = Some (v, vs') ->
    exists vs, d a = Some (v, vs) /\
          incl vs' vs.
Proof.
(* skipped proof tokens: 66 *)
Admitted.
Hint Resolve ListUtils.incl_cons2.
Hint Resolve incl_refl.
Hint Resolve possible_sync_respects_sync_mem.
Lemma step_sync_later : forall T (p: prog T) d d' d'' vm vm' hm hm' v,
    possible_sync d d' ->
    step d' vm hm p d'' vm' hm' v ->
    exists d'2, step d vm hm p d'2 vm' hm' v /\
           possible_sync (AEQ:=addr_eq_dec) d'2 d''.
(* hint proof tokens: 140 *)
Proof.
  intros.
  inversion H0; subst; repeat sigT_eq; eauto.
  - 
    eapply possible_sync_in_domain in H10; eauto; deex.
    eauto.
  - eapply possible_sync_in_domain in H10; eauto; deex.
    eexists; split.
    constructor; eauto.
    eapply possible_sync_respects_upd; eauto.
  - destruct vs, vs'.
    eapply possible_sync_in_domain in H10; eauto; deex.
    eexists; split.
    econstructor; eauto.
    eapply possible_sync_respects_upd; eauto.
Qed.
Lemma possible_sync_not_in_domain : forall AT AEQ (d d': @mem AT AEQ _) a,
    possible_sync d d' ->
    d' a = None ->
    d a = None.
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Hint Resolve possible_sync_not_in_domain.
Hint Constructors fail_step.
Lemma fail_step_sync_later  : forall T (p: prog T) d vm d',
    fail_step d' vm p ->
    possible_sync d d' ->
    fail_step d vm p.
(* hint proof tokens: 22 *)
Proof.
  inversion 1; intros; subst; repeat sigT_eq; eauto.
Qed.
Theorem exec_eq_sync_later : forall T (p: prog T) d d' vm hm out,
    Exec.R eq d' vm hm p out ->
    possible_sync d d' ->
    exists out', Exec.R eq d vm hm p out' /\
            outcome_obs_ge out out'.
(* hint proof tokens: 204 *)
Proof.
  intros.
  generalize dependent d.
  induction H; subst; intros; simpl.
  - eauto 10.
  - eauto 10.
  - eauto 10.
  - eauto 10.
  - eapply step_sync_later in H0; eauto; deex.
    eexists; intuition eauto.
  - specialize (IHR1 _ H1); deex.
    simpl in *; deex.
    specialize (IHR2 _ H5); deex.
    eauto 10.
  - specialize (IHR _ H0); deex.
    simpl in *; subst.
    eauto 10.
  - specialize (IHR _ H0); deex.
    simpl in *; deex.
    eauto 10.
  - eapply fail_step_sync_later in H; eauto.
  - inversion H; subst; repeat sigT_eq; eauto 10.
Qed.
Theorem exec_sync_obs_irrelevant : forall T (p: prog T) d vm hm out,
    Exec.R possible_sync d vm hm p out ->
    exists out', Exec.R eq d vm hm p out' /\
            outcome_obs_le out' out.
Proof.
(* original proof tokens: 202 *)

(* No more tactics to try *)
Admitted.

Module ExecRecover.
Inductive R
            {exec: forall T, rawdisk -> varmem -> hashmap -> prog T -> outcome T -> Prop}
            {possible_crash: rawdisk -> rawdisk -> Prop}
            (TF TR: Type)
  : rawdisk -> varmem -> hashmap -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
  | XRFail : forall m vm hm p1 p2,
      exec _ m vm hm p1 (Failed TF)
      -> R m vm hm p1 p2 (RFailed TF TR)
  | XRFinished : forall m vm hm p1 p2 m' vm' hm' (v: TF),
      exec _ m vm hm p1 (Finished m' vm' hm' v)
      -> R m vm hm p1 p2 (RFinished TR m' vm' hm' v)
  | XRCrashedFailed : forall m vm hm p1 p2 m' hm' m'r,
      exec _ m vm hm p1 (Crashed TF m' hm')
      -> possible_crash m' m'r
      -> R (TF:=TR) m'r Mem.empty_mem hm' p2 p2 (RFailed TR TR)
      -> R m vm hm p1 p2 (RFailed TF TR)
  | XRCrashedFinished : forall m vm hm p1 p2 m' hm' m'r m'' vm'' hm'' (v: TR),
      exec _ m vm hm p1 (Crashed TF m' hm')
      -> possible_crash m' m'r
      -> R (TF:=TR) m'r Mem.empty_mem hm' p2 p2 (RFinished TR m'' vm'' hm'' v)
      -> R m vm hm p1 p2 (RRecovered TF m'' vm'' hm'' v)
  | XRCrashedRecovered : forall m vm hm p1 p2 m' hm' m'r m'' vm'' hm'' (v: TR),
      exec _ m vm hm p1 (Crashed TF m' hm')
      -> possible_crash m' m'r
      -> R (TF:=TR) m'r Mem.empty_mem hm' p2 p2 (RRecovered TR m'' vm'' hm'' v)
      -> R m vm hm p1 p2 (RRecovered TF m'' vm'' hm'' v).
End ExecRecover.
Arguments ExecRecover.R exec possible_crash {TF TR} _ _ _ _ _.
Definition routcome_disk_R (R: rawdisk -> rawdisk -> Prop)
           TF TR (out out': recover_outcome TF TR) :=
  match out with
  | RFinished _ d vm hm v => exists d', out' = RFinished _ d' vm hm v /\
                               R d d'
  | RRecovered _ d vm hm v => exists d', out' = RRecovered _ d' vm hm v /\
                                R d d'
  | RFailed _ _ => out' = RFailed _ _
  end.
Definition routcome_disk_R_conv (R: rawdisk -> rawdisk -> Prop)
           TF TR (out' out: recover_outcome TF TR) :=
  match out' with
  | RFinished _ d vm hm v => exists d', out = RFinished _ d' vm hm v /\
                               R d' d
  | RRecovered _ d vm hm v => exists d', out = RRecovered _ d' vm hm v /\
                                R d' d
  | RFailed _ _ => out = RFailed _ _
  end.
Theorem routcome_disk_R_conv_ok : forall R TF TR (out out': recover_outcome TF TR),
    routcome_disk_R R out out' <->
    routcome_disk_R_conv R out' out.
(* hint proof tokens: 59 *)
Proof.
  split;
    destruct out, out'; simpl; intros;
      repeat deex;
      match goal with
      | [ H: @eq (recover_outcome _ _) _ _ |- _ ] =>
        inversion H; subst
      end; eauto.
Qed.
Hint Constructors ExecRecover.R exec_recover.
Theorem exec_recover_is_R : forall TF TR d vm hm (p: prog TF) (r: prog TR) out,
    exec_recover d vm hm p r out <->
    ExecRecover.R exec possible_crash d vm hm p r out.
Proof.
(* skipped proof tokens: 15 *)
Admitted.
Theorem exec_recover_without_sync : forall TF TR d vm hm (p: prog TF) (r: prog TR) out,
    ExecRecover.R (@Exec.R possible_sync) possible_crash d vm hm p r out ->
    exists out', ExecRecover.R (@Exec.R eq) possible_crash d vm hm p r out' /\
            routcome_disk_R possible_sync out' out.
(* hint proof tokens: 215 *)
Proof.
  induction 1; simpl;
    repeat match goal with
           | [ H: Exec.R possible_sync _ _ _ _ _ |- _ ] =>
             apply exec_sync_obs_irrelevant in H; simpl in H
           | [ H: outcome_obs_le _ _ |- _ ] =>
             apply outcome_obs_ge_ok in H; progress simpl in H
           | [ H: routcome_disk_R _ _ _ |- _ ] =>
             apply routcome_disk_R_conv_ok in H; progress simpl in H
           | [ H: possible_sync ?m ?m',
                  H': possible_crash ?m' ?m'' |- _ ] =>
             lazymatch goal with
             | [ H: possible_crash m m'' |- _ ] => fail
             | _ => pose proof possible_crash_possible_sync_trans H H'
             end
           | _ => progress subst
           | _ => deex
           end;
    try solve [ eexists; intuition eauto; simpl; eauto ].
Qed.
Module PhysicalSemantics.
Definition flush_disk (d d': rawdisk) :=
    forall a,
      match d a with
      | None => d' a = None
      | Some (v, vs) => exists n, d' a = Some (v, firstn n vs)
      end.
Theorem flush_disk_refl : forall d, flush_disk d d.
Proof.
(* skipped proof tokens: 45 *)
Admitted.
Theorem flush_disk_trans : forall d d' d'',
      flush_disk d d' ->
      flush_disk d' d'' ->
      flush_disk d d''.
(* hint proof tokens: 83 *)
Proof.
    unfold flush_disk; intros.
    specialize (H a).
    specialize (H0 a).
    destruct (d a) as [ [? ?] | ];
      destruct (d' a) as [ [? ?] | ];
      repeat deex;
      inv_opt;
      try congruence.
    rewrite firstn_firstn in H0.
    eauto.
  Qed.
Lemma firstn_incl : forall A (l: list A) n,
      incl (firstn n l) l.
Proof.
(* skipped proof tokens: 20 *)
Admitted.
Hint Resolve firstn_incl.
Theorem flush_disk_is_sync : forall d d',
      flush_disk d d' ->
      possible_sync (AEQ:=addr_eq_dec) d d'.
Proof.
(* skipped proof tokens: 47 *)
Admitted.
Hint Resolve flush_disk_is_sync.
Fixpoint diskval (v: valu) (vs: list valu) :=
    match vs with
    | nil => v
    | v'::vs' => diskval v' vs'
    end.
Definition discard_buffers (d d': rawdisk) :=
    forall a, match d a with
         | None => d' a = None
         | Some (v, vs) =>
           d' a = Some (diskval v vs, nil)
         end.
Lemma discard_buffers_f (d: rawdisk) : {d':rawdisk | discard_buffers d d'}.
(* hint proof tokens: 69 *)
Proof.
    unfold discard_buffers.
    exists (fun a =>
         match d a with
         | None => None
         | Some (v, vs) =>
           Some (diskval v vs, nil)
         end).
    intros.
    destruct (d a); auto.
    destruct p; auto.
  Qed.
Remark discard_buffers_deterministic : forall d d' d'',
      discard_buffers d d' ->
      discard_buffers d d'' ->
      d' = d''.
(* hint proof tokens: 50 *)
Proof.
    unfold discard_buffers; intros.
    extensionality a.
    specialize (H a).
    specialize (H0 a).
    destruct (d a) as [ [? ?] | ]; congruence.
  Qed.
Definition outcome_disk_R (R: rawdisk -> rawdisk -> Prop) T (out out':outcome T) :=
    match out with
    | Finished d vm hm v => exists d', out' = Finished d' vm hm v /\
                              R d d'
    | Crashed _ d hm => exists d', out' = Crashed _ d' hm /\
                           R d d'
    | Failed _ => out' = Failed _
    end.
Definition pexec T d vm hm (p: prog T) out :=
    exists out', Exec.R flush_disk d vm hm p out' /\
          outcome_disk_R flush_disk out' out.
Definition pexec_recover := @ExecRecover.R pexec discard_buffers.
Hint Resolve flush_disk_refl flush_disk_trans.
Hint Resolve flush_disk_is_sync.
Lemma flush_disk_in_domain : forall d d' a v vs,
      d a = Some (v, vs)  ->
      flush_disk d d' ->
      exists n, d' a = Some (v, firstn n vs).
Proof.
(* skipped proof tokens: 31 *)
Admitted.
Theorem outcome_obs_le_to_R : forall T (out out': outcome T),
      outcome_obs_le out out' <->
      outcome_disk_R possible_sync out out'.
(* hint proof tokens: 28 *)
Proof.
    unfold outcome_obs_le, outcome_disk_R; split; intros;
      destruct out; eauto.
  Qed.
Lemma exec_flush_to_exec : forall T (p: prog T) d vm hm out,
      Exec.R flush_disk d vm hm p out ->
      exec d vm hm p out.
Proof.
(* skipped proof tokens: 28 *)
Admitted.
Corollary pexec_to_exec : forall T (p: prog T) d vm hm out,
      pexec d vm hm p out ->
      exists out', exec d vm hm p out' /\
              outcome_disk_R flush_disk out' out.
Proof.
(* skipped proof tokens: 26 *)
Admitted.
Definition outcome_disk_R_conv (R: rawdisk -> rawdisk -> Prop)
             T (out' out: outcome T) :=
   match out' with
   | Finished m vm hm v => exists m', out = Finished m' vm hm v /\
                               R m' m
   | Crashed _ m hm => exists m', out = Crashed _ m' hm /\
                            R m' m
   | Failed _ => out = Failed  _
   end.
Theorem outcome_disk_R_conv_ok : forall R T (out out': outcome T),
      outcome_disk_R R out out' <->
      outcome_disk_R_conv R out' out.
Proof.
(* skipped proof tokens: 69 *)
Admitted.
Lemma diskval_firstn_in_list : forall l n v,
      In (diskval v (firstn n l)) (v::l).
(* hint proof tokens: 46 *)
Proof.
    induction l; simpl; intros.
    rewrite firstn_nil; eauto.
    destruct n; simpl; eauto.
    destruct (IHl n a); simpl; eauto.
  Qed.
Theorem discard_flush_is_crash : forall d d' d'',
      flush_disk d d' ->
      discard_buffers d' d'' ->
      possible_crash d d''.
Proof.
(* skipped proof tokens: 100 *)
Admitted.
Hint Constructors exec_recover.
Theorem pexec_recover_to_exec_recover : forall TF TR (p: prog TF) (r: prog TR) d vm hm out,
      pexec_recover d vm hm p r out ->
      exists out', exec_recover d vm hm p r out' /\
              routcome_disk_R possible_sync out' out.
Proof.
(* skipped proof tokens: 218 *)
Admitted.
End PhysicalSemantics.
