Require Import Mem.
Require Import Pred.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import Morphisms.
Require Import AsyncDisk.
Require Import Arith.
Set Implicit Arguments.
Definition ptsto_subset {AT AEQ} (a : AT) (vs : valuset) : @pred AT AEQ valuset :=
  (exists old, a |-> (fst vs, old) * [[ incl old (snd vs) ]])%pred.
Notation "a |=> v" := (a |-> ((v, nil) : valuset))%pred (at level 35) : pred_scope.
Notation "a |~> v" := (exists old, a |-> ((v, old) : valuset))%pred (at level 35) : pred_scope.
Notation "a |+> v" := (ptsto_subset a v) (at level 35) : pred_scope.
Notation "a |+>?" := (exists v, a |+> v)%pred (at level 35) : pred_scope.
Definition rawpred := @pred addr addr_eq_dec valuset.
Definition possible_crash (m m' : rawdisk) : Prop :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists vs v', m a = Some vs /\ m' a = Some (v', nil) /\ In v' (vsmerge vs)).
Definition crash_xform (p : rawpred) : rawpred :=
  fun m => exists m', p m' /\ possible_crash m' m.
Definition sync_xform (p : rawpred) : rawpred :=
  fun m => exists m', p m' /\ m = sync_mem m'.
Theorem crash_xform_apply : forall (p : rawpred) (m m' : rawdisk), possible_crash m m'
  -> p m
  -> crash_xform p m'.
Proof.
(* original proof tokens: 14 *)
(* generated proof tokens: 19 *)
intros.
exists m; split; [ assumption | apply H ].
Qed.

Theorem possible_crash_mem_union : forall (ma mb m' : rawdisk), possible_crash (mem_union ma mb) m'
  -> @mem_disjoint _ addr_eq_dec _ ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_crash ma ma' /\ possible_crash mb mb'.
Proof.
(* original proof tokens: 384 *)
unfold possible_crash.
intros.
(* No more tactics to try *)
Admitted.

Theorem possible_crash_disjoint : forall (ma mb ma' mb' : rawdisk),
  @mem_disjoint _ addr_eq_dec _ ma' mb'
  -> possible_crash ma ma'
  -> possible_crash mb mb'
  -> @mem_disjoint _ addr_eq_dec _ ma mb.
Proof.
(* original proof tokens: 65 *)
intros.
apply mem_disjoint_comm.
(* No more tactics to try *)
Admitted.

Theorem possible_crash_union : forall (ma mb ma' mb' : rawdisk), possible_crash ma ma'
  -> possible_crash mb mb'
  -> possible_crash (mem_union ma mb) (mem_union ma' mb').
Proof.
(* original proof tokens: 178 *)
intros.
unfold possible_crash.
intros.
destruct (ma a) as [|v1 old1], (mb a) as [|v2 old2], (ma' a) as [|v1' _], (mb' a) as [|v2' _].
  
  auto.
  
  auto.
  
  auto.
  
  auto.
  
  eauto.
  
  eauto.
  
  eauto.
  
  eauto.
  
  eauto.
  
  eauto.
  
  eauto.
  
  eauto.
destruct (H a) as [H1 | H1].
right.
(* No more tactics to try *)
Admitted.

Theorem possible_crash_trans : forall (ma mb mc : rawdisk),
  possible_crash ma mb ->
  possible_crash mb mc ->
  possible_crash ma mc.
Proof.
(* original proof tokens: 88 *)
intros.
unfold possible_crash.
intros a.
destruct (H a) as [? | ?].
destruct (H0 a) as [H2 | H3].
right.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_notindomain : forall AEQ (m m' : @mem _ AEQ _) a,
  possible_crash m m' ->
  notindomain a m ->
  notindomain a m'.
Proof.
(* original proof tokens: 29 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_upd : forall m m' a v vs,
  possible_crash m m' ->
  In v (vsmerge vs) ->
  possible_crash (upd m a vs) (upd m' a (v, nil)).
Proof.
(* original proof tokens: 58 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_updSome : forall m m' a v vs,
  possible_crash m m' ->
  In v (vsmerge vs) ->
  possible_crash (updSome m a vs) (updSome m' a (v, nil)).
Proof.
(* original proof tokens: 87 *)
intros.
(* No more tactics to try *)
Admitted.

Definition synced_mem (m : rawdisk) :=
  forall a, m a = None \/ exists v, m a = Some (v, nil).
Lemma synced_mem_snd_nil : forall m a vs,
  synced_mem m ->
  m a = Some vs ->
  snd vs = nil.
Proof.
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Theorem possible_crash_synced : forall m m',
  possible_crash m m' ->
  synced_mem m'.
Proof.
(* original proof tokens: 38 *)

(* No more tactics to try *)
Admitted.

Theorem possible_crash_refl : forall m,
  synced_mem m ->
  possible_crash m m.
Proof.
(* original proof tokens: 44 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_emp_l : forall (m m' : @mem _ addr_eq_dec _),
  possible_crash m m' ->
  emp m' ->
  emp m.
Proof.
(* original proof tokens: 32 *)
intros m m' Hpc Hemp.
apply emp_empty_mem_only in Hemp.
rewrite Hemp in Hpc.
unfold possible_crash in Hpc.
intros a.
destruct (Hpc a).
inversion H; auto.
inversion H; subst; auto.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_emp_r : forall (m m' : @mem _ addr_eq_dec _),
  possible_crash m m' ->
  emp m ->
  emp m'.
Proof.
(* original proof tokens: 32 *)
intros m m' Hpc Hemp.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_ptsto_upd_incl' : forall m m' a vs vs',
  m a = Some vs ->
  possible_crash m m' ->
  incl (vsmerge vs) (vsmerge vs') ->
  possible_crash (upd m a vs') m'.
Proof.
(* original proof tokens: 152 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_ptsto_upd_incl : forall F m m' a vs vs',
  (F * a |-> vs)%pred m ->
  possible_crash m m' ->
  incl (vsmerge vs) (vsmerge vs') ->
  possible_crash (upd m a vs') m'.
Proof.
(* original proof tokens: 34 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_upd_incl : forall m m' a v v0,
  possible_crash (upd m a v) m' ->
  m a = Some v0 ->
  incl (vsmerge v) (vsmerge v0) ->
  possible_crash m m'.
Proof.
(* original proof tokens: 143 *)
intros.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_upd_nil : forall m m' a v0,
  possible_crash (upd m a (fst v0, nil)) m' ->
  m a = Some v0 ->
  possible_crash m m'.
Proof.
(* original proof tokens: 38 *)
intros m m' a v0 H1 H2.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_ptsto_upd_postfix : forall F m m' a v vs vs',
  (F * a |-> (v, vs))%pred m ->
  possible_crash m m' ->
  postfix vs vs' ->
  possible_crash (upd m a (v, vs')) m'.
Proof.
(* original proof tokens: 59 *)
intros.
destruct H1 as [n H1].
(* No more tactics to try *)
Admitted.

Lemma possible_crash_sel_exis : forall m m' a vs,
  possible_crash m m' ->
  m a = Some vs ->
  exists v, m' a = Some (v, nil) /\ In v (vsmerge vs).
Proof.
(* original proof tokens: 55 *)

(* No more tactics to try *)
Admitted.

Theorem crash_xform_sep_star_dist : forall (p q : rawpred),
  crash_xform (p * q) <=p=> crash_xform p * crash_xform q.
Proof.
(* original proof tokens: 110 *)
unfold piff.
split.
intros.
unfold crash_xform.
unfold pimpl.
intros m H.
unfold sep_star.
apply sep_star_comm.
destruct H as [m1 H].
destruct H as [Hpq Hpc].
apply sep_star_comm.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_or_dist : forall (p q : rawpred),
  crash_xform (p \/ q) <=p=> crash_xform p \/ crash_xform q.
Proof.
(* original proof tokens: 9 *)
split.
intros.
unfold crash_xform.
unfold pimpl.
intros.
destruct H.
destruct H as [H1 H2].
destruct H1.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_lift_empty : forall (P : Prop),
  @crash_xform [[ P ]] <=p=> [[ P ]].
Proof.
(* original proof tokens: 59 *)
unfold crash_xform.
intros.
eapply piff_refl.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_sep_star_apply : forall (p q : rawpred) (m m' : mem), possible_crash m m'
  -> (p * q)%pred m
  -> (crash_xform p * crash_xform q)%pred m'.
Proof.
(* original proof tokens: 59 *)
unfold crash_xform.
unfold sep_star.
intros.
apply sep_star_comm.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_exists_comm : forall T (p : T -> rawpred),
  crash_xform (exists x, p x) <=p=> exists x, crash_xform (p x).
Proof.
(* original proof tokens: 34 *)
unfold piff.
split.
intros.
eapply pimpl_exists_l.
intros.
eapply pimpl_exists_r.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_forall_comm : forall T (p : T -> rawpred),
  crash_xform (foral x, p x) =p=> foral x, crash_xform (p x).
Proof.
(* original proof tokens: 32 *)
intros.
unfold crash_xform.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_ptsto: forall a v,
  crash_xform (a |-> v) =p=> exists v', [[ In v' (vsmerge v) ]] * a |=> v'.
Proof.
(* original proof tokens: 112 *)
unfold crash_xform.
intros.
unfold crash_xform.
unfold ptsto_subset.
unfold possible_crash.
unfold vsmerge.
unfold synced_mem.
unfold sync_mem.
unfold sync_xform.
unfold ptsto.
eapply pimpl_exists_r.
eexists.
apply pimpl_exists_l.
eapply pimpl_exists_l; eauto.
(* Reached max number of model calls *)
Admitted.

Theorem crash_xform_ptsto_r: forall a v vs,
  In v (vsmerge vs) ->
  a |=> v =p=> crash_xform (a |-> vs).
Proof.
(* original proof tokens: 91 *)
intros.
eapply pimpl_trans.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_ptsto_exis : forall a,
  crash_xform ( a |->? ) =p=> a |->?.
Proof.
(* original proof tokens: 75 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_ptsto_subset : forall a v,
  crash_xform (a |+> v) =p=> exists v', [[ In v' (vsmerge v) ]] * a |=> v'.
Proof.
(* original proof tokens: 134 *)
unfold crash_xform, ptsto_subset.
intros.
eapply pimpl_exists_l; intros.
eapply pimpl_exists_l; intros.
apply pimpl_exists_l.
eapply pimpl_trans.
eapply pimpl_trans2; [ apply pimpl_exists_l | ].
eapply pimpl_exists_l; eauto.
apply pimpl_refl.
apply pimpl_refl.
eapply pimpl_exists_l; [| eauto].
apply pimpl_exists_l.
eapply pimpl_exists_l; [| eauto].
apply pimpl_exists_l; auto.
(* Reached max number of model calls *)
Admitted.

Theorem crash_xform_ptsto_subset_r: forall a v vs,
  In v (vsmerge vs) ->
  a |=> v =p=> crash_xform (a |+> vs).
Proof.
(* original proof tokens: 96 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_pimpl : forall (p q : rawpred), p =p=>q
  -> crash_xform p =p=> crash_xform q.
Proof.
(* original proof tokens: 9 *)
intros.
eapply pimpl_pimpl_proper1; eauto.
(* No more tactics to try *)
Admitted.

Instance crash_xform_pimpl_proper:
  Proper (pimpl ==> pimpl) crash_xform.
Proof.
(* original proof tokens: 9 *)
intros p q H. unfold crash_xform. unfold pimpl. intros m H1.
eexists.
destruct H1.
(* No more tactics to try *)
Admitted.

Instance crash_xform_flip_pimpl_proper:
  Proper (Basics.flip pimpl ==> Basics.flip pimpl) crash_xform.
Proof.
(* original proof tokens: 9 *)
intros p q H. unfold crash_xform. unfold pimpl in *.  unfold Basics.flip.
intros m H0.
eexists; eauto.
(* No more tactics to try *)
Admitted.

Instance crash_xform_piff_proper:
  Proper (piff ==> piff) crash_xform.
Proof.
(* original proof tokens: 9 *)
intros p q H. unfold Proper, crash_xform. simpl. split; intros; subst.
(* No more tactics to try *)
Admitted.

Theorem crash_invariant_emp:
  crash_xform emp =p=> emp.
Proof.
(* original proof tokens: 49 *)
unfold crash_xform.
(* No more tactics to try *)
Admitted.

Theorem crash_invariant_emp_r:
  emp =p=> crash_xform emp.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Theorem crash_invariant_ptsto: forall a v,
  crash_xform (a |=> v) =p=> a |=> v.
Proof.
(* original proof tokens: 118 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_synced_valid:
  forall a v (F : rawpred) m,
  (a |=> v * F)%pred m
  -> m a = Some (v, nil).
Proof.
(* original proof tokens: 18 *)

(* No more tactics to try *)
Admitted.

Lemma ptsto_cur_valid:
  forall a v (F : rawpred) m,
  (a |~> v * F)%pred m
  -> exists l, m a = Some (v, l).
Proof.
(* original proof tokens: 44 *)
unfold ptsto_subset.
(* No more tactics to try *)
Admitted.

Lemma crash_xform_diskIs: forall m,
  crash_xform (diskIs m) =p=> exists m', [[ possible_crash m m' ]] * diskIs m'.
Proof.
(* original proof tokens: 76 *)
unfold crash_xform.
intros.
apply pimpl_exists_r.
exists m.
apply pimpl_exists_l.
intros.
(* No more tactics to try *)
Admitted.

Lemma crash_xform_diskIs_r: forall m m',
  possible_crash m m' ->
  diskIs m' =p=> crash_xform (diskIs m).
Proof.
(* original proof tokens: 25 *)

(* No more tactics to try *)
Admitted.

Lemma crash_xform_diskIs_piff: forall m,
  crash_xform (diskIs m) <=p=> exists m', [[ possible_crash m m' ]] * diskIs m'.
Proof.
(* original proof tokens: 52 *)
unfold piff.
split.
intros.
eapply pimpl_exists_r.
intros.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_mem_except : forall m1 m2 a,
  possible_crash m1 m2 ->
  possible_crash (mem_except m1 a) (mem_except m2 a).
Proof.
(* original proof tokens: 35 *)
intros.
unfold possible_crash.
intros a0.
destruct (H a0).
destruct H0.
right.
destruct H0; auto.
(* No more tactics to try *)
Admitted.

Lemma mem_except_upd : forall AT AEQ V (m : @mem AT AEQ V) a v,
  mem_except m a = mem_except (upd m a v) a.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_upd_mem_except : forall m1 m2 a v,
  possible_crash m1 (upd m2 a v) ->
  possible_crash (mem_except m1 a) (mem_except m2 a).
Proof.
(* original proof tokens: 32 *)
intros.
unfold possible_crash.
intros a0.
destruct (H a0).
destruct H0.
right.
inversion H0; subst.
(* No more tactics to try *)
Admitted.

Lemma possible_crash_eq : forall a b c,
  possible_crash a b ->
  possible_crash b c ->
  b = c.
Proof.
(* original proof tokens: 89 *)
intros a b c H1 H2.
(* No more tactics to try *)
Admitted.

Lemma crash_xform_diskIs_trans : forall d x d',
  crash_xform (diskIs d) x ->
  crash_xform (diskIs x) d' ->
  crash_xform (diskIs x) =p=> crash_xform (diskIs d).
Proof.
(* original proof tokens: 158 *)
intros.
eapply pimpl_trans2.
apply crash_xform_diskIs_r.
(* No more tactics to try *)
Admitted.

Lemma crash_xform_diskIs_eq : forall F a b,
  crash_xform F a ->
  crash_xform (diskIs a) b ->
  a = b.
Proof.
(* original proof tokens: 131 *)
intros.
inversion H0.
inversion H1.
inversion H0.
inversion H0.
inversion H0; inversion H1; subst; auto.
inversion H0; inversion H1; subst; auto.
inversion H0; inversion H1; subst; auto.
inversion H0; inversion H1; subst; auto.
inversion H0; inversion H1; subst; auto.
inversion H0; inversion H1; subst; auto.
inversion H0; inversion H1; subst; auto.
inversion H0; inversion H1; subst; auto.
inversion H0; inversion H; subst; auto.
inversion H0; inversion H; subst; auto.
inversion H0; inversion H; subst; auto.
inversion H0; inversion H; subst; auto.
inversion H0; inversion H; subst; auto.
inversion H0; inversion H; subst; auto.
(* Reached max number of model calls *)
Admitted.

Lemma crash_xform_diskIs_pred : forall (F : pred) m,
  F m -> crash_xform (diskIs m) =p=> crash_xform F.
Proof.
(* original proof tokens: 36 *)
(* generated proof tokens: 21 *)
intros.
apply crash_xform_pimpl.
apply diskIs_pred; auto.
Qed.

Lemma crash_xform_ptsto_or : forall (a : addr) (vs : valuset),
  crash_xform (a |-> vs) <=p=> crash_xform (a |-> vs \/ a |=> (fst vs)).
Proof.
(* original proof tokens: 102 *)
unfold crash_xform.
split.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
unfold crash_xform.
unfold impl.
intros.
apply pimpl_or_l.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
apply pimpl_or_l.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
unfold crash_xform.
unfold impl.
intros.
apply pimpl_or_l.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
apply pimpl_or_l.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
eapply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros.
apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros.
apply pimpl_or_l.
unfold crash_xform.
unfold impl.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros; apply pimpl_or_l; auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l.
auto.
intros.
apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros ; apply pimpl_or_l ;auto .
intros.
apply pimpl_or_l.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros; apply pimpl_or_l; auto.
intros; apply pimpl_or_l; auto.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros.
apply pimpl_or_l.
intros; apply pimpl_or_l; auto.
intros.
apply pimpl_or_l.
(* Reached max number of model calls *)
Admitted.

Lemma crash_xform_ptsto_vsmerge :  forall (a : addr) (vs : valuset) (v : valu),
  crash_xform (a |-> (v, vsmerge vs)) <=p=> crash_xform (a |-> vs \/ a |-> (v, vsmerge vs)).
Proof.
(* original proof tokens: 90 *)
split.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_idem_l : forall (p : rawpred), 
  crash_xform (crash_xform p) =p=> crash_xform p.
Proof.
(* original proof tokens: 39 *)
intros. unfold crash_xform. simpl. intros.
apply pimpl_exists_l.
intros. unfold crash_xform. simpl. intros.
intros. unfold pimpl. intros.
eexists; eauto.
destruct H as [? H].
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
apply pimpl_exists_l; auto.
eapply pimpl_exists_l; eauto.
apply pimpl_exists_l; auto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
eapply pimpl_exists_l; eauto.
eexists; eauto.
eexists.
eapply H0; eauto.
(* Reached max number of model calls *)
Admitted.

Theorem crash_xform_idem_r : forall (p : rawpred),
  crash_xform p =p=> crash_xform (crash_xform p).
Proof.
(* original proof tokens: 72 *)
intros. unfold crash_xform. simpl.
eapply pimpl_trans.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_idem : forall (p : rawpred),
  crash_xform (crash_xform p) <=p=> crash_xform p.
Proof.
(* original proof tokens: 26 *)
(* generated proof tokens: 33 *)

intros.
unfold piff.
split.
eapply crash_xform_idem_l.
eapply crash_xform_idem_r.
Qed.

Theorem crash_xform_synced : forall p m,
  crash_xform p m ->
  synced_mem m.
Proof.
(* original proof tokens: 30 *)
intros.
unfold crash_xform in H.
(* No more tactics to try *)
Admitted.

Theorem crash_xform_possible_crash_refl : forall p m,
  crash_xform p m ->
  possible_crash m m.
Proof.
(* original proof tokens: 28 *)
(* generated proof tokens: 38 *)
unfold crash_xform.
intros.
eapply possible_crash_refl; eauto.
eauto.
eapply crash_xform_synced; eauto.
Qed.

Hint Rewrite crash_xform_sep_star_dist : crash_xform.
Hint Rewrite crash_xform_or_dist : crash_xform.
Hint Rewrite crash_xform_exists_comm : crash_xform.
Hint Rewrite crash_xform_forall_comm : crash_xform.
Hint Rewrite crash_xform_lift_empty : crash_xform.
Hint Rewrite crash_xform_ptsto : crash_xform.
Hint Rewrite crash_xform_diskIs : crash_xform.
Hint Rewrite crash_invariant_ptsto : crash_xform.
Hint Resolve crash_invariant_emp.
Lemma pred_apply_crash_xform : forall (p : rawpred) m m',
  possible_crash m m' -> p m -> (crash_xform p) m'.
Proof.
(* original proof tokens: 17 *)
(* generated proof tokens: 19 *)

intros.
eapply crash_xform_apply; eauto.
Qed.

Lemma pred_apply_crash_xform_pimpl : forall (p q : rawpred) m m',
  possible_crash m m' -> p m -> crash_xform p =p=> q -> q m'.
Proof.
(* original proof tokens: 26 *)
intros.
apply H1; auto.
eapply pimpl_apply in H1; eauto.
eapply pimpl_fun_l.
(* No more tactics to try *)
Admitted.

Definition possible_sync AT AEQ (m m' : @mem AT AEQ valuset) :=
  forall a, (m a = None /\ m' a = None) \/
  (exists v l l', m a = Some (v, l) /\ m' a = Some (v, l') /\ incl l' l).
Theorem possible_sync_refl : forall AT AEQ (m: @mem AT AEQ _),
    possible_sync m m.
Proof.
(* original proof tokens: 28 *)

(* No more tactics to try *)
Admitted.

Theorem possible_sync_trans : forall AT AEQ (m1 m2 m3 : @mem AT AEQ _),
  possible_sync m1 m2 ->
  possible_sync m2 m3 ->
  possible_sync m1 m3.
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Theorem possible_sync_sync_mem : forall AT AEQ (m : @mem AT AEQ valuset),
  possible_sync m (sync_mem m).
Proof.
(* original proof tokens: 36 *)

(* No more tactics to try *)
Admitted.

Theorem possible_sync_after_sync : forall A AEQ (m m': @mem A AEQ _),
    possible_sync (sync_mem m) m' ->
    m' = sync_mem m.
Proof.
(* original proof tokens: 78 *)

(* No more tactics to try *)
Admitted.

Theorem possible_sync_upd : forall AT AEQ (m : @mem AT AEQ _) a v l l',
  m a = Some (v, l) ->
  incl l' l ->
  possible_sync m (upd m a (v, l')).
Proof.
(* original proof tokens: 84 *)

(* No more tactics to try *)
Admitted.

Ltac xform_simpl :=
  match goal with
  | [ |- pimpl (exis _) _ ] => apply pimpl_exists_l; intro
  end.
Ltac xform' := autorewrite with crash_xform; repeat xform_simpl.
Ltac xform := repeat xform'.
Definition sync_invariant (p : rawpred) :=
  (forall m m',
   possible_sync m m' ->
   p m -> p m').
Theorem sync_xform_sync_invariant : forall p,
  sync_invariant p ->
  sync_xform p =p=> p.
Proof.
(* original proof tokens: 39 *)
intros.
unfold sync_xform.
intros m Hm.
destruct Hm as [m' ?].
(* No more tactics to try *)
Admitted.

Theorem ptsto_pimpl_ptsto_subset : forall AT AEQ (a : AT) vs,
  ((a |-> vs) : @pred AT AEQ _) =p=> a |+> vs.
Proof.
(* original proof tokens: 41 *)

(* No more tactics to try *)
Admitted.

Theorem ptsto_subset_pimpl_ptsto_ex : forall AT AEQ (a : AT) vs,
  ((a |+> vs) : @pred AT AEQ _) =p=> a |->?.
Proof.
(* original proof tokens: 39 *)

(* No more tactics to try *)
Admitted.

Theorem ptsto_subset_pimpl_ptsto : forall AT AEQ (a : AT) v,
  ((a |+> (v, nil)) : @pred AT AEQ _) <=p=> a |=> v.
Proof.
(* original proof tokens: 88 *)
split; intros; subst; try (apply ptsto_subset_pimpl_ptsto).
(* No more tactics to try *)
Admitted.

Theorem ptsto_subset_pimpl : forall AT AEQ (a : AT) v l l',
  incl l l' ->
  ((a |+> (v, l)) : @pred AT AEQ _) =p=> a |+> (v, l').
Proof.
(* original proof tokens: 58 *)

(* No more tactics to try *)
Admitted.

Theorem crash_xform_ptsto_subset' : forall a v,
  crash_xform (a |+> v) =p=> exists v', [[ In v' (vsmerge v) ]] * a |+> (v', nil).
Proof.
(* original proof tokens: 47 *)
unfold crash_xform.
intros.
apply pimpl_exists_l; intro.
(* No more tactics to try *)
Admitted.

Theorem ptsto_sync_mem : forall (a : addr) (vs : valuset) v m,
  (a |-> vs)%pred m ->
  v = fst vs ->
  (a |-> (v, nil) : @pred _ addr_eq_dec _)%pred (sync_mem m).
Proof.
(* original proof tokens: 39 *)
intros.
unfold sync_mem.
rewrite H0.
simpl.
auto.
apply ptsto_subset_pimpl_ptsto.
(* No more tactics to try *)
Admitted.

Theorem possible_sync_ptsto : forall AT AEQ a v l (m m' : @mem AT AEQ _),
  possible_sync m m' ->
  (a |-> (v, l))%pred m ->
  (exists l', a |-> (v, l') * [[ incl l' l ]])%pred m'.
Proof.
(* original proof tokens: 99 *)

(* No more tactics to try *)
Admitted.

Theorem sync_invariant_ptsto_subset : forall a vs,
  sync_invariant (a |+> vs)%pred.
Proof.
(* original proof tokens: 97 *)
intros. unfold sync_invariant. unfold ptsto_subset. intros. unfold possible_sync in H. destruct (H a) as [H1 | H2].
(* No more tactics to try *)
Admitted.

Theorem sync_invariant_ptsto_any : forall a,
  sync_invariant (a |->?)%pred.
Proof.
(* original proof tokens: 63 *)
intros a. unfold sync_invariant. intros m m' Hsync H. unfold possible_sync in Hsync. destruct (Hsync a) as [H1|H2].
(* No more tactics to try *)
Admitted.

Theorem sync_xform_ptsto_subset_precise : forall a vs,
  sync_xform (a |+> vs) =p=> a |=> (fst vs).
Proof.
(* original proof tokens: 50 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_ptsto_subset_preserve : forall a vs,
  sync_xform (a |+> vs) =p=> a |+> vs.
Proof.
(* original proof tokens: 50 *)

(* No more tactics to try *)
Admitted.

Theorem sync_invariant_ptsto_nil : forall a v,
  sync_invariant (a |=> v)%pred.
Proof.
(* original proof tokens: 61 *)

(* No more tactics to try *)
Admitted.

Theorem sync_invariant_emp :
  sync_invariant emp.
Proof.
(* original proof tokens: 46 *)
intros.
unfold sync_invariant.
intros.
intros.
simpl in H0.
auto.
eapply possible_crash_emp_r; eauto.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_or_dist : forall p q,
  sync_xform (p \/ q) <=p=> sync_xform p \/ sync_xform q.
Proof.
(* original proof tokens: 9 *)
unfold piff.
unfold pimpl.
split.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_and_dist : forall p q,
  sync_xform (p /\ q) =p=> sync_xform p /\ sync_xform q.
Proof.
(* original proof tokens: 9 *)
intros.
unfold sync_xform.
intros.
unfold sync_xform.
split.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_lift_empty : forall (P : Prop),
  @sync_xform [[ P ]] <=p=> [[ P ]].
Proof.
(* original proof tokens: 64 *)
unfold piff.
split.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_emp :
  sync_xform emp <=p=> emp.
Proof.
(* original proof tokens: 73 *)
unfold piff.
split.
intros.
eapply pimpl_refl.
(* No more tactics to try *)
Admitted.

Lemma sync_mem_union : forall AT AEQ (m1 m2 : @mem AT AEQ _),
  sync_mem (mem_union m1 m2) = mem_union (sync_mem m1) (sync_mem m2).
Proof.
(* original proof tokens: 39 *)
unfold sync_mem, mem_union.
(* No more tactics to try *)
Admitted.

Lemma sync_mem_disjoint1 : forall AT AEQ (m1 m2 : @mem AT AEQ _),
  mem_disjoint m1 m2 -> mem_disjoint (sync_mem m1) (sync_mem m2).
Proof.
(* original proof tokens: 57 *)

(* No more tactics to try *)
Admitted.

Lemma sync_mem_disjoint2 : forall AT AEQ (m1 m2 : @mem AT AEQ _),
  mem_disjoint (sync_mem m1) (sync_mem m2) -> mem_disjoint m1 m2.
Proof.
(* original proof tokens: 49 *)

(* No more tactics to try *)
Admitted.

Hint Resolve sync_mem_disjoint1.
Hint Resolve sync_mem_disjoint2.
Hint Resolve sync_mem_union.
Theorem sync_xform_sep_star_dist : forall (p q : rawpred),
  sync_xform (p * q) <=p=> sync_xform p * sync_xform q.
Proof.
(* original proof tokens: 70 *)
unfold piff.
split.
intros.
unfold sync_xform.
intros m H.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_exists_comm : forall T (p : T -> rawpred),
  sync_xform (exists x, p x) <=p=> exists x, sync_xform (p x).
Proof.
(* original proof tokens: 34 *)
split.
intros.
unfold sync_xform.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_forall_comm : forall T (p : T -> rawpred),
  sync_xform (foral x, p x) =p=> foral x, sync_xform (p x).
Proof.
(* original proof tokens: 32 *)
intros.
unfold sync_xform.
unfold pimpl.
intros.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_pimpl : forall p q,
  p =p=> q ->
  sync_xform p =p=> sync_xform q.
Proof.
(* original proof tokens: 23 *)
intros.
unfold sync_xform.
unfold pimpl.
intros.
eexists; eauto.
eexists; eauto.
destruct H0.
(* No more tactics to try *)
Admitted.

Instance sync_xform_pimpl_proper:
  Proper (pimpl ==> pimpl) sync_xform.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance sync_xform_flip_pimpl_proper:
  Proper (Basics.flip pimpl ==> Basics.flip pimpl) sync_xform.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance sync_xform_piff_proper:
  Proper (piff ==> piff) sync_xform.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Instance sync_invariant_piff_proper:
  Proper (piff ==> Basics.impl) sync_invariant.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Theorem sync_xform_diskIs: forall m,
  sync_xform (diskIs m) =p=> diskIs (sync_mem m).
Proof.
(* original proof tokens: 25 *)
intros.
unfold sync_xform.
(* No more tactics to try *)
Admitted.

Theorem sync_xform_pred_apply : forall (p : rawpred) m,
  p m -> (sync_xform p) (sync_mem m).
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Theorem sync_mem_idem : forall AT AEQ (m : @mem AT AEQ _),
  sync_mem (sync_mem m) = sync_mem m.
Proof.
(* original proof tokens: 35 *)

(* No more tactics to try *)
Admitted.

Theorem sync_xform_idem : forall p,
  sync_xform (sync_xform p) <=p=> sync_xform p.
Proof.
(* original proof tokens: 61 *)
unfold piff.
split.
(* No more tactics to try *)
Admitted.

Theorem sync_invariant_exists : forall T (p : T -> rawpred),
  (forall v, sync_invariant (p v)) ->
  sync_invariant (exists v, p v)%pred.
Proof.
(* original proof tokens: 24 *)

(* No more tactics to try *)
Admitted.

Theorem possible_sync_mem_union : forall AT AEQ (ma mb m' : @mem AT AEQ _),
  possible_sync (mem_union ma mb) m'
  -> @mem_disjoint _ _ _ ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_sync ma ma' /\ possible_sync mb mb'.
Proof.
(* original proof tokens: 369 *)
unfold possible_sync.
(* No more tactics to try *)
Admitted.

Theorem possible_sync_disjoint : forall AT AEQ (ma mb ma' mb' : @mem AT AEQ _),
  @mem_disjoint _ _ _ ma' mb'
  -> possible_sync ma ma'
  -> possible_sync mb mb'
  -> @mem_disjoint _ _ _ ma mb.
Proof.
(* original proof tokens: 61 *)
intros.
unfold mem_disjoint in *.
intros Hcontra.
(* No more tactics to try *)
Admitted.

Theorem possible_sync_union : forall AT AEQ (ma mb ma' mb' : @mem AT AEQ _), possible_sync ma ma'
  -> possible_sync mb mb'
  -> possible_sync (mem_union ma mb) (mem_union ma' mb').
Proof.
(* original proof tokens: 177 *)

(* No more tactics to try *)
Admitted.

Theorem sync_invariant_sep_star : forall p q,
  sync_invariant p ->
  sync_invariant q ->
  sync_invariant (p * q)%pred.
Proof.
(* original proof tokens: 49 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem sync_invariant_lift_empty : forall P,
  sync_invariant [[ P ]]%pred.
Proof.
(* original proof tokens: 60 *)
intros. unfold sync_invariant. unfold lift_empty. intros. simpl. split; auto.
destruct H0.
auto.
inversion H0.
intros a.
(* No more tactics to try *)
Admitted.

Theorem sync_invariant_and : forall p q,
  sync_invariant p ->
  sync_invariant q ->
  sync_invariant (p /\ q)%pred.
Proof.
(* original proof tokens: 9 *)
intros p q Hinvp Hinvq. unfold sync_invariant. intros m m' Hsync pm.
apply conj; auto.
destruct pm.
(* No more tactics to try *)
Admitted.

Theorem sync_invariant_or : forall p q,
  sync_invariant p ->
  sync_invariant q ->
  sync_invariant (p \/ q)%pred.
Proof.
(* original proof tokens: 9 *)

(* No more tactics to try *)
Admitted.

Lemma possible_sync_possible_crash_trans : forall m m1 m2,
  possible_crash m m1 ->
  possible_sync m1 m2 ->
  possible_crash m m2.
Proof.
(* original proof tokens: 85 *)
intros.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
eapply possible_crash_trans; eauto.
(* No more tactics to try *)
Admitted.

Lemma incl_vsmerge : forall l l' v,
    incl l l' ->
    incl (vsmerge (v, l)) (vsmerge (v, l')).
Proof.
(* original proof tokens: 73 *)

(* No more tactics to try *)
Admitted.

Lemma possible_crash_possible_sync_trans : forall m m1 m2,
    possible_sync m m1 ->
    possible_crash m1 m2 ->
    possible_crash m m2.
Proof.
(* original proof tokens: 77 *)

(* No more tactics to try *)
Admitted.

Theorem sync_invariant_crash_xform : forall F,
  sync_invariant (crash_xform F).
Proof.
(* original proof tokens: 42 *)
intros. unfold sync_invariant. intros. unfold possible_sync in H. unfold crash_xform in H0. simpl in *.
exists m'.
inversion H0.
split.
inversion H1.
destruct H1.
destruct H0.
destruct H0.
(* No more tactics to try *)
Admitted.

Hint Resolve sync_invariant_ptsto_subset.
Hint Resolve sync_invariant_ptsto_any.
Hint Resolve sync_invariant_ptsto_nil.
Hint Resolve sync_invariant_emp.
Hint Resolve sync_invariant_exists.
Hint Resolve sync_invariant_sep_star.
Hint Resolve sync_invariant_lift_empty.
Hint Resolve sync_invariant_and.
Hint Resolve sync_invariant_or.
Hint Resolve sync_invariant_crash_xform.
Theorem upd_sync_invariant : forall (p : @pred _ _ _) m a v l l',
  sync_invariant p ->
  p m ->
  m a = Some (v, l) ->
  incl l' l ->
  p (upd m a (v, l')).
Proof.
(* original proof tokens: 27 *)
intros.
eapply H; eauto.
(* No more tactics to try *)
Admitted.

Theorem ptsto_subset_valid : forall AT AEQ a vs F (m : @mem AT AEQ _),
  (a |+> vs * F)%pred m ->
  exists l, m a = Some (fst vs, l) /\ incl l (snd vs).
Proof.
(* original proof tokens: 63 *)
unfold ptsto_subset.
(* No more tactics to try *)
Admitted.

Theorem ptsto_subset_valid' : forall AT AEQ a vs F (m : @mem AT AEQ _),
  (F * a |+> vs)%pred m ->
  exists l, m a = Some (fst vs, l) /\ incl l (snd vs).
Proof.
(* original proof tokens: 27 *)
unfold ptsto_subset.
intros.
(* No more tactics to try *)
Admitted.

Lemma ptsto_subset_upd : forall v0 v a m vs vs' vs0 (F : rawpred),
  (F * a |+> (v0, vs0))%pred m ->
  incl vs' vs ->
  (F * a |+> (v, vs))%pred (upd m a (v, vs')).
Proof.
(* original proof tokens: 155 *)
intros.
(* No more tactics to try *)
Admitted.

