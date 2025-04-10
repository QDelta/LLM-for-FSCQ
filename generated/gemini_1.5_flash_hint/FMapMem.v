Require Import List.
Require Import FMapFacts.
Require Import Lia.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import MapUtils.
Require Import Mem.
Require Import Pred.
Require Import FunctionalExtensionality.
Module MapMem (OT : UsualOrderedType) (M : S with Module E := OT).
Module Map := M.
Module Defs := MapDefs OT.
Section MapMemSec.
Variable V : Type.
Definition mem_type := @mem Map.key OT.eq_dec V.
Definition mm (m : Map.t V) : mem_type := fun a => Map.find a m.
Lemma find_add_eq : forall m a (v : V),
      Map.find a (Map.add a v m) = Some v.
Proof.
(* original proof tokens: 32 *)

(* No more tactics to try *)
Admitted.

Lemma find_add_ne : forall m a a' (v : V),
      a <> a' -> Map.find a (Map.add a' v m) = Map.find a m.
(* hint proof tokens: 141 *)
Proof.
      intros.
      case_eq (Map.find a (Map.add a' v m)); intros.
      - apply M.find_2 in H0.
        eapply M.add_3 in H0; [| congruence ].
        erewrite M.find_1 with (e := v0); auto.
      - case_eq (Map.find a m); intros; eauto.
        eapply M.find_2 in H1.
        eapply M.add_2 with (x := a') (e' := v) in H1.
        eapply M.find_1 in H1; congruence.
        congruence.
    Qed.
Lemma find_remove_eq : forall m a,
      @Map.find V a (Map.remove a m) = None.
(* hint proof tokens: 62 *)
Proof.
      intros.
      case_eq (Map.find a (Map.remove a m)); eauto; intros.
      apply M.find_2 in H.
      exfalso.
      eapply M.remove_1; unfold M.In; try eauto.
      reflexivity.
    Qed.
Lemma find_remove_ne : forall m a a',
      a <> a' -> @Map.find V a (Map.remove a' m) = Map.find a m.
Proof.
(* original proof tokens: 121 *)

(* No more tactics to try *)
Admitted.

Theorem mm_init :
      @emp _ OT.eq_dec _ (mm (Map.empty _)).
(* hint proof tokens: 56 *)
Proof.
      unfold emp, mm; intros.
      case_eq (Map.find a (Map.empty V)); intros; auto.
      apply M.find_2 in H.
      exfalso.
      eapply M.empty_1; eauto.
    Qed.
Theorem mm_add : forall m (F : @pred Map.key OT.eq_dec V) a v,
      Map.find a m = None ->
      F (mm m) ->
      (F * a |-> v)%pred (mm (Map.add a v m)).
(* hint proof tokens: 184 *)
Proof.
      unfold_sep_star; intros; repeat deex.
      exists (mm m).
      unfold mm in *.
      exists (fun a' => if OT.eq_dec a' a then Some v else None).
      split; [|split].
      - apply functional_extensionality; intro.
        unfold mem_union; destruct (OT.eq_dec x a); unfold OT.eq in *; subst.
        rewrite find_add_eq; rewrite H; auto.
        rewrite find_add_ne by auto.
        destruct (Map.find x m); auto.
      - unfold mem_disjoint in *. intuition. repeat deex.
        destruct (OT.eq_dec a0 a); subst; intuition; pred.
      - intuition; eauto.
        unfold ptsto; intuition.
        destruct (OT.eq_dec a a); pred.
        destruct (OT.eq_dec a' a); pred.
    Qed.
Theorem mm_replace : forall m (F : @pred Map.key OT.eq_dec V) a v0 v,
      (a |-> v0 * F)%pred (mm m) ->
      (a |-> v * F)%pred (mm (Map.add a v m)).
(* hint proof tokens: 246 *)
Proof.
      unfold_sep_star; intros; repeat deex.
      exists (fun a' => if OT.eq_dec a' a then Some v else None).
      exists m2.
      unfold mm in *.
      split; [|split].
      - apply functional_extensionality; intro.
        unfold mem_union; destruct (OT.eq_dec x a); unfold OT.eq in *; subst; eauto.
        rewrite find_add_eq; eauto.
        rewrite find_add_ne by auto.
        destruct H1; repeat deex.
        apply equal_f with (x := x) in H0; rewrite H0.
        unfold mem_union. rewrite H2; auto.
      - unfold mem_disjoint in *. intuition. repeat deex.
        apply H.
        destruct H1; repeat deex.
        repeat eexists; eauto.
        destruct (OT.eq_dec a0 a); unfold OT.eq in *; subst; eauto.
        pred.
      - intuition eauto.
        unfold ptsto; intuition; unfold OT.eq in *.
        destruct (OT.eq_dec a a); pred.
        destruct (OT.eq_dec a' a); pred.
    Qed.
Theorem mm_remove : forall m (F : @pred Map.key OT.eq_dec V) a v,
      (a |-> v * F)%pred (mm m) ->
      F (mm (Map.remove a m)).
Proof.
(* original proof tokens: 200 *)
unfold_sep_star;intros;pred.
(* No more tactics to try *)
Admitted.

Theorem mm_remove_none : forall m (F : @pred Map.key OT.eq_dec V) a,
      Map.find a m = None ->
      F (mm m) ->
      F (mm (Map.remove a m)).
Proof.
(* original proof tokens: 100 *)
intros.
(* No more tactics to try *)
Admitted.

Theorem mm_find : forall m (F : @pred Map.key OT.eq_dec V) a v,
      (a |-> v * F)%pred (mm m) ->
      Map.find a m = Some v.
(* hint proof tokens: 47 *)
Proof.
      unfold ptsto, mm; unfold_sep_star.
      intros; repeat deex.
      eapply equal_f in H0; rewrite H0.
      apply mem_union_addr; eauto.
    Qed.
Theorem mm_add_upd: forall k v m,
    mm (Map.add k v m) = Mem.upd (mm m) k v.
Proof.
(* original proof tokens: 63 *)
unfold mm, upd; intros.
apply functional_extensionality; intros.
(* No more tactics to try *)
Admitted.

End MapMemSec.
End MapMem.
