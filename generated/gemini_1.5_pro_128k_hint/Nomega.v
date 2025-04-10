Require Import Arith Lia NArith.
Local Open Scope N_scope.
Hint Rewrite Nplus_0_r nat_of_Nsucc nat_of_Nplus nat_of_Nminus
  N_of_nat_of_N nat_of_N_of_nat
  Pnat.nat_of_P_o_P_of_succ_nat_eq_succ Pnat.nat_of_P_succ_morphism : N.
Theorem nat_of_N_eq : forall n m,
  nat_of_N n = nat_of_N m
  -> n = m.
Proof.
(* skipped proof tokens: 32 *)
Admitted.
Theorem Nneq_in : forall n m,
  nat_of_N n <> nat_of_N m
  -> n <> m.
Proof.
(* skipped proof tokens: 10 *)
Admitted.
Theorem Nneq_out : forall n m,
  n <> m
  -> nat_of_N n <> nat_of_N m.
(* hint proof tokens: 8 *)
Proof.
  lia.
Qed.
Theorem Nlt_out : forall n m, n < m
  -> (nat_of_N n < nat_of_N m)%nat.
(* hint proof tokens: 31 *)
Proof.
  unfold N.lt; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_Lt_lt; assumption.
Qed.
Theorem Nlt_in : forall n m, (nat_of_N n < nat_of_N m)%nat
  -> n < m.
Proof.
(* skipped proof tokens: 33 *)
Admitted.
Theorem Nge_out : forall n m, n >= m
  -> (nat_of_N n >= nat_of_N m)%nat.
(* hint proof tokens: 29 *)
Proof.
  unfold N.ge; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_ge; assumption.
Qed.
Theorem Nge_in : forall n m, (nat_of_N n >= nat_of_N m)%nat
  -> n >= m.
(* hint proof tokens: 27 *)
Proof.
  unfold N.ge; intros.
  rewrite nat_of_Ncompare.
  apply nat_compare_ge; assumption.
Qed.
Ltac nsimp H := simpl in H; repeat progress (autorewrite with N in H; simpl in H).
