Require Import Arith Lia NArith.
Local Open Scope N_scope.
Hint Rewrite Nplus_0_r nat_of_Nsucc nat_of_Nplus nat_of_Nminus
  N_of_nat_of_N nat_of_N_of_nat
  Pnat.nat_of_P_o_P_of_succ_nat_eq_succ Pnat.nat_of_P_succ_morphism : N.
Theorem nat_of_N_eq : forall n m,
  nat_of_N n = nat_of_N m
  -> n = m.
Proof.
(* original proof tokens: 32 *)
(* generated proof tokens: 18 *)
intro n.
intro m.
apply N2Nat.inj.
Qed.

Theorem Nneq_in : forall n m,
  nat_of_N n <> nat_of_N m
  -> n <> m.
Proof.
(* original proof tokens: 10 *)

(* No more tactics to try *)
Admitted.

Theorem Nneq_out : forall n m,
  n <> m
  -> nat_of_N n <> nat_of_N m.
Proof.
(* original proof tokens: 8 *)
intros n m H.
(* No more tactics to try *)
Admitted.

Theorem Nlt_out : forall n m, n < m
  -> (nat_of_N n < nat_of_N m)%nat.
Proof.
(* original proof tokens: 31 *)

(* No more tactics to try *)
Admitted.

Theorem Nlt_in : forall n m, (nat_of_N n < nat_of_N m)%nat
  -> n < m.
Proof.
(* original proof tokens: 33 *)

(* No more tactics to try *)
Admitted.

Theorem Nge_out : forall n m, n >= m
  -> (nat_of_N n >= nat_of_N m)%nat.
Proof.
(* original proof tokens: 29 *)

(* No more tactics to try *)
Admitted.

Theorem Nge_in : forall n m, (nat_of_N n >= nat_of_N m)%nat
  -> n >= m.
Proof.
(* original proof tokens: 27 *)

(* No more tactics to try *)
Admitted.

Ltac nsimp H := simpl in H; repeat progress (autorewrite with N in H; simpl in H).
