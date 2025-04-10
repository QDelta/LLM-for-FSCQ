Require Import Word.
Require Import ZArith.
Require Import Lia.
Set Implicit Arguments.
Definition wordToZ sz (w : word sz) : Z := Z.of_N (wordToN w).
Definition ZToWordTrunc sz (z : Z) : word sz :=
  match z with
  | Z0 => $0
  | Zpos p => posToWord sz p
  | Zneg p => wneg (posToWord sz p)
  end.
Definition ZToWord sz (z : Z) : option (word sz) :=
  match z with
  | Z0 => Some $0
  | Zpos p =>
    match Z.compare z (2 ^ (Z.of_nat sz))%Z with
    | Lt => Some (posToWord sz p)
    | _ => None
    end
  | Zneg p => None
  end.
Theorem wordToZ_nat : forall sz (w : word sz), wordToZ w = Z_of_nat (wordToNat w).
Proof.
(* skipped proof tokens: 43 *)
Admitted.
Theorem ZToWordTrunc_wordToZ : forall sz w,
  ZToWordTrunc sz (wordToZ w) = w.
Proof.
(* skipped proof tokens: 80 *)
Admitted.
Lemma Z_pow_Npow2 : forall p,
  Z.pow 2 (Z.of_nat p) = Z.of_N (Npow2 p).
Proof.
(* skipped proof tokens: 116 *)
Admitted.
Theorem wordToZ_ZToWordTrunc_idempotent : forall sz z,
  (0 <= z < (2 ^ (Z.of_nat sz)))%Z -> wordToZ (ZToWordTrunc sz z) = z.
Proof.
(* skipped proof tokens: 115 *)
Admitted.
Lemma wordToZ_bound : forall sz (w : word sz),
  (0 <= wordToZ w < (2 ^ (Z.of_nat sz)))%Z.
Proof.
(* skipped proof tokens: 85 *)
Admitted.
Theorem ZToWord_wordToZ : forall sz w,
  ZToWord sz (wordToZ w) = Some w.
Proof.
(* skipped proof tokens: 126 *)
Admitted.
Theorem wordToZ_ZToWord : forall sz w z,
  ZToWord sz z = Some w ->
  wordToZ w = z.
Proof.
(* skipped proof tokens: 167 *)
Admitted.
