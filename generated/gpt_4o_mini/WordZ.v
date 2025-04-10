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
(* original proof tokens: 43 *)

(* No more tactics to try *)
Admitted.

Theorem ZToWordTrunc_wordToZ : forall sz w,
  ZToWordTrunc sz (wordToZ w) = w.
Proof.
(* original proof tokens: 80 *)

(* No more tactics to try *)
Admitted.

Lemma Z_pow_Npow2 : forall p,
  Z.pow 2 (Z.of_nat p) = Z.of_N (Npow2 p).
Proof.
(* original proof tokens: 116 *)

(* No more tactics to try *)
Admitted.

Theorem wordToZ_ZToWordTrunc_idempotent : forall sz z,
  (0 <= z < (2 ^ (Z.of_nat sz)))%Z -> wordToZ (ZToWordTrunc sz z) = z.
Proof.
(* original proof tokens: 115 *)

(* No more tactics to try *)
Admitted.

Lemma wordToZ_bound : forall sz (w : word sz),
  (0 <= wordToZ w < (2 ^ (Z.of_nat sz)))%Z.
Proof.
(* original proof tokens: 85 *)

(* No more tactics to try *)
Admitted.

Theorem ZToWord_wordToZ : forall sz w,
  ZToWord sz (wordToZ w) = Some w.
Proof.
(* original proof tokens: 126 *)

(* No more tactics to try *)
Admitted.

Theorem wordToZ_ZToWord : forall sz w z,
  ZToWord sz z = Some w ->
  wordToZ w = z.
Proof.
(* original proof tokens: 167 *)

(* No more tactics to try *)
Admitted.

