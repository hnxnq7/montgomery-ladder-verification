From Stdlib Require Import ZArith Lia.
From Crypto Require Import Spec.ModularArithmetic.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import fiat_field cube_encoding field_aggregate_spectral curve_snapshot noisy_leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module Curve25519Snapshot.

Lemma power_to_nat k : Z.to_nat (Z.pow 2 (Z.of_nat k)) = (2 ^ k)%N.
Proof.
  rewrite (Z2Nat.inj_pow 2 (Z.of_nat k) ltac:(lia) (Nat2Z.is_nonneg k)).
  change (Nat.pow 2 (Z.to_nat (Z.of_nat k)) = (2 ^ k)%N).
  by rewrite Nat2Z.id -CubeEncoding.expn_nat.
Qed.

(* This conversion compares binary integers only, never unary natural powers. *)
Lemma modulus_Z : Z.pos FiatField.curve25519_modulus = Z.sub (Z.pow 2 255) 19.
Proof. reflexivity. Qed.

Lemma modulus_nat :
  Z.to_nat (Z.pos FiatField.curve25519_modulus) = (2 ^ 255 - 19)%N.
Proof.
  rewrite modulus_Z (Z2Nat.inj_sub (Z.pow 2 255) 19 ltac:(lia)).
  change (Nat.sub (Z.to_nat (Z.pow 2 (Z.of_nat 255))) 19 = (2 ^ 255 - 19)%N).
  by rewrite power_to_nat minusE.
Qed.

Definition law n (R : realType) (s : FiatField.curve25519) :=
  @FieldAggregateSpectral.law FiatField.curve25519_modulus
    FiatField.curve25519_modulus_gt1 255 n R s.

Section Bound.
Variable n : nat.
Hypothesis shares : (1 <= n)%N.
Variable R : realType.
Local Notation K := FiatField.curve25519.
Local Notation M := (255 * n.+1).+1%N.

Theorem actual_TV_squared (s1 s2 : K) :
  NoisyLeakage.TV (law n R s1) (law n R s2)^+2 <= @ratr R (CurveSnapshot.squared_budget n).
Proof.
  exact: (@CurveSnapshot.actual_TV_squared FiatField.curve25519_modulus
    FiatField.curve25519_modulus_gt1 modulus_nat n shares R s1 s2).
Qed.

Theorem actual_TV_bound (epsilon : R) (s1 s2 : K) :
  0 <= epsilon -> @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2 ->
  NoisyLeakage.bounded_indistinguishable epsilon (law n R s1) (law n R s2).
Proof.
  exact: (@CurveSnapshot.actual_TV_bound FiatField.curve25519_modulus
    FiatField.curve25519_modulus_gt1 modulus_nat n shares R epsilon s1 s2).
Qed.

Theorem noisy_TV_squared (O : finType) (channel : 'I_M -> R.-fdist O) (s1 s2 : K) :
  NoisyLeakage.TV (law n R s1 >>= channel) (law n R s2 >>= channel)^+2 <=
    @ratr R (CurveSnapshot.squared_budget n).
Proof.
  exact: (@CurveSnapshot.noisy_TV_squared FiatField.curve25519_modulus
    FiatField.curve25519_modulus_gt1 modulus_nat n shares R O channel s1 s2).
Qed.

Theorem noisy_TV_bound (O : finType) (channel : 'I_M -> R.-fdist O)
    (epsilon : R) (s1 s2 : K) :
  0 <= epsilon -> @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2 ->
  NoisyLeakage.bounded_indistinguishable epsilon
    (law n R s1 >>= channel) (law n R s2 >>= channel).
Proof.
  exact: (@CurveSnapshot.noisy_TV_bound FiatField.curve25519_modulus
    FiatField.curve25519_modulus_gt1 modulus_nat n shares R O channel epsilon s1 s2).
Qed.

End Bound.

End Curve25519Snapshot.

Print Assumptions Curve25519Snapshot.modulus_nat.
Print Assumptions Curve25519Snapshot.actual_TV_squared.
Print Assumptions Curve25519Snapshot.noisy_TV_squared.
