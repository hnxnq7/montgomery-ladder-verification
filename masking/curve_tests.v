From Stdlib Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Crypto Require Import Spec.ModularArithmetic Spec.Curve25519.
From Masking Require Import finite_masking shared_power shared_loop fiat_field ladder_bridge masked_curve25519.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section Boundaries.
Variable R : realType.
Local Notation K := FiatField.curve25519.

Example zero_width_reconstructs_zero (xp : K) :
  fdistmap (@reconstruct K)
    (SharedLoop.program R MaskedCurve25519.inverse_exponent 0 0 xp (fun _ => false)) = fdist1 0.
Proof.
rewrite SharedLoop.program_correct.
change (@fdist1 R K (1 * SharedPower.clear_power MaskedCurve25519.inverse_exponent 0) = fdist1 0).
by rewrite SharedPower.clear_power_zero mulr0.
Qed.

Example zero_scalar_correct (P : Curve25519.M.point) :
  fdistmap (@reconstruct K)
    (MaskedCurve25519.program R 255 (F.to_Z (Curve25519.M.X0 P)) 0) =
  @fdist1 R K (Curve25519.M.X0 (Curve25519.M.scalarmult 0 P)).
Proof.
apply: MaskedCurve25519.program_correct.
split; [lia | apply Z.pow_pos_nonneg; lia].
Qed.

Example full_width_correct_and_output_independent (P : Curve25519.M.point) n1 n2 :
  (0 <= n1 < 2 ^ 255)%Z -> (0 <= n2 < 2 ^ 255)%Z ->
  fdistmap (@reconstruct K) (MaskedCurve25519.program R 255 (F.to_Z (Curve25519.M.X0 P)) n1) =
    @fdist1 R K (Curve25519.M.X0 (Curve25519.M.scalarmult n1 P)) /\
  fdistmap (@reconstruct K) (MaskedCurve25519.program R 255 (F.to_Z (Curve25519.M.X0 P)) n2) =
    @fdist1 R K (Curve25519.M.X0 (Curve25519.M.scalarmult n2 P)) /\
  fdistmap snd (MaskedCurve25519.program R 255 (F.to_Z (Curve25519.M.X0 P)) n1) =
    fdistmap snd (MaskedCurve25519.program R 255 (F.to_Z (Curve25519.M.X0 P)) n2).
Proof. exact (@MaskedCurve25519.correct_and_output_independent R 255 P n1 n2). Qed.

End Boundaries.

Print Assumptions FiatField.ordinal_cancel.
Print Assumptions LadderBridge.projective_matches_math.
Print Assumptions SharedPower.power_correct.
Print Assumptions SharedLoop.projective_correct.
Print Assumptions MaskedCurve25519.inverse_matches_math.
Print Assumptions MaskedCurve25519.program_correct.
Print Assumptions MaskedCurve25519.correct_and_output_independent.
