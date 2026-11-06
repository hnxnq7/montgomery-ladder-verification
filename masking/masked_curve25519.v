From Stdlib Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Crypto Require Import Spec.Curve25519 Arithmetic.PrimeFieldTheorems.
Require Import ladder_math curve25519_math.
From Masking Require Import finite_masking shared_power shared_loop fiat_field ladder_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module MaskedCurve25519.
Local Notation K := FiatField.curve25519.
Local Notation q := FiatField.curve25519_modulus.
Local Notation encode := (FiatField.encode FiatField.curve25519_modulus_gt1).

Definition inverse_exponent : positive :=
  (2 ^ 255 - 21)%positive.

Lemma projective_matches_math m xp n :
  LadderBridge.encode_pair encode (MontLadderCSwap (Z.pos q) 121666 m xp n) =
  SharedLoop.clear_projective m (encode 121666) (encode xp) (fun i => bit_i n i).
Proof.
apply: LadderBridge.projective_matches_math.
- exact: FiatField.encode_zero.
- exact: FiatField.encode_one.
- exact: FiatField.encode_add.
- exact: FiatField.encode_sub.
- exact: FiatField.encode_mul.
- exact: FiatField.encode_mod.
Qed.

Lemma inverse_matches_math x :
  SharedPower.clear_power inverse_exponent (encode x) = F.inv (encode x).
Proof.
rewrite (@LadderBridge.power_matches_math K encode (FiatField.encode_mul _) inverse_exponent x).
rewrite (@F.Fq_inv_fermat q Curve25519.prime_p ltac:(vm_compute; reflexivity)).
rewrite F.of_Z_pow.
change (F.of_Z q (x ^ Z.pos inverse_exponent) =
  F.of_Z q ((x ^ Z.pos inverse_exponent) mod Z.pos q))%Z.
exact: F.of_Z_mod.
Qed.

Lemma affine_matches_math m xp n :
  SharedLoop.clear_affine inverse_exponent m (encode 121666) (encode xp) (fun i => bit_i n i) =
  Curve25519Bridge.affine_output q (MontLadderCSwap (Z.pos q) 121666 m xp n).
Proof.
rewrite /SharedLoop.clear_affine -projective_matches_math.
case: (MontLadderCSwap (Z.pos q) 121666 m xp n) => X Zc.
change (encode X * SharedPower.clear_power inverse_exponent (encode Zc) =
  F.mul (encode X) (F.inv (encode Zc))).
by rewrite inverse_matches_math.
Qed.

Section Distribution.
Variable R : realType.

Definition program (m : nat) (xp n : Z) :=
  SharedLoop.program R inverse_exponent m (encode 121666) (encode xp) (fun i => bit_i n i).

Theorem program_correct m n (P : Curve25519.M.point) :
  (0 <= n < 2 ^ Z.of_nat m)%Z ->
  fdistmap (@reconstruct K) (program m (F.to_Z (Curve25519.M.X0 P)) n) =
  @fdist1 R K (Curve25519.M.X0 (Curve25519.M.scalarmult n P)).
Proof.
move=> Hn; rewrite /program SharedLoop.program_correct affine_matches_math.
congr (fdist1 _); apply/(proj2 (F.eq_to_Z_iff _ _)).
exact: Curve25519Bridge.curve25519_cswap_correct Hn.
Qed.

Theorem output_uniform m xp n :
  fdistmap snd (program m xp n) = uniform R K.
Proof. exact: SharedLoop.output_uniform. Qed.

Theorem output_independent m xp n1 n2 :
  fdistmap snd (program m xp n1) = fdistmap snd (program m xp n2).
Proof. by rewrite !output_uniform. Qed.

(* Correct reconstruction and secrecy of final Y; no execution trace is observed. *)
Theorem correct_and_output_independent m (P : Curve25519.M.point) n1 n2 :
  (0 <= n1 < 2 ^ Z.of_nat m)%Z ->
  (0 <= n2 < 2 ^ Z.of_nat m)%Z ->
  fdistmap (@reconstruct K) (program m (F.to_Z (Curve25519.M.X0 P)) n1) =
    @fdist1 R K (Curve25519.M.X0 (Curve25519.M.scalarmult n1 P)) /\
  fdistmap (@reconstruct K) (program m (F.to_Z (Curve25519.M.X0 P)) n2) =
    @fdist1 R K (Curve25519.M.X0 (Curve25519.M.scalarmult n2 P)) /\
  fdistmap snd (program m (F.to_Z (Curve25519.M.X0 P)) n1) =
    fdistmap snd (program m (F.to_Z (Curve25519.M.X0 P)) n2).
Proof.
move=> H1 H2; split; first exact: program_correct H1.
split; [exact: program_correct H2 | exact: output_independent].
Qed.

End Distribution.
End MaskedCurve25519.
