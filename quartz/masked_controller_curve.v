From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import masked_controller masked_controller_program masked_controller_schedule
  masked_controller_loop masked_controller_functional.
From Masking Require Import fiat_field shared_loop masked_curve25519.
From Crypto Require Import Spec.Curve25519 Arithmetic.PrimeFieldTheorems.
From Stdlib Require Import ZArith Bits Lia.
Require Import ladder_math curve25519_math.

Module MaskedControllerCurve.
Module C := MaskedController.
Module P := MaskedControllerProgram.
Module S := MaskedControllerSchedule.
Module L := MaskedControllerLoop.
Module F := MaskedControllerFunctional.
Local Open Scope Z_scope.

Definition load (point : Curve25519.M.point) (scalar : Z) : type.interp C.Load :=
  (bits.of_Z 255 (F.to_Z (Curve25519.M.X0 point)),bits.of_Z 255 scalar).

Lemma coordinate_range (point : Curve25519.M.point) :
  0 <= F.to_Z (Curve25519.M.X0 point) < 2^255.
Proof.
  have H := F.to_Z_range (Curve25519.M.X0 point) (Pos2Z.is_pos _).
  change (0 <= F.to_Z (Curve25519.M.X0 point) < 2^255-19) in H. lia.
Qed.

Lemma load_coordinate point scalar :
  C.M.decode_word (load point scalar).1 =
  FiatField.encode FiatField.curve25519_modulus_gt1 (F.to_Z (Curve25519.M.X0 point)).
Proof.
  unfold load, C.M.decode_word. cbn [fst].
  rewrite (bits.unsigned_of_Z_small _ (coordinate_range point)). reflexivity.
Qed.

Lemma load_scalar point scalar : 0 <= scalar < 2^255 ->
  Zmod.unsigned (load point scalar).2 = scalar.
Proof. intro H. exact (bits.unsigned_of_Z_small scalar H). Qed.

Theorem clear_affine_correct point scalar : 0 <= scalar < 2^255 ->
  SharedLoop.clear_affine MaskedCurve25519.inverse_exponent 255 P.a24
    (C.M.decode_word (load point scalar).1)
    (fun i => Z.testbit (Zmod.unsigned (load point scalar).2) (Z.of_nat i)) =
  Curve25519.M.X0 (Curve25519.M.scalarmult scalar point).
Proof.
  intro H. rewrite load_coordinate (load_scalar point scalar H).
  change (SharedLoop.clear_affine MaskedCurve25519.inverse_exponent 255
    (FiatField.encode FiatField.curve25519_modulus_gt1 121666)
    (FiatField.encode FiatField.curve25519_modulus_gt1 (F.to_Z (Curve25519.M.X0 point)))
    (fun i => bit_i scalar i) = Curve25519.M.X0 (Curve25519.M.scalarmult scalar point)).
  rewrite MaskedCurve25519.affine_matches_math.
  apply (proj2 (F.eq_to_Z_iff _ _)).
  exact (Curve25519Bridge.curve25519_cswap_correct 255 scalar point H).
Qed.

Definition program n point scalar first_randomness randomness :=
  S.ticks n S.work_edges randomness (S.launch n (load point scalar) first_randomness).

Lemma inverse_power_matches : L.inverse_power = MaskedCurve25519.inverse_exponent.
Proof. vm_compute. reflexivity. Qed.

Lemma output_value n state :
  C.reconstruct_group n (fn.interp (C.output n) state) = F.value n state.2 263%nat.
Proof. reflexivity. Qed.

Theorem program_correct n point scalar first_randomness randomness : 0 <= scalar < 2^255 ->
  C.reconstruct_group n (fn.interp (C.output n) (program n point scalar first_randomness randomness)) =
  Curve25519.M.X0 (Curve25519.M.scalarmult scalar point).
Proof.
  intro H. rewrite output_value /program L.program_correct_actual inverse_power_matches.
  exact (clear_affine_correct point scalar H).
Qed.

Theorem program_ready n point scalar first_randomness randomness :
  fn.interp (C.ready n) (program n point scalar first_randomness randomness) = bits.of_Z 1 1.
Proof. exact (S.complete_tick_ready n (load point scalar) first_randomness randomness). Qed.

End MaskedControllerCurve.
Print Assumptions MaskedControllerCurve.clear_affine_correct.
Print Assumptions MaskedControllerCurve.program_correct.
Print Assumptions MaskedControllerCurve.program_ready.
