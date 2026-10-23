Require Import ladder_math ladder_machine curve25519.
From Crypto Require Import Spec.Curve25519 Spec.ModularArithmetic.
From Stdlib Require Import ZArith Lia.
Import Curve25519Bridge.
Open Scope Z_scope.

Example scalar_zero : curve25519_ladder 0 9 0 = 0.
Proof.
  pose proof (curve25519_ladder_correct 0 0 Curve25519.M.B ltac:(cbn; lia)) as H.
  exact H.
Qed.

Example scalar_one : curve25519_ladder 1 9 1 = 9.
Proof.
  pose proof (curve25519_ladder_correct 1 1 Curve25519.M.B ltac:(cbn; lia)) as H.
  exact H.
Qed.

Example scalar_truncated : curve25519_ladder 3 9 8 = 0.
Proof. exact (curve25519_ladder_correct_mod 3 8 Curve25519.M.B). Qed.

Example cswap_scalar_one : curve25519_cswap 1 9 1 = 9.
Proof.
  pose proof (curve25519_cswap_correct 1 1 Curve25519.M.B ltac:(cbn; lia)) as H.
  exact H.
Qed.

Example zero_coordinate_step : MontLadder (2^255-19) 121666 1 0 1 = (0, 0).
Proof. vm_compute. reflexivity. Qed.

Example basepoint_first_step : MontLadder (2^255-19) 121666 1 9 1 = (324, 36).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions curve25519_ladder_correct_mod.
Print Assumptions curve25519_ladder_correct.
Print Assumptions curve25519_cswap_correct.

Example protected_scalar_zero : Curve25519Machine.output 9 0 = 0.
Proof.
  pose proof (Curve25519Machine.program_correct Curve25519.M.B 0 ltac:(vm_compute; split; congruence)) as H.
  exact H.
Qed.

Example protected_scalar_one : Curve25519Machine.output 9 1 = 9.
Proof.
  pose proof (Curve25519Machine.program_correct Curve25519.M.B 1 ltac:(vm_compute; split; congruence)) as H.
  exact H.
Qed.

Example protected_max_scalar :
  Curve25519Machine.output 9 (2^255-1) = F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult (2^255-1) Curve25519.M.B)).
Proof.
  exact (Curve25519Machine.program_correct Curve25519.M.B (2^255-1) ltac:(vm_compute; split; congruence)).
Qed.

Example protected_trace_zero_vs_max :
  LadderMachine.hw_trace 255 Curve25519Machine.modulus (Curve25519Machine.initial 9 0) Curve25519Machine.program =
  LadderMachine.hw_trace 255 Curve25519Machine.modulus (Curve25519Machine.initial 9 (2^255-1)) Curve25519Machine.program.
Proof. apply Curve25519Machine.power_trace_independent. Qed.

Print Assumptions Curve25519Machine.program_correct.
Print Assumptions Curve25519Machine.program_secure.
Print Assumptions Curve25519Machine.protected_ladder_correct_and_secure.
Print Assumptions Curve25519Machine.power_trace_independent.

Example processor_scalar_zero : Curve25519Processor.output 9 0 = 0.
Proof. rewrite Curve25519Processor.output_refines. apply protected_scalar_zero. Qed.

Example processor_scalar_one : Curve25519Processor.output 9 1 = 9.
Proof. rewrite Curve25519Processor.output_refines. apply protected_scalar_one. Qed.

Example processor_max_scalar :
  Curve25519Processor.output 9 (2^255-1) =
    F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult (2^255-1) Curve25519.M.B)).
Proof. rewrite Curve25519Processor.output_refines. apply protected_max_scalar. Qed.

Example processor_trace_zero_vs_max :
  Curve25519Processor.leakage 9 0 = Curve25519Processor.leakage 9 (2^255-1).
Proof. apply Curve25519Processor.power_trace_independent. Qed.

Example processor_fixed_trace_length : length (Curve25519Processor.leakage 9 1) = 22201%nat.
Proof. apply Curve25519Processor.leakage_length. Qed.

Print Assumptions Curve25519Processor.execute_refines.
Print Assumptions Curve25519Processor.program_correct.
Print Assumptions Curve25519Processor.program_boundary.
Print Assumptions Curve25519Processor.program_valid.
Print Assumptions Curve25519Processor.power_trace_independent.
Print Assumptions Curve25519Processor.protected_ladder_correct_and_secure.
