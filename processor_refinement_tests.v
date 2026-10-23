Require Import processor_refinement state_machine ladder_machine dual_circuit ladder_math.
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector list.
Open Scope Z_scope.

Module ProcessorRefinementTests.
Module PR := ProcessorRefinement.
Module SM := StateMachine.
Module LM := LadderMachine.

Definition initial (scalar : Z) :=
  PR.initial_regs 21 (Z_to_bv 21 6) (Z_to_bv 21 7) (Z_to_bv 21 scalar).

Definition projective_run (scalar : Z) :=
  PR.run_program 21 (Z_to_bv 21 13) (initial scalar) (LM.projective_program 3).

Definition affine_code :=
  LM.affine_program 3 11%positive.

Definition affine_run (scalar : Z) :=
  PR.run_program 21 (Z_to_bv 21 13) (initial scalar) affine_code.

Example projective_loop_outputs :
  List.map (fun scalar => PR.projective_output 21 (projective_run scalar)) [0; 1; 5; 7; 8] =
    [(1, 0); (12, 2); (12, 8); (3, 8); (1, 0)].
Proof. vm_compute. reflexivity. Qed.

Example mathematical_loop_outputs :
  List.map (MontLadderCSwap 13 7 3 6) [0; 1; 5; 7; 8] =
    [(1, 0); (12, 2); (12, 8); (3, 8); (1, 0)].
Proof. vm_compute. reflexivity. Qed.

Example affine_loop_outputs :
  List.map (fun scalar => PR.affine_output 21 (affine_run scalar)) [0; 1; 5; 7; 8] =
    [0; 6; 8; 2; 0].
Proof. vm_compute. reflexivity. Qed.

Example continuous_execution_boundaries :
  length (LM.projective_program 3) = 88%nat /\ length affine_code = 95%nat /\
  bv_unsigned (SM.pc 21 (projective_run 5)) = 88 /\
  SM.Stage 21 (projective_run 5) = SM.Fetch /\
  bv_unsigned (SM.pc 21 (affine_run 5)) = 95 /\
  SM.Stage 21 (affine_run 5) = SM.Fetch.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example affine_preserves_public_inputs_and_scalar :
  let s := affine_run 5 in
  List.map (fun r => bv_unsigned (SM.read_reg 21 (SM.Regs 21 s) r))
    [0%nat; 5%nat; 24%nat] = [6; 7; 5].
Proof. vm_compute. reflexivity. Qed.

Example affine_register_bridge :
  let abstract := (LM.run 21 (Z_to_bv 21 13)
    (LM.initial_state 21 (Z_to_bv 21 6) (Z_to_bv 21 7) (Z_to_bv 21 5)) affine_code).1 in
  List.map (fun r => bv_unsigned (SM.read_reg 21 (SM.Regs 21 (affine_run 5)) r)) (seq 0 28) =
  List.map (fun value => bv_unsigned value) (env 21 abstract).
Proof. vm_compute. reflexivity. Qed.

Example empty_loop_initialization :
  PR.projective_output 21
    (PR.run_program 21 (Z_to_bv 21 13) (initial 5) (LM.projective_program 0)) = (1, 0).
Proof. vm_compute. reflexivity. Qed.

Example affine_trace_independent scalar1 scalar2 :
  SM.hw_trace 21 (Z_to_bv 21 13)
    (SM.mk_processor_state 21 (PR.encoded_program 21 affine_code) (initial scalar1)) 285 =
  SM.hw_trace 21 (Z_to_bv 21 13)
    (SM.mk_processor_state 21 (PR.encoded_program 21 affine_code) (initial scalar2)) 285.
Proof. apply SM.processor_trace_independent. Qed.

Print Assumptions SM.run_code_correct.
Print Assumptions PR.instruction_refines.
Print Assumptions PR.run_refines.
Print Assumptions PR.initial_registers_match.
Print Assumptions PR.compiled_in_bounds.
Print Assumptions PR.run_program_refines.
Print Assumptions PR.run_program_boundary.
Print Assumptions PR.projective_program_correct.
Print Assumptions PR.affine_program_correct.
Print Assumptions SM.processor_trace_independent.
End ProcessorRefinementTests.
