Require Import ladder_math dual_circuit ladder_machine.
From stdpp Require Import bitvector list.
Open Scope Z_scope.

Module LadderMachineTests.
Module LM := LadderMachine.

Definition make_state (values : list Z) : state 8 :=
  let regs := map (Z_to_bv 8) values in
  {| env := regs; denv := map bv_not regs |}.

Definition execute (values : list Z) (code : list LM.instr) : list Z :=
  map bv_unsigned (env 8 (LM.run 8 (Z_to_bv 8 101) (make_state values) code).1).

Example copy_alias : execute [42] [LM.Copy 0 0] = [42].
Proof. vm_compute. reflexivity. Qed.

Example bit_alias : execute [128] [LM.GetBit 0 0 7] = [1].
Proof. vm_compute. reflexivity. Qed.

Example high_bit_is_zero : execute [255] [LM.GetBit 0 0 8] = [0].
Proof. vm_compute. reflexivity. Qed.

Example xor_alias : execute [170; 85] [LM.Xor 0 0 1] = [255; 85].
Proof. vm_compute. reflexivity. Qed.

Example swap_false : execute [10; 20; 0] [LM.CSwap 2 0 1] = [10; 20; 0].
Proof. vm_compute. reflexivity. Qed.

Example swap_true : execute [10; 20; 1] [LM.CSwap 2 0 1] = [20; 10; 1].
Proof. vm_compute. reflexivity. Qed.

Example swap_self : execute [42; 1] [LM.CSwap 1 0 0] = [42; 1].
Proof. vm_compute. reflexivity. Qed.

Example swap_control_alias : execute [1; 7] [LM.CSwap 0 0 1] = [7; 1].
Proof. vm_compute. reflexivity. Qed.

Example base_observe_is_not_hidden : (LM.run 8 (Z_to_bv 8 101) (make_state [42]) [LM.Base (Observe 0%nat)]).2 = [RegObservation 8 0%nat (Z_to_bv 8 42)].
Proof. vm_compute. reflexivity. Qed.

Definition iteration_state (scalar : Z) (previous : bool) : state 8 :=
  make_state ([9; 3; 4; 5; 6; 3] ++ repeat 255 18 ++ [scalar; Z.b2z previous; 255; 255] ++ [99]).

Example all_control_combinations :
  forall current previous : bool,
    let initial := iteration_state (Z.b2z current) previous in
    let final := (LM.run 8 (Z_to_bv 8 101) initial (LM.iteration 0)).1 in
    (LM.point_regs 8 final, bv_unsigned (read_register 8 (env 8 final) 25%nat)) =
      let result := MontLadderCSwap_step 101 3 9 current previous (3, 4, 5, 6) in (result.1, Z.b2z result.2).
Proof. intros [] []; vm_compute; reflexivity. Qed.

Example consecutive_iterations :
  let initial := iteration_state 2 false in
  let final := (LM.run 8 (Z_to_bv 8 101) initial (LM.iteration 1 ++ LM.iteration 0)).1 in
  let '(middle, previous) := MontLadderCSwap_step 101 3 9 true false (3, 4, 5, 6) in
  let result := MontLadderCSwap_step 101 3 9 false previous middle in
  (LM.point_regs 8 final, bv_unsigned (read_register 8 (env 8 final) 25%nat)) = (result.1, Z.b2z result.2).
Proof. vm_compute. reflexivity. Qed.

Example iteration_has_no_raw_observations : (LM.run 8 (Z_to_bv 8 101) (iteration_state 1 false) (LM.iteration 0)).2 = [].
Proof. apply LM.run_no_observe, LM.iteration_no_observe. Qed.

Example iteration_trace : LM.hw_trace 8 (Z_to_bv 8 101) (iteration_state 1 false) (LM.iteration 0) = repeat 232%nat 28.
Proof. rewrite LM.hw_trace_constant by reflexivity. reflexivity. Qed.

Example curve25519_iteration :
  let values := [9; 1; 0; 9; 1; 121666] ++ repeat (2 ^ 255 - 1) 18 ++ [1; 0; 0; 0] in
  let regs := map (Z_to_bv 255) values in
  let initial := {| env := regs; denv := map bv_not regs |} in
  let final := (LM.run 255 (Z_to_bv 255 (2 ^ 255 - 19)) initial (LM.iteration 0)).1 in
  (LM.point_regs 255 final, bv_unsigned (read_register 255 (env 255 final) 25%nat)) = ((MontLadderCSwap_step (2 ^ 255 - 19) 121666 9 true false (1, 0, 9, 1)).1, 1).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions LM.iteration_correct.
Print Assumptions LM.iteration_secure.
Print Assumptions LM.iteration_preserves_inputs.
Definition projective_run (width : nat) (scalar : Z) : Z * Z :=
  LM.projective_output 8 (LM.run 8 (Z_to_bv 8 101) (LM.initial_state 8 (Z_to_bv 8 9) (Z_to_bv 8 3) (Z_to_bv 8 scalar)) (LM.projective_program width)).1.

Example zero_width : projective_run 0 255 = (1, 0).
Proof. vm_compute. reflexivity. Qed.

Example zero_scalar : projective_run 4 0 = (1, 0).
Proof. vm_compute. reflexivity. Qed.

Example final_swap_taken : projective_run 1 1 = (324 mod 101, 36).
Proof. vm_compute. reflexivity. Qed.

Example final_swap_skipped : projective_run 3 6 = MontLadderCSwap 101 3 3 9 6.
Proof. vm_compute. reflexivity. Qed.

Example scalar_truncated_to_width : projective_run 3 13 = projective_run 3 5.
Proof. vm_compute. reflexivity. Qed.

Example small_scalars_all_widths :
  forallb (fun width => forallb (fun scalar => let actual := projective_run width (Z.of_nat scalar) in let expected := MontLadderCSwap 101 3 width 9 (Z.of_nat scalar) in Z.eqb actual.1 expected.1 && Z.eqb actual.2 expected.2) (seq 0 16)) (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.

Example fixed_255_instruction_count : length (LM.projective_program 255) = 6892%nat.
Proof. rewrite LM.projective_program_length. reflexivity. Qed.

Example fixed_255_trace :
  forall x a24 scalar : bv 255,
    LM.hw_trace 255 (Z_to_bv 255 (2 ^ 255 - 19)) (LM.initial_state 255 x a24 scalar) (LM.projective_program 255) = repeat 7140%nat 6893.
Proof. intros. exact (proj1 (LM.projective_program_secure 255 (Z_to_bv 255 (2 ^ 255 - 19)) x a24 scalar 255)). Qed.

Example full_width_execution : projective_run 255 173 = MontLadderCSwap 101 3 255 9 173.
Proof. vm_compute. reflexivity. Qed.

Example full_curve25519_projective_correct :
  let prime := 2 ^ 255 - 19 in
  let initial := LM.initial_state 255 (Z_to_bv 255 9) (Z_to_bv 255 121666) (Z_to_bv 255 (2 ^ 253 + 3)) in
  LM.projective_output 255 (LM.run 255 (Z_to_bv 255 prime) initial (LM.projective_program 255)).1 = MontLadderCSwap prime 121666 255 9 (2 ^ 253 + 3).
Proof. apply LM.projective_program_correct. vm_compute. reflexivity. Qed.

Print Assumptions LM.loop_correct.
Print Assumptions LM.final_swap_correct.
Print Assumptions LM.projective_program_correct.
Print Assumptions LM.projective_program_secure.

Definition conversion_input (x z : Z) : state 8 :=
  let regs := map (Z_to_bv 8) ([0; x; z] ++ repeat 255 25) in
  {| env := regs; denv := map bv_not regs |}.

Definition converted (x z : Z) (exponent : positive) : Z :=
  LM.affine_result 8 (LM.run 8 (Z_to_bv 8 101) (conversion_input x z) (LM.affine_code exponent)).1.

Example affine_zero_denominator : converted 42 0 99 = 0.
Proof. vm_compute. reflexivity. Qed.

Example affine_unit_denominator : converted 42 1 99 = 42.
Proof. vm_compute. reflexivity. Qed.

Example affine_noncanonical_inputs : converted 254 255 99 = 41.
Proof. vm_compute. reflexivity. Qed.

Example affine_first_ladder_step : converted (324 mod 101) 36 99 = 9.
Proof. vm_compute. reflexivity. Qed.

Example positive_power_cases :
  forallb (fun e => forallb (fun x => forallb (fun z => Z.eqb (converted x z (Pos.of_nat e)) ((x * z ^ Z.pos (Pos.of_nat e)) mod 101)) [0; 1; 2; 100; 101; 255]) [0; 1; 42; 254]) (seq 1 8) = true.
Proof. vm_compute. reflexivity. Qed.

Definition affine_run (width : nat) (scalar : Z) : Z :=
  LM.affine_result 8 (LM.run 8 (Z_to_bv 8 101) (LM.initial_state 8 (Z_to_bv 8 9) (Z_to_bv 8 3) (Z_to_bv 8 scalar)) (LM.affine_program width 99)).1.

Example affine_zero_width : affine_run 0 255 = 0.
Proof. vm_compute. reflexivity. Qed.

Example affine_zero_scalar : affine_run 4 0 = 0.
Proof. vm_compute. reflexivity. Qed.

Example affine_scalar_one : affine_run 4 1 = 9.
Proof. vm_compute. reflexivity. Qed.

Example affine_small_scalars_all_widths :
  forallb (fun width => forallb (fun scalar => let '(x, z) := MontLadderCSwap 101 3 width 9 (Z.of_nat scalar) in Z.eqb (affine_run width (Z.of_nat scalar)) ((x * z ^ 99) mod 101)) (seq 0 16)) (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.

Example affine_full_width_execution :
  affine_run 255 173 = let '(x, z) := MontLadderCSwap 101 3 255 9 173 in (x * z ^ 99) mod 101.
Proof. vm_compute. reflexivity. Qed.

Example affine_trace_includes_conversion :
  LM.hw_trace 8 (Z_to_bv 8 101) (LM.initial_state 8 (Z_to_bv 8 9) (Z_to_bv 8 3) (Z_to_bv 8 1)) (LM.affine_program 4 99) = repeat 224%nat 127.
Proof. rewrite LM.hw_trace_constant by reflexivity. reflexivity. Qed.

Print Assumptions LM.power_code_correct.
Print Assumptions LM.affine_program_correct.
Print Assumptions LM.affine_program_secure.
End LadderMachineTests.
