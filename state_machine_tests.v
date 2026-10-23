Require Import state_machine dual_circuit ladder_math.
From stdpp Require Import bitvector list.
From Stdlib Require Import Vectors.Vector Vectors.Fin.
Open Scope Z_scope.
Module SM := StateMachine.
Module StateMachineTests.

Definition initial (code : list SM.instr) (a b : Z) : SM.state 21 :=
  let regs := SM.write_reg 21 (SM.write_reg 21 (Vector.const (bv_0 21) 32) 1%nat (Z_to_bv 21 a)) 2%nat (Z_to_bv 21 b) in
  SM.mk_processor_state 21 (List.map (SM.encode_instr 21) code) regs.

Definition run (code : list SM.instr) (a b : Z) (cycles : nat) : SM.state 21 :=
  SM.run_ticks 21 (Z_to_bv 21 13) (initial code a b) cycles.

Definition result (e : SM.instr) (a b : Z) (rd : nat) : Z :=
  bv_unsigned (SM.read_reg 21 (SM.Regs 21 (run [e] a b 3)) rd).

Lemma initial_valid code a b : SM.valid_state 21 (initial code a b).
Proof. apply SM.mk_processor_state_valid. Qed.

Lemma run_valid code a b cycles : SM.valid_state 21 (run code a b cycles).
Proof. apply SM.run_ticks_preserves_valid, initial_valid. Qed.

Example decode_max_indices :
  SM.decode_instr 21 (SM.encode_instr 21 (SM.IMul 31%nat 31%nat 31%nat)) = Some (SM.IMul 31%nat 31%nat 31%nat).
Proof. vm_compute. reflexivity. Qed.

Example add_before_bitvector_wrap : result (SM.IAdd 1%nat 1%nat 2%nat) 2097151 2097151 1 = 8.
Proof. vm_compute. reflexivity. Qed.

Example subtract_before_bitvector_wrap : result (SM.ISub 1%nat 1%nat 2%nat) 0 1 1 = 12.
Proof. vm_compute. reflexivity. Qed.

Example multiply_before_bitvector_wrap : result (SM.IMul 1%nat 1%nat 2%nat) 2097151 2097151 1 = 3.
Proof. vm_compute. reflexivity. Qed.

Example fetch_then_execute_then_writeback :
  SM.Stage 21 (run [SM.IAdd 1%nat 1%nat 2%nat] 12 12 1) = SM.Execute /\
  SM.Stage 21 (run [SM.IAdd 1%nat 1%nat 2%nat] 12 12 2) = SM.WriteBack /\
  SM.Stage 21 (run [SM.IAdd 1%nat 1%nat 2%nat] 12 12 3) = SM.Fetch.
Proof. vm_compute. repeat split. Qed.

Example execute_does_not_write_early :
  bv_unsigned (SM.read_reg 21 (SM.Regs 21 (run [SM.IAdd 1%nat 1%nat 2%nat] 12 12 2)) 1%nat) = 12.
Proof. vm_compute. reflexivity. Qed.

Example execute_latches_complement :
  SM.bookkeepingState 21 (run [SM.IAdd 1%nat 1%nat 2%nat] 12 12 2) =
    (((true, 1%nat), Z_to_bv 21 11), bv_not (Z_to_bv 21 11)).
Proof. vm_compute. reflexivity. Qed.

Example consecutive_instructions :
  bv_unsigned (SM.read_reg 21 (SM.Regs 21 (run [SM.IAdd 1%nat 1%nat 2%nat; SM.IMul 3%nat 1%nat 2%nat] 2097151 2097151 6)) 3%nat) = 6.
Proof. vm_compute. reflexivity. Qed.

Example counter_advances_once_per_instruction :
  bv_unsigned (SM.pc 21 (run [SM.IAdd 1%nat 1%nat 2%nat; SM.IMul 3%nat 1%nat 2%nat] 12 12 6)) = 2.
Proof. vm_compute. reflexivity. Qed.

Example initial_pairing_balances_secret :
  SM.state_HW 21 (initial [SM.IAdd 23%nat 1%nat 2%nat] 0 0) = SM.state_HW 21 (initial [SM.IAdd 23%nat 1%nat 2%nat] 1 0).
Proof. vm_compute. reflexivity. Qed.

Example register_23_write_balanced :
  SM.state_HW 21 (run [SM.IAdd 23%nat 1%nat 2%nat] 1 0 3) = SM.state_HW 21 (run [SM.IAdd 23%nat 1%nat 2%nat] 0 0 3).
Proof. vm_compute. reflexivity. Qed.

Example every_destination_balanced_each_cycle :
  forallb (fun rd => forallb (fun cycles =>
    Nat.eqb (SM.state_HW 21 (run [SM.IAdd rd 1%nat 2%nat; SM.IMul rd rd 2%nat] 0 1 cycles))
      (SM.state_HW 21 (run [SM.IAdd rd 1%nat 2%nat; SM.IMul rd rd 2%nat] 12 1 cycles)))
    (seq 0 7)) (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Example register_31_complement_written :
  let s := run [SM.IAdd 31%nat 1%nat 2%nat] 12 12 3 in
  SM.read_reg 21 (SM.DRegs 21 s) 31%nat = bv_not (Z_to_bv 21 11).
Proof. vm_compute. reflexivity. Qed.

Example writeback_resets_latch_to_pair :
  SM.bookkeepingState 21 (run [SM.IAdd 23%nat 1%nat 2%nat] 12 12 3) =
    (((false, 0%nat), bv_0 21), bv_not (bv_0 21)).
Proof. vm_compute. reflexivity. Qed.

Example protected_storage_constant code a b cycles :
  SM.protected_HW 21 (run code a b cycles) = 714%nat.
Proof. apply SM.run_ticks_protected_HW, initial_valid. Qed.

Definition inactive_latch (value dual : bv 21) : SM.state 21 :=
  let s := initial [] 0 0 in
  SM.mkState 21 (SM.pc 21 s) (SM.Regs 21 s) (SM.DRegs 21 s) [] SM.Execute
    (false, bv_0 21) (false, bv_0 21) (((false, 23%nat), value), dual)
    (((false, 0%nat), bv_0 21), bv_not (bv_0 21)).

Example inactive_latch_cannot_hide_unpaired_data :
  ~ SM.valid_state 21 (inactive_latch (bv_0 21) (bv_0 21)).
Proof.
  intros [_ [Hlatch _]].
  pose proof (f_equal bv_unsigned Hlatch) as Hbits. vm_compute in Hbits. discriminate.
Qed.

Example inactive_latch_is_protected value :
  SM.valid_state 21 (inactive_latch value (bv_not value)).
Proof.
  split; [exact (proj1 (initial_valid [] 0 0)) | split; reflexivity].
Qed.

Example stalled_execute_preserves_pair :
  SM.protected_HW 21 (SM.full_tick 21 (Z_to_bv 21 13) (inactive_latch (Z_to_bv 21 42) (bv_not (Z_to_bv 21 42)))) = 714%nat.
Proof. vm_compute. reflexivity. Qed.

Example disabled_writeback_preserves_pair :
  let s := inactive_latch (Z_to_bv 21 42) (bv_not (Z_to_bv 21 42)) in
  SM.protected_HW 21 (SM.run_ticks 21 (Z_to_bv 21 13) s 2) = 714%nat.
Proof. vm_compute. reflexivity. Qed.

Example nonwriting_instruction_preserves_pair :
  SM.protected_HW 21 (run [SM.Observe 1%nat] 12 12 3) = 714%nat.
Proof. vm_compute. reflexivity. Qed.

Example full_pairing_implies_selective_validity : forall classify,
  valid_state_partial 21
    {| env := [Z_to_bv 21 3; Z_to_bv 21 5]; denv := List.map bv_not [Z_to_bv 21 3; Z_to_bv 21 5] |} classify.
Proof. intro classify. apply valid_state_implies_partial. reflexivity. Qed.

Example selective_update_preserves_validity : forall classify e,
  valid_state_partial 21
    (dual_interp_selective 21 (Z_to_bv 21 13) classify
      {| env := [Z_to_bv 21 3; Z_to_bv 21 5]; denv := List.map bv_not [Z_to_bv 21 3; Z_to_bv 21 5] |} e).1 classify.
Proof.
  intros classify e. apply dual_interp_selective_preserves_partial.
  - apply valid_state_implies_partial. reflexivity.
  - reflexivity.
Qed.

Definition swap_initial (control a b : Z) : SM.state 21 :=
  SM.mk_processor_state 21 [SM.encode_instr 21 (SM.CSwap 3%nat 1%nat 2%nat)]
    (SM.write_reg 21 (SM.Regs 21 (initial [] a b)) 3%nat (Z_to_bv 21 control)).

Definition swap_run (control a b : Z) (cycles : nat) : SM.state 21 :=
  SM.run_ticks 21 (Z_to_bv 21 13) (swap_initial control a b) cycles.

Definition operand_values (s : SM.state 21) : Z * Z :=
  (bv_unsigned (SM.read_reg 21 (SM.Regs 21 s) 1%nat),
   bv_unsigned (SM.read_reg 21 (SM.Regs 21 s) 2%nat)).

Example all_opcodes_roundtrip :
  List.map (fun e => SM.decode_instr 21 (SM.encode_instr 21 e))
    [SM.IAdd 31%nat 31%nat 31%nat; SM.ISub 31%nat 31%nat 31%nat; SM.IMul 31%nat 31%nat 31%nat; SM.Observe 31%nat;
     SM.Copy 31%nat 31%nat; SM.GetBit 31%nat 31%nat 255%nat; SM.Xor 31%nat 31%nat 31%nat; SM.CSwap 31%nat 31%nat 31%nat] =
  List.map Some
    [SM.IAdd 31%nat 31%nat 31%nat; SM.ISub 31%nat 31%nat 31%nat; SM.IMul 31%nat 31%nat 31%nat; SM.Observe 31%nat;
     SM.Copy 31%nat 31%nat; SM.GetBit 31%nat 31%nat 255%nat; SM.Xor 31%nat 31%nat 31%nat; SM.CSwap 31%nat 31%nat 31%nat].
Proof. vm_compute. reflexivity. Qed.

Example copy_preserves_noncanonical_value : result (SM.Copy 1%nat 1%nat) 2097151 0 1 = 2097151.
Proof. vm_compute. reflexivity. Qed.

Example copy_to_distinct_destination : result (SM.Copy 2%nat 1%nat) 2097151 0 2 = 2097151.
Proof. vm_compute. reflexivity. Qed.

Example getbit_aliased_source : result (SM.GetBit 1%nat 1%nat 20%nat) 1048576 0 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Example getbit_above_word_width : result (SM.GetBit 1%nat 1%nat 255%nat) 2097151 0 1 = 0.
Proof. vm_compute. reflexivity. Qed.

Example xor_reads_original_operands : result (SM.Xor 1%nat 1%nat 2%nat) 1048577 1 1 = 1048576.
Proof. vm_compute. reflexivity. Qed.

Example swap_true : operand_values (swap_run 1 42 99 3) = (99, 42).
Proof. vm_compute. reflexivity. Qed.

Example swap_false : operand_values (swap_run 0 42 99 3) = (42, 99).
Proof. vm_compute. reflexivity. Qed.

Example swap_nonboolean_control : operand_values (swap_run 2 42 99 3) = (42, 99).
Proof. vm_compute. reflexivity. Qed.

Example swap_control_aliases_first : operand_values (run [SM.CSwap 1%nat 1%nat 2%nat] 1 99 3) = (99, 1).
Proof. vm_compute. reflexivity. Qed.

Example swap_control_aliases_second : operand_values (run [SM.CSwap 2%nat 1%nat 2%nat] 42 1 3) = (1, 42).
Proof. vm_compute. reflexivity. Qed.

Example swap_same_operand : operand_values (run [SM.CSwap 1%nat 2%nat 2%nat] 1 99 3) = (1, 99).
Proof. vm_compute. reflexivity. Qed.

Example swap_execute_does_not_write : operand_values (swap_run 1 42 99 2) = (42, 99).
Proof. vm_compute. reflexivity. Qed.

Example swap_second_result_paired :
  SM.bookkeepingState2 21 (swap_run 1 42 99 2) =
    (((true, 2%nat), Z_to_bv 21 42), bv_not (Z_to_bv 21 42)).
Proof. vm_compute. reflexivity. Qed.

Example false_swap_still_writes_both :
  SM.bookkeepingState 21 (swap_run 0 42 99 2) =
    (((true, 1%nat), Z_to_bv 21 42), bv_not (Z_to_bv 21 42)) /\
  SM.bookkeepingState2 21 (swap_run 0 42 99 2) =
    (((true, 2%nat), Z_to_bv 21 99), bv_not (Z_to_bv 21 99)).
Proof. vm_compute. split; reflexivity. Qed.

Example swap_resets_second_latch :
  SM.bookkeepingState2 21 (swap_run 1 42 99 3) =
    (((false, 0%nat), bv_0 21), bv_not (bv_0 21)).
Proof. vm_compute. reflexivity. Qed.

Example swap_cycle_leakage_equal :
  List.map (fun cycles => SM.state_HW 21 (swap_run 0 42 99 cycles)) (seq 0 4) =
  List.map (fun cycles => SM.state_HW 21 (swap_run 1 2097151 0 cycles)) (seq 0 4).
Proof. vm_compute. reflexivity. Qed.

Example swap_followed_by_add :
  operand_values (run [SM.CSwap 1%nat 1%nat 2%nat; SM.IAdd 2%nat 1%nat 2%nat] 1 99 6) = (99, 9).
Proof. vm_compute. reflexivity. Qed.

Example getbit_curve25519_top_bit :
  let regs := SM.write_reg 255 (Vector.const (bv_0 255) 32) 1%nat (Z_to_bv 255 (2 ^ 254)) in
  let s := SM.mk_processor_state 255 [SM.encode_instr 255 (SM.GetBit 1%nat 1%nat 254%nat)] regs in
  bv_unsigned (SM.read_reg 255
    (SM.Regs 255 (SM.run_ticks 255 (Z_to_bv 255 (2 ^ 255 - 19)) s 3)) 1%nat) = 1.
Proof. vm_compute. reflexivity. Qed.

Example swap_to_highest_register :
  bv_unsigned (SM.read_reg 21 (SM.Regs 21 (run [SM.CSwap 1%nat 2%nat 31%nat] 1 99 3)) 31%nat) = 99.
Proof. vm_compute. reflexivity. Qed.

Definition unpaired_second_latch : SM.state 21 :=
  let s := initial [] 0 0 in
  SM.mkState 21 (SM.pc 21 s) (SM.Regs 21 s) (SM.DRegs 21 s) [] SM.Execute
    (false, bv_0 21) (false, bv_0 21)
    (((false, 0%nat), bv_0 21), bv_not (bv_0 21))
    (((false, 0%nat), bv_0 21), bv_0 21).

Example inactive_second_latch_cannot_hide_unpaired_data :
  ~ SM.valid_state 21 unpaired_second_latch.
Proof.
  intros [_ [_ Hlatch]].
  pose proof (f_equal bv_unsigned Hlatch) as Hbits. vm_compute in Hbits. discriminate.
Qed.

Definition ladder_start (x2 z2 x3 z3 x1 a24 : Z) : SM.state 21 :=
  SM.ladder_init 21 (Z_to_bv 21 x2) (Z_to_bv 21 z2) (Z_to_bv 21 x3)
    (Z_to_bv 21 z3) (Z_to_bv 21 x1) (Z_to_bv 21 a24).

Definition ladder_finish (x2 z2 x3 z3 x1 a24 : Z) : SM.state 21 :=
  SM.run_ticks 21 (Z_to_bv 21 13) (ladder_start x2 z2 x3 z3 x1 a24) 54.

Definition ladder_case (x2 z2 x3 z3 x1 a24 : Z) (expected : Z * Z * Z * Z) : Prop :=
  SM.ladder_output 21 (ladder_finish x2 z2 x3 z3 x1 a24) = expected /\
  LadderStep 13 a24 x1 x2 z2 x3 z3 = expected.

Example ladder_step_mixed_inputs : ladder_case 2 3 4 5 6 7 (12, 0, 1, 5).
Proof. vm_compute. split; reflexivity. Qed.

Example ladder_step_zero_inputs : ladder_case 0 0 0 0 0 0 (0, 0, 0, 0).
Proof. vm_compute. split; reflexivity. Qed.

Example ladder_step_maximum_words :
  ladder_case 2097151 2097151 2097151 2097151 2097151 2097151 (0, 4, 0, 0).
Proof. vm_compute. split; reflexivity. Qed.

Example ladder_step_noncanonical_input : ladder_case 2097151 1 12 2 9 5 (4, 7, 1, 4).
Proof. vm_compute. split; reflexivity. Qed.

Example ladder_step_nonzero_scratch :
  let regs := Vector.const (Z_to_bv 21 2097151) 32 in
  let regs := SM.write_reg 21 regs 0%nat (Z_to_bv 21 6) in
  let regs := SM.write_reg 21 regs 1%nat (Z_to_bv 21 2) in
  let regs := SM.write_reg 21 regs 2%nat (Z_to_bv 21 3) in
  let regs := SM.write_reg 21 regs 3%nat (Z_to_bv 21 4) in
  let regs := SM.write_reg 21 regs 4%nat (Z_to_bv 21 5) in
  let regs := SM.write_reg 21 regs 5%nat (Z_to_bv 21 7) in
  let s := SM.mk_processor_state 21 (SM.ladder_instr_mem 21) regs in
  SM.ladder_output 21 (SM.run_ticks 21 (Z_to_bv 21 13) s 54) = (12, 0, 1, 5).
Proof. vm_compute. reflexivity. Qed.

Example ladder_step_execution_boundary :
  let s := ladder_finish 2097151 1 12 2 9 5 in
  bv_unsigned (SM.pc 21 s) = 18 /\ SM.Stage 21 s = SM.Fetch /\
  List.map (fun r => bv_unsigned (SM.read_reg 21 (SM.Regs 21 s) r)) (seq 0 6) =
    [9; 2097151; 1; 12; 2; 5].
Proof. vm_compute. repeat split; reflexivity. Qed.

Example ladder_step_trace_independent x2 z2 x3 z3 x1 a24 x2' z2' x3' z3' :
  SM.hw_trace 21 (Z_to_bv 21 13) (ladder_start x2 z2 x3 z3 x1 a24) 54 =
  SM.hw_trace 21 (Z_to_bv 21 13) (ladder_start x2' z2' x3' z3' x1 a24) 54.
Proof. apply SM.processor_trace_independent. Qed.

Definition iteration_inputs (n : N) (scalar : Z) (previous : bool) : Vector.t (bv n) 32 :=
  let regs := Vector.const (Z_to_bv n (-1)) 32 in
  let regs := SM.write_reg n regs 0%nat (Z_to_bv n 6) in
  let regs := SM.write_reg n regs 1%nat (Z_to_bv n 2) in
  let regs := SM.write_reg n regs 2%nat (Z_to_bv n 3) in
  let regs := SM.write_reg n regs 3%nat (Z_to_bv n 4) in
  let regs := SM.write_reg n regs 4%nat (Z_to_bv n 5) in
  let regs := SM.write_reg n regs 5%nat (Z_to_bv n 7) in
  let regs := SM.write_reg n regs 24%nat (Z_to_bv n scalar) in
  SM.write_reg n regs 25%nat (Z_to_bv n (Z.b2z previous)).

Definition iteration_case (bit previous : bool) (expected : Z * Z * Z * Z) : Prop :=
  let s := SM.iteration_result 21 (Z_to_bv 21 13)
    (iteration_inputs 21 (Z.b2z bit) previous) 0%nat in
  SM.point_regs 21 s = expected /\
  bv_unsigned (SM.read_reg 21 (SM.Regs 21 s) 25%nat) = Z.b2z bit /\
  MontLadderCSwap_step 13 7 6 bit previous (2, 3, 4, 5) = (expected, bit).

Example iteration_false_false : iteration_case false false (12, 0, 1, 5).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example iteration_false_true : iteration_case false true (3, 4, 1, 5).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example iteration_true_false : iteration_case true false (3, 4, 1, 5).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example iteration_true_true : iteration_case true true (12, 0, 1, 5).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example iteration_execution_boundary :
  let s := SM.iteration_result 21 (Z_to_bv 21 13) (iteration_inputs 21 2097151 false) 20%nat in
  SM.point_regs 21 s = (3, 4, 1, 5) /\
  bv_unsigned (SM.pc 21 s) = 27 /\ SM.Stage 21 s = SM.Fetch /\
  List.map (fun r => bv_unsigned (SM.read_reg 21 (SM.Regs 21 s) r)) [0%nat; 5%nat; 24%nat; 25%nat] =
    [6; 7; 2097151; 1].
Proof. vm_compute. repeat split; reflexivity. Qed.

Example iteration_index_254 :
  let s := SM.iteration_result 255 (Z_to_bv 255 13)
    (iteration_inputs 255 (2 ^ 254) false) 254%nat in
  SM.point_regs 255 s = (3, 4, 1, 5) /\
  bv_unsigned (SM.read_reg 255 (SM.Regs 255 s) 24%nat) = 2 ^ 254 /\
  bv_unsigned (SM.read_reg 255 (SM.Regs 255 s) 25%nat) = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example iteration_trace_independent scalar1 scalar2 previous1 previous2 index :
  let code := List.map (SM.encode_instr 21) (SM.iteration_code index) in
  SM.hw_trace 21 (Z_to_bv 21 13)
    (SM.mk_processor_state 21 code (iteration_inputs 21 scalar1 previous1)) 81 =
  SM.hw_trace 21 (Z_to_bv 21 13)
    (SM.mk_processor_state 21 code (iteration_inputs 21 scalar2 previous2)) 81.
Proof. apply SM.processor_trace_independent. Qed.

Print Assumptions valid_state_implies_partial.
Print Assumptions dual_interp_selective_preserves_partial.
Print Assumptions SM.decode_encode_instr.
Print Assumptions SM.instruction_cycle_correct.
Print Assumptions SM.add_cycle_correct.
Print Assumptions SM.sub_cycle_correct.
Print Assumptions SM.mul_cycle_correct.
Print Assumptions SM.copy_cycle_correct.
Print Assumptions SM.getbit_cycle_correct.
Print Assumptions SM.xor_cycle_correct.
Print Assumptions SM.cswap_cycle_correct.
Print Assumptions SM.ladder_result_valid.
Print Assumptions SM.run_instruction.
Print Assumptions SM.ladder_result_correct.
Print Assumptions SM.ladder_block_correct.
Print Assumptions SM.iteration_code_length.
Print Assumptions SM.iteration_correct.
Print Assumptions SM.run_ticks_preserves_valid.
Print Assumptions SM.protected_HW_constant.
Print Assumptions SM.run_ticks_protected_HW.
Print Assumptions SM.state_HW_decomposition.
Print Assumptions SM.state_HW_public.
Print Assumptions SM.power_independence.
Print Assumptions SM.hw_trace_length.
Print Assumptions SM.hw_trace_independent.
Print Assumptions SM.processor_trace_independent.
End StateMachineTests.
