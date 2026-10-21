Require Import state_machine dual_circuit.
From stdpp Require Import bitvector list.
From Stdlib Require Import Vectors.Vector Vectors.Fin.
Open Scope Z_scope.
Module SM := StateMachine.
Module StateMachineTests.

Definition initial (code : list instr) (a b : Z) : SM.state 17 :=
  let regs := SM.write_reg 17 (SM.write_reg 17 (Vector.const (bv_0 17) 32) 1%nat (Z_to_bv 17 a)) 2%nat (Z_to_bv 17 b) in
  SM.mk_processor_state 17 (List.map (SM.encode_instr 17) code) regs.

Definition run (code : list instr) (a b : Z) (cycles : nat) : SM.state 17 :=
  SM.run_ticks 17 (Z_to_bv 17 13) (initial code a b) cycles.

Definition result (e : instr) (a b : Z) (rd : nat) : Z :=
  bv_unsigned (SM.read_reg 17 (SM.Regs 17 (run [e] a b 3)) rd).

Lemma initial_valid code a b : SM.valid_state 17 (initial code a b).
Proof. apply SM.mk_processor_state_valid. Qed.

Lemma run_valid code a b cycles : SM.valid_state 17 (run code a b cycles).
Proof. apply SM.run_ticks_preserves_valid, initial_valid. Qed.

Example decode_max_indices :
  SM.decode_instr 17 (SM.encode_instr 17 (IMul 31%nat 31%nat 31%nat)) = Some (IMul 31%nat 31%nat 31%nat).
Proof. vm_compute. reflexivity. Qed.

Example add_before_bitvector_wrap : result (IAdd 1%nat 1%nat 2%nat) 131071 131071 1 = 10.
Proof. vm_compute. reflexivity. Qed.

Example subtract_before_bitvector_wrap : result (ISub 1%nat 1%nat 2%nat) 0 1 1 = 12.
Proof. vm_compute. reflexivity. Qed.

Example multiply_before_bitvector_wrap : result (IMul 1%nat 1%nat 2%nat) 131071 131071 1 = 12.
Proof. vm_compute. reflexivity. Qed.

Example fetch_then_execute_then_writeback :
  SM.Stage 17 (run [IAdd 1%nat 1%nat 2%nat] 12 12 1) = SM.Execute /\
  SM.Stage 17 (run [IAdd 1%nat 1%nat 2%nat] 12 12 2) = SM.WriteBack /\
  SM.Stage 17 (run [IAdd 1%nat 1%nat 2%nat] 12 12 3) = SM.Fetch.
Proof. vm_compute. repeat split. Qed.

Example execute_does_not_write_early :
  bv_unsigned (SM.read_reg 17 (SM.Regs 17 (run [IAdd 1%nat 1%nat 2%nat] 12 12 2)) 1%nat) = 12.
Proof. vm_compute. reflexivity. Qed.

Example execute_latches_complement :
  SM.bookkeepingState 17 (run [IAdd 1%nat 1%nat 2%nat] 12 12 2) =
    (((true, 1%nat), Z_to_bv 17 11), bv_not (Z_to_bv 17 11)).
Proof. vm_compute. reflexivity. Qed.

Example consecutive_instructions :
  bv_unsigned (SM.read_reg 17 (SM.Regs 17 (run [IAdd 1%nat 1%nat 2%nat; IMul 3%nat 1%nat 2%nat] 131071 131071 6)) 3%nat) = 11.
Proof. vm_compute. reflexivity. Qed.

Example counter_advances_once_per_instruction :
  bv_unsigned (SM.pc 17 (run [IAdd 1%nat 1%nat 2%nat; IMul 3%nat 1%nat 2%nat] 12 12 6)) = 2.
Proof. vm_compute. reflexivity. Qed.

Example initial_pairing_balances_secret :
  SM.state_HW 17 (initial [IAdd 23%nat 1%nat 2%nat] 0 0) = SM.state_HW 17 (initial [IAdd 23%nat 1%nat 2%nat] 1 0).
Proof. vm_compute. reflexivity. Qed.

Example register_23_write_balanced :
  SM.state_HW 17 (run [IAdd 23%nat 1%nat 2%nat] 1 0 3) = SM.state_HW 17 (run [IAdd 23%nat 1%nat 2%nat] 0 0 3).
Proof. vm_compute. reflexivity. Qed.

Example every_destination_balanced_each_cycle :
  forallb (fun rd => forallb (fun cycles =>
    Nat.eqb (SM.state_HW 17 (run [IAdd rd 1%nat 2%nat; IMul rd rd 2%nat] 0 1 cycles))
      (SM.state_HW 17 (run [IAdd rd 1%nat 2%nat; IMul rd rd 2%nat] 12 1 cycles)))
    (seq 0 7)) (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Example register_31_complement_written :
  let s := run [IAdd 31%nat 1%nat 2%nat] 12 12 3 in
  SM.read_reg 17 (SM.DRegs 17 s) 31%nat = bv_not (Z_to_bv 17 11).
Proof. vm_compute. reflexivity. Qed.

Example writeback_resets_latch_to_pair :
  SM.bookkeepingState 17 (run [IAdd 23%nat 1%nat 2%nat] 12 12 3) =
    (((false, 0%nat), bv_0 17), bv_not (bv_0 17)).
Proof. vm_compute. reflexivity. Qed.

Example protected_storage_constant code a b cycles :
  SM.protected_HW 17 (run code a b cycles) = 561%nat.
Proof. apply SM.run_ticks_protected_HW, initial_valid. Qed.

Definition inactive_latch (value dual : bv 17) : SM.state 17 :=
  let s := initial [] 0 0 in
  SM.mkState 17 (SM.pc 17 s) (SM.Regs 17 s) (SM.DRegs 17 s) [] SM.Execute
    (false, bv_0 17) (false, bv_0 17) (((false, 23%nat), value), dual).

Example inactive_latch_cannot_hide_unpaired_data :
  ~ SM.valid_state 17 (inactive_latch (bv_0 17) (bv_0 17)).
Proof.
  intros [_ Hlatch].
  pose proof (f_equal bv_unsigned Hlatch) as Hbits. vm_compute in Hbits. discriminate.
Qed.

Example inactive_latch_is_protected value :
  SM.valid_state 17 (inactive_latch value (bv_not value)).
Proof.
  split; [exact (proj1 (initial_valid [] 0 0)) | reflexivity].
Qed.

Example stalled_execute_preserves_pair :
  SM.protected_HW 17 (SM.full_tick 17 (Z_to_bv 17 13) (inactive_latch (Z_to_bv 17 42) (bv_not (Z_to_bv 17 42)))) = 561%nat.
Proof. vm_compute. reflexivity. Qed.

Example disabled_writeback_preserves_pair :
  let s := inactive_latch (Z_to_bv 17 42) (bv_not (Z_to_bv 17 42)) in
  SM.protected_HW 17 (SM.run_ticks 17 (Z_to_bv 17 13) s 2) = 561%nat.
Proof. vm_compute. reflexivity. Qed.

Example nonwriting_instruction_preserves_pair :
  SM.protected_HW 17 (run [Observe 1%nat] 12 12 3) = 561%nat.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions SM.decode_encode_instr.
Print Assumptions SM.instruction_cycle_correct.
Print Assumptions SM.add_cycle_correct.
Print Assumptions SM.sub_cycle_correct.
Print Assumptions SM.mul_cycle_correct.
Print Assumptions SM.ladder_result_valid.
Print Assumptions SM.run_ticks_preserves_valid.
Print Assumptions SM.protected_HW_constant.
Print Assumptions SM.run_ticks_protected_HW.
Print Assumptions SM.state_HW_decomposition.
Print Assumptions SM.state_HW_public.
Print Assumptions SM.power_independence.
End StateMachineTests.
