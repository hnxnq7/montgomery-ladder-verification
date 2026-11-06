Require Import ladder_math.
Require Import ladder_machine.
Require Import state_machine processor_refinement.
From stdpp Require Import bitvector list.
From Crypto Require Import Spec.ModularArithmetic Arithmetic.ModularArithmeticTheorems Curves.Montgomery.XZ.
From Crypto Require Import Util.LetIn Util.Loops.
From Crypto Require Import Spec.Curve25519 Curves.Montgomery.XZProofs Arithmetic.PrimeFieldTheorems.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Require curve25519_math.
Module Curve25519Bridge := curve25519_math.Curve25519Bridge.

(* Complete instruction-level program, not the cycle-level processor. *)
Module Curve25519Machine.
  Local Notation q := (2^255-19)%positive.

  Definition modulus : bv 255 :=
    Z_to_bv 255 (Z.pos q).

  Definition inverse_exponent : positive :=
    (2^255-21)%positive.

  Definition program : list LadderMachine.instr :=
    LadderMachine.affine_program 255 inverse_exponent.

  Definition initial (x scalar : Z) : dual_circuit.state 255 :=
    LadderMachine.initial_state 255 (Z_to_bv 255 x) (Z_to_bv 255 121666) (Z_to_bv 255 scalar).

  Definition execute (x scalar : Z) :=
    LadderMachine.run 255 modulus (initial x scalar) program.

  Definition output (x scalar : Z) : Z :=
    LadderMachine.affine_result 255 (execute x scalar).1.

  Lemma modulus_unsigned : bv_unsigned modulus = Z.pos q.
  Proof. apply Z_to_bv_small. vm_compute. split; congruence. Qed.

  Local Lemma field_affine_power X Zc :
    F.to_Z (Curve25519Bridge.affine_output q (X, Zc)) = (X * Zc ^ Z.pos inverse_exponent) mod Z.pos q.
  Proof.
    unfold Curve25519Bridge.affine_output.
    rewrite (@F.Fq_inv_fermat q Curve25519.prime_p ltac:(vm_compute; reflexivity)).
    rewrite F.of_Z_pow, F.to_Z_mul, !F.to_Z_of_Z.
    repeat rewrite ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r, ?Z.mod_mod by (vm_compute; discriminate).
    reflexivity.
  Qed.

  Theorem program_correct (P : Curve25519.M.point) scalar :
    0 <= scalar < 2^255 ->
    output (F.to_Z (Curve25519.M.X0 P)) scalar = F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult scalar P)).
  Proof.
    intro Hscalar. unfold output, execute, initial, program.
    rewrite LadderMachine.affine_program_correct by (rewrite modulus_unsigned; vm_compute; reflexivity).
    rewrite modulus_unsigned.
    rewrite (Z_to_bv_small 255 scalar) by exact Hscalar.
    rewrite (Z_to_bv_small 255 121666) by (vm_compute; split; congruence).
    rewrite Z_to_bv_small.
    - rewrite <- Curve25519Bridge.curve25519_cswap_correct with (m := 255%nat) by exact Hscalar.
      unfold Curve25519Bridge.curve25519_cswap.
      destruct (ladder_math.MontLadderCSwap (Z.pos q) 121666 255 (F.to_Z (Curve25519.M.X0 P)) scalar).
      symmetry. apply field_affine_power.
    - pose proof (F.to_Z_range (Curve25519.M.X0 P) ltac:(vm_compute; reflexivity)) as H.
      change (0 <= F.to_Z (Curve25519.M.X0 P) < 2^255).
      change (0 <= F.to_Z (Curve25519.M.X0 P) < Z.pos q) in H.
      split; [lia |]. eapply Z.lt_trans; [exact (proj2 H) | vm_compute; reflexivity].
  Qed.

  Lemma program_length : length program = 7400%nat.
  Proof.
    unfold program, LadderMachine.affine_program. rewrite List.length_app, LadderMachine.projective_program_length.
    vm_compute. reflexivity.
  Qed.

  Lemma program_in_bounds : Forall (LadderMachine.in_bounds 28) program.
  Proof. apply LadderMachine.affine_program_in_bounds. Qed.

  Theorem program_secure x scalar :
    LadderMachine.hw_trace 255 modulus (initial x scalar) program = repeat 7140%nat 7401 /\
    (execute x scalar).2 = [] /\ dual_circuit.valid_state 255 (execute x scalar).1.
  Proof.
    pose proof (LadderMachine.affine_program_secure 255 modulus
      (Z_to_bv 255 x) (Z_to_bv 255 121666) (Z_to_bv 255 scalar) 255 inverse_exponent) as H.
    change (LadderMachine.hw_trace 255 modulus (initial x scalar) program = repeat 7140%nat (S (length program)) /\
      (execute x scalar).2 = [] /\ dual_circuit.valid_state 255 (execute x scalar).1) in H.
    rewrite program_length in H. exact H.
  Qed.

  Theorem protected_ladder_correct_and_secure (P : Curve25519.M.point) scalar :
    0 <= scalar < 2^255 ->
    length program = 7400%nat /\
    Forall (LadderMachine.in_bounds 28) program /\
    output (F.to_Z (Curve25519.M.X0 P)) scalar = F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult scalar P)) /\
    LadderMachine.hw_trace 255 modulus (initial (F.to_Z (Curve25519.M.X0 P)) scalar) program = repeat 7140%nat 7401 /\
    (execute (F.to_Z (Curve25519.M.X0 P)) scalar).2 = [] /\
    dual_circuit.valid_state 255 (execute (F.to_Z (Curve25519.M.X0 P)) scalar).1.
  Proof.
    intro Hscalar. split; [apply program_length |]. split; [apply program_in_bounds |].
    split; [apply program_correct; exact Hscalar | apply program_secure].
  Qed.

  Corollary power_trace_independent x scalar1 scalar2 :
    LadderMachine.hw_trace 255 modulus (initial x scalar1) program =
    LadderMachine.hw_trace 255 modulus (initial x scalar2) program.
  Proof. rewrite (proj1 (program_secure x scalar1)), (proj1 (program_secure x scalar2)). reflexivity. Qed.
End Curve25519Machine.

Module Curve25519Processor.
  Module SM := StateMachine.
  Module PR := ProcessorRefinement.
  Module CM := Curve25519Machine.
  Local Opaque SM.run_ticks SM.hw_trace LadderMachine.run.

  Definition program :=
    PR.encoded_program 255 CM.program.

  Definition initial (x scalar : Z) :=
    SM.mk_processor_state 255 program
      (PR.initial_regs 255 (Z_to_bv 255 x) (Z_to_bv 255 121666) (Z_to_bv 255 scalar)).

  Definition cycles : nat :=
    3 * length CM.program.

  Definition execute (x scalar : Z) :=
    PR.run_program 255 CM.modulus
      (PR.initial_regs 255 (Z_to_bv 255 x) (Z_to_bv 255 121666) (Z_to_bv 255 scalar)) CM.program.

  Definition output (x scalar : Z) : Z :=
    PR.affine_output 255 (execute x scalar).

  (* The trace ends before the intended output is released. *)
  Definition leakage (x scalar : Z) : list nat :=
    SM.hw_trace 255 CM.modulus (initial x scalar) cycles.

  Lemma program_length : length program = 7400%nat.
  Proof. unfold program, PR.encoded_program. rewrite !List.length_map. apply CM.program_length. Qed.

  Lemma cycles_count : cycles = 22200%nat.
  Proof. unfold cycles. rewrite CM.program_length. reflexivity. Qed.

  Lemma program_bit_indices : Forall PR.bit_index_fits CM.program.
  Proof. apply PR.affine_bit_indices. lia. Qed.

  Lemma program_fits : Z.of_nat (length CM.program) < 2 ^ Z.of_N 255.
  Proof. rewrite CM.program_length. vm_compute. reflexivity. Qed.

  Lemma execute_refines x scalar :
    PR.registers_match 255 (SM.Regs 255 (execute x scalar))
      (dual_circuit.env 255 (CM.execute x scalar).1).
  Proof.
    exact (PR.run_program_refines 255 CM.modulus _ (CM.initial x scalar) CM.program
      ltac:(lia) eq_refl CM.program_in_bounds program_bit_indices program_fits
      (PR.initial_registers_match 255 _ _ _)).
  Qed.

  Lemma output_refines x scalar : output x scalar = CM.output x scalar.
  Proof.
    unfold output, PR.affine_output, CM.output, LadderMachine.affine_result.
    rewrite (execute_refines x scalar); [reflexivity |].
    unfold CM.execute. rewrite LadderMachine.run_preserves_length. unfold CM.initial.
    rewrite LadderMachine.initial_state_length. lia.
  Qed.

  Theorem program_correct (P : Curve25519.M.point) scalar :
    0 <= scalar < 2^255 ->
    output (F.to_Z (Curve25519.M.X0 P)) scalar =
      F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult scalar P)).
  Proof. intro Hscalar. rewrite output_refines. apply CM.program_correct, Hscalar. Qed.

  Theorem program_boundary x scalar :
    SM.pc 255 (execute x scalar) = Z_to_bv 255 7400 /\
    SM.Stage 255 (execute x scalar) = SM.Fetch.
  Proof.
    pose proof (PR.run_program_boundary 255 CM.modulus
      (PR.initial_regs 255 (Z_to_bv 255 x) (Z_to_bv 255 121666) (Z_to_bv 255 scalar)) CM.program
      ltac:(lia) CM.program_in_bounds program_bit_indices program_fits) as H.
    rewrite CM.program_length in H. exact H.
  Qed.

  Theorem program_valid x scalar : SM.valid_state 255 (execute x scalar).
  Proof. apply SM.run_ticks_preserves_valid, SM.mk_processor_state_valid. Qed.

  Theorem power_trace_independent x scalar1 scalar2 : leakage x scalar1 = leakage x scalar2.
  Proof. apply SM.processor_trace_independent. Qed.

  Lemma leakage_length x scalar : length (leakage x scalar) = 22201%nat.
  Proof. unfold leakage. rewrite SM.hw_trace_length, cycles_count. reflexivity. Qed.

  (* Correct output and equal cycle-by-cycle aggregate HW for the same public point. *)
  Theorem protected_ladder_correct_and_secure (P : Curve25519.M.point) scalar1 scalar2 :
    0 <= scalar1 < 2^255 -> 0 <= scalar2 < 2^255 ->
    let x := F.to_Z (Curve25519.M.X0 P) in
    output x scalar1 = F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult scalar1 P)) /\
    output x scalar2 = F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult scalar2 P)) /\
    leakage x scalar1 = leakage x scalar2 /\
    length (leakage x scalar1) = 22201%nat /\
    SM.valid_state 255 (execute x scalar1) /\ SM.valid_state 255 (execute x scalar2).
  Proof.
    intros H1 H2 x. split; [apply program_correct, H1 |]. split; [apply program_correct, H2 |].
    split; [apply power_trace_independent |]. split; [apply leakage_length |].
    split; apply program_valid.
  Qed.
End Curve25519Processor.
