From Stdlib Require Import ZArith Bits List Lia.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import accelerator accelerator_correctness accelerator_ladder_bridge
  hamming_weight protected_accelerator.
Import ListNotations.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module ProtectedAcceleratorSecurity.
  Module P := ProtectedAccelerator.
  Module C := LadderAccelerator.

  Definition bank_HW (s : P.ProtectedState) : nat :=
    (RegisterHW.bank_HW (P.core_words (P.core s)) + RegisterHW.bank_HW (P.dual_words s))%nat.

  Theorem protected_bank_HW_constant s :
    P.valid s -> bank_HW s = 8160%nat.
  Proof.
    intros H. unfold bank_HW, P.valid in *.
    rewrite H, RegisterHW.bank_complement by lia. reflexivity.
  Qed.

  (* All stored accelerator bits: both data banks and the public 5-bit phase. *)
  Definition register_HW (s : P.ProtectedState) : nat :=
    (bank_HW s + RegisterHW.word_HW (fn.interp C.phase_value (P.core s)))%nat.

  Lemma register_HW_equal s1 s2 :
    P.valid s1 -> P.valid s2 ->
    fn.interp C.phase_value (P.core s1) = fn.interp C.phase_value (P.core s2) ->
    register_HW s1 = register_HW s2.
  Proof.
    intros H1 H2 Hphase. unfold register_HW.
    rewrite !protected_bank_HW_constant by assumption. rewrite Hphase. reflexivity.
  Qed.

  Fixpoint leakage_trace (cycles : nat) (s : P.ProtectedState) : list nat :=
    register_HW s ::
      match cycles with
      | O => []
      | S rest => leakage_trace rest (fn.interp P.tick s)
      end.

  Theorem register_trace_independent cycles s1 s2 :
    P.valid s1 -> P.valid s2 ->
    fn.interp C.phase_value (P.core s1) = fn.interp C.phase_value (P.core s2) ->
    leakage_trace cycles s1 = leakage_trace cycles s2.
  Proof.
    revert s1 s2. induction cycles; intros s1 s2 H1 H2 Hphase; cbn [leakage_trace].
    - rewrite (register_HW_equal s1 s2 H1 H2 Hphase). reflexivity.
    - f_equal.
      + apply register_HW_equal; assumption.
      + apply IHcycles; try apply P.tick_valid.
        rewrite !P.tick_core. apply C.tick_phase_independent. exact Hphase.
  Qed.

  Theorem initialized_trace_independent cycles x1 x2 z2 x3 z3 y1 y2 w2 y3 w3 :
    leakage_trace cycles (P.initial x1 x2 z2 x3 z3) =
    leakage_trace cycles (P.initial y1 y2 w2 y3 w3).
  Proof.
    apply register_trace_independent; try apply P.initial_valid.
    rewrite !P.initial_core. reflexivity.
  Qed.

  Theorem ladder_step_correct x1 x2 z2 x3 z3 :
    0 <= x1 < C.prime -> 0 <= x2 < C.prime -> 0 <= z2 < C.prime ->
    0 <= x3 < C.prime -> 0 <= z3 < C.prime ->
    AcceleratorCorrectness.output_Z (P.core (P.run 18 (P.initial x1 x2 z2 x3 z3))) =
    AcceleratorLadderBridge.mathematical_step x1 x2 z2 x3 z3.
  Proof.
    intros. rewrite P.run_core, P.initial_core.
    apply AcceleratorLadderBridge.ladder_step_matches_math; assumption.
  Qed.

  (* The reference trace fixes only public control, not the result. *)
  Theorem ladder_step_correct_and_secure x1 x2 z2 x3 z3 :
    0 <= x1 < C.prime -> 0 <= x2 < C.prime -> 0 <= z2 < C.prime ->
    0 <= x3 < C.prime -> 0 <= z3 < C.prime ->
    AcceleratorCorrectness.output_Z (P.core (P.run 18 (P.initial x1 x2 z2 x3 z3))) =
      AcceleratorLadderBridge.mathematical_step x1 x2 z2 x3 z3 /\
    leakage_trace 18 (P.initial x1 x2 z2 x3 z3) = leakage_trace 18 (P.initial 0 0 0 0 0).
  Proof.
    intros. split.
    - apply ladder_step_correct; assumption.
    - apply initialized_trace_independent.
  Qed.

End ProtectedAcceleratorSecurity.

Print Assumptions ProtectedAcceleratorSecurity.ladder_step_correct_and_secure.
