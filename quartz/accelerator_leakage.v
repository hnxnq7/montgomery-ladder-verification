From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import accelerator.
From Stdlib Require Import BinInt Bits List.
Import InterfaceExample fn type ListNotations LadderAccelerator.
Import QStdlib.
Import (coercions) domain.Zmod.
Open Scope Z_scope.

Module LadderAcceleratorLeakage.
  Import (notations) eexpr expr.
  Local Open Scope string_scope.

  Definition bank_word {var} (index : Z) : fn var State (Bits 255) :=
    Fn (fun s => quartz_eexpr:(return #s..bank[$(expr.Const (t := Bits 5) (bits.of_Z 5 index))])).

  Definition word_HW (w : bits 255) : nat :=
    List.fold_left (fun total i =>
      if Z.testbit (Zmod.unsigned w) (Z.of_nat i) then S total else total)
      (List.seq 0 255) 0%nat.

  (* All 32 stored words, excluding phase and combinational intermediates. *)
  Definition bank_HW (s : State) : nat :=
    List.fold_left (fun total i =>
      (total + word_HW (fn.interp (bank_word (Z.of_nat i)) s))%nat)
      (List.seq 0 32) 0%nat.

  (* Canonical accelerator coordinates, not a proved pair of full scalar-multiplication executions. *)
  Definition input_zero : State :=
    initial 9 0 1 9 1.
  Definition input_one : State :=
    initial 9 1 1 9 1.

  Lemma inputs_same_phase :
    fn.interp phase_value input_zero = fn.interp phase_value input_one.
  Proof. reflexivity. Qed.

  Lemma inputs_differ_one_bit :
    List.map (fun i => Z.lxor
      (Zmod.unsigned (fn.interp (bank_word (Z.of_nat i)) input_zero))
      (Zmod.unsigned (fn.interp (bank_word (Z.of_nat i)) input_one)))
      (List.seq 0 32) = [0;1] ++ List.repeat 0 30.
  Proof. vm_compute. reflexivity. Qed.

  Lemma initial_bank_HW_increment :
    bank_HW input_one = S (bank_HW input_zero).
  Proof. vm_compute. reflexivity. Qed.

  Theorem initial_bank_HW_distinguishes :
    bank_HW input_zero <> bank_HW input_one.
  Proof. vm_compute. discriminate. Qed.

  (* Fixed scheduling does not make the unprotected bank's HW independent. *)
  Theorem same_control_different_bank_HW cycles :
    fn.interp phase_value (run cycles input_zero) =
      fn.interp phase_value (run cycles input_one) /\
    bank_HW input_zero <> bank_HW input_one.
  Proof.
    split.
    - apply run_phase_independent, inputs_same_phase.
    - exact initial_bank_HW_distinguishes.
  Qed.

  Print Assumptions initial_bank_HW_distinguishes.
  Print Assumptions same_control_different_bank_HW.
End LadderAcceleratorLeakage.
