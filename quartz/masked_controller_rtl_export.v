From quartz.lang Require Import domain Syntax transform.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import masked_controller masked_controller_storage hamming_weight.
From Stdlib Require Import String ZArith Bits.
Import fn Syntax.type InterfaceExample.QStdlib.
Import (notations) Syntax.eexpr Syntax.expr.
Local Open Scope string_scope.

Module MaskedControllerRTL.
Module C := MaskedController.
Module M := C.M.

Definition Response n := Pair (C.State n) (Pair Bool (M.Shares (S n))).

Definition gated_output {var} n : fn var (C.State n) (M.Shares (S n)) :=
  Fn (fun s => quartz_eexpr:(
    let status := {C.ready n} (#s) in
    let value := {C.output n} (#s) in
    return $(Syntax.expr.If (Syntax.expr.Var status) (Syntax.expr.Var value)
      (Syntax.expr.Const (t := M.Shares (S n)) (type.default (M.Shares (S n))))))).

(* Status and output describe the current state; only next_state is clocked. *)
Definition cycle {var} n : fn var (C.Input n) (Response n) :=
  Fn (fun request => quartz_eexpr:(
    let next_state := {C.tick n} (#request) in
    let status := {C.ready n} (#request .1) in
    let value := {gated_output n} (#request .1) in
    return (#next_state,(#status,#value)))).

Theorem cycle_next n input :
  fst (fn.interp (cycle n) input) = fn.interp (C.tick n) input.
Proof. reflexivity. Qed.

Theorem cycle_ready n input :
  fst (snd (fn.interp (cycle n) input)) = fn.interp (C.ready n) (fst input).
Proof. reflexivity. Qed.

Lemma gated_output_interp n state :
  fn.interp (gated_output n) state =
  if Zmod.nonzero (fn.interp (C.ready n) state)
  then fn.interp (C.output n) state else type.default (M.Shares (S n)).
Proof. reflexivity. Qed.

Theorem output_before_ready n state :
  fn.interp (C.ready n) state = Zmod.embed_bool false ->
  fn.interp (gated_output n) state = type.default (M.Shares (S n)).
Proof. intro H. rewrite gated_output_interp, H. reflexivity. Qed.

Theorem output_when_ready n state :
  fn.interp (C.ready n) state = Zmod.embed_bool true ->
  fn.interp (gated_output n) state = fn.interp (C.output n) state.
Proof. intro H. rewrite gated_output_interp, H. reflexivity. Qed.

Theorem cycle_output n input :
  snd (snd (fn.interp (cycle n) input)) = fn.interp (gated_output n) (fst input).
Proof. reflexivity. Qed.

Theorem cycle_storage n input :
  RegisterHW.word_HW (@transform.type.pack (C.State n) (fst (fn.interp (cycle n) input))) =
  MaskedControllerStorage.state_HW n (fn.interp (C.tick n) input).
Proof. rewrite cycle_next. apply MaskedControllerStorage.state_HW_storage. Qed.

End MaskedControllerRTL.
Print Assumptions MaskedControllerRTL.cycle_next.
Print Assumptions MaskedControllerRTL.output_before_ready.
Print Assumptions MaskedControllerRTL.cycle_storage.
