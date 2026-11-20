From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import accelerator.
From Stdlib Require Import ZArith Bits Vector.
Import fn type.
Import InterfaceExample.QStdlib.
Import (coercions) domain.Zmod.
Open Scope Z_scope.

Module ProtectedAccelerator.
  Module Core := LadderAccelerator.
  Definition Bank := Array (Bits 255) 32.
  Definition ProtectedState := Pair Core.State Bank.
  Definition State := ProtectedState.
  Import (notations) eexpr expr.
  Local Open Scope string_scope.

  Definition core (s : ProtectedState) : Core.State :=
    fst s.
  Definition dual_words (s : ProtectedState) : Vector.t (bits 255) 32 :=
    snd s.
  Definition bank_value {var} : fn var Core.State Bank :=
    Fn (fun s => quartz_eexpr:(return #s..Core.bank)).
  Definition core_words (s : Core.State) : Vector.t (bits 255) 32 :=
    fn.interp bank_value s.

  (* The recursion unrolls into 32 fixed-address complement writes. *)
  Fixpoint copy_complements {var} (count : nat) : fn var (Pair Bank Bank) Bank :=
    match count with
    | O => Fn (fun p => quartz_eexpr:(return #p .2))
    | S n => Fn (fun p => quartz_eexpr:(
        let src := #p .1 in
        let dst := {copy_complements n} (#p) in
        let value := #src[$(expr.Const (t := Bits 5) (bits.of_Z 5 (Z.of_nat n)))] in
        let dst <- #dst[$(expr.Const (t := Bits 5) (bits.of_Z 5 (Z.of_nat n)))] =
          $(expr.Unop unop.Not (expr.Var value)) in
        return #dst))
    end.

  Definition protect {var} : fn var Core.State ProtectedState :=
    Fn (fun s => quartz_eexpr:(
      let bank := bank_value (#s) in
      let dual := {copy_complements 32} ((#bank, $(expr.Const (t := Bank) (type.default Bank)))) in
      return (#s, #dual))).

  (* Observation boundaries are atomic: core and complement banks update together. *)
  Definition tick {var} : fn var ProtectedState ProtectedState :=
    Fn (fun s => quartz_eexpr:(
      let next := Core.tick (#s .1) in
      return protect (#next))).

  Definition start {var} : fn var Core.Inputs ProtectedState :=
    Fn (fun input => quartz_eexpr:(
      let next := Core.start (#input) in
      return protect (#next))).

  Definition reset {var} : fn var ProtectedState ProtectedState :=
    Fn (fun s => quartz_eexpr:(
      let next := Core.reset (#s .1) in
      return protect (#next))).

  Definition ready {var} : fn var State Bool :=
    Fn (fun s => quartz_eexpr:(return Core.ready (#s .1))).

  Definition output {var} :
    fn var State (Pair (Pair (Bits 255) (Bits 255)) (Pair (Bits 255) (Bits 255))) :=
    Fn (fun s => quartz_eexpr:(return Core.output (#s .1))).

  Lemma ready_core s :
    fn.interp ready s = fn.interp Core.ready (core s).
  Proof. reflexivity. Qed.

  Lemma output_core s :
    fn.interp output s = fn.interp Core.output (core s).
  Proof. reflexivity. Qed.

  Definition valid (s : ProtectedState) : Prop :=
    dual_words s = Vector.map (@Zmod.not (2^255)) (core_words (core s)).

  Lemma copy_complements_correct (regs : Vector.t (bits 255) 32) :
    fn.interp (copy_complements 32) (regs, type.default Bank) =
    Vector.map (@Zmod.not (2^255)) regs.
  Proof.
    do 32 (pattern regs; apply Vector.caseS'; clear regs;
      let h := fresh "word" in intros h regs).
    pattern regs. apply Vector.case0. reflexivity.
  Qed.

  Lemma protect_core s :
    core (fn.interp protect s) = s.
  Proof. reflexivity. Qed.

  Lemma protect_dual s :
    dual_words (fn.interp protect s) = Vector.map (@Zmod.not (2^255)) (core_words s).
  Proof.
    change (fn.interp (copy_complements 32) (core_words s, type.default Bank) =
      Vector.map (@Zmod.not (2^255)) (core_words s)).
    apply copy_complements_correct.
  Qed.

  Theorem protect_valid s : valid (fn.interp protect s).
  Proof. unfold valid. rewrite protect_core, protect_dual. reflexivity. Qed.

  Lemma tick_interp s :
    fn.interp tick s = fn.interp protect (fn.interp Core.tick (core s)).
  Proof. reflexivity. Qed.

  Lemma start_interp input :
    fn.interp start input = fn.interp protect (fn.interp Core.start input).
  Proof. reflexivity. Qed.

  Lemma reset_interp s :
    fn.interp reset s = fn.interp protect (fn.interp Core.reset (core s)).
  Proof. reflexivity. Qed.

  Theorem tick_valid s : valid (fn.interp tick s).
  Proof. rewrite tick_interp. apply protect_valid. Qed.

  Theorem start_valid input : valid (fn.interp start input).
  Proof. rewrite start_interp. apply protect_valid. Qed.

  Theorem reset_valid s : valid (fn.interp reset s).
  Proof. rewrite reset_interp. apply protect_valid. Qed.

  Theorem tick_core s :
    core (fn.interp tick s) = fn.interp Core.tick (core s).
  Proof. rewrite tick_interp, protect_core. reflexivity. Qed.

  Theorem start_core input :
    core (fn.interp start input) = fn.interp Core.start input.
  Proof. rewrite start_interp, protect_core. reflexivity. Qed.

  Theorem reset_core s :
    core (fn.interp reset s) = fn.interp Core.reset (core s).
  Proof. rewrite reset_interp, protect_core. reflexivity. Qed.

  Definition initial (x1 x2 z2 x3 z3 : Z) : ProtectedState :=
    fn.interp protect (Core.initial x1 x2 z2 x3 z3).

  Theorem initial_valid x1 x2 z2 x3 z3 :
    valid (initial x1 x2 z2 x3 z3).
  Proof. apply protect_valid. Qed.

  Lemma initial_core x1 x2 z2 x3 z3 :
    core (initial x1 x2 z2 x3 z3) = Core.initial x1 x2 z2 x3 z3.
  Proof. apply protect_core. Qed.

  Fixpoint run (cycles : nat) (s : ProtectedState) : ProtectedState :=
    match cycles with O => s | S rest => run rest (fn.interp tick s) end.

  Theorem run_core cycles s :
    core (run cycles s) = Core.run cycles (core s).
  Proof.
    revert s. induction cycles; intros s.
    - reflexivity.
    - cbn [run Core.run]. rewrite IHcycles, tick_core. reflexivity.
  Qed.

  Theorem run_valid cycles s : valid s -> valid (run cycles s).
  Proof.
    revert s. induction cycles; intros s H.
    - exact H.
    - apply IHcycles, tick_valid.
  Qed.
End ProtectedAccelerator.
