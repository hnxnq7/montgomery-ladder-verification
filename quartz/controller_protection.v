From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax transform.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import ladder_controller hamming_weight packed_storage.
From Crypto Require Import Spec.Curve25519 Arithmetic.PrimeFieldTheorems.
Require Import curve25519_math.
From Stdlib Require Import ZArith Bits List Lia.
Import fn Syntax.type InterfaceExample.QStdlib ListNotations.
Import (coercions) domain.Zmod.
Open Scope Z_scope.

Module ControllerProtection.
  Module Core := LadderController.
  Definition width := type.size Core.State.
  Definition State := Pair Core.State (Bits width).

  Lemma core_well_formed : transform.type.wf Core.State.
  Proof. vm_compute. repeat split; intros; try reflexivity; discriminate. Qed.

  Definition pack_state {var} : fn var Core.State (Bits width) :=
    Fn (fun s => eexpr.pack core_well_formed (Syntax.expr.Var s)).

  Lemma pack_state_correct s : fn.interp pack_state s = @type.pack Core.State s.
  Proof.
    change (Syntax.eexpr.interp (eexpr.pack core_well_formed
      (@Syntax.expr.Var Syntax.type.interp Syntax.type.interpfn Core.State s)) = @type.pack Core.State s).
    apply eexpr.interp_pack.
  Qed.

  Import (notations) Syntax.eexpr Syntax.expr.
  Local Open Scope string_scope.

  (* Pair every stored controller field, including scalar, swap bit, and core scratch. *)
  Definition protect {var} : fn var Core.State State :=
    Fn (fun s => quartz_eexpr:(
      let packed := pack_state (#s) in
      let dual := $(Syntax.expr.Unop unop.Not (Syntax.expr.Var packed)) in
      return (#s, #dual))).

  Definition init {var} : fn var Core.Inputs State :=
    Fn (fun input => quartz_eexpr:(
      let next := Core.init (#input) in
      return protect (#next))).

  Definition tick {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let next := Core.tick (#s .1) in
      return protect (#next))).

  Definition valid (s : State) : Prop :=
    snd s = Zmod.not (@type.pack Core.State (fst s)).

  Definition state_HW (s : State) : nat :=
    (RegisterHW.word_HW (@type.pack Core.State (fst s)) + RegisterHW.word_HW (snd s))%nat.

  Lemma core_plain : PackedStorage.plain Core.State.
  Proof. vm_compute. repeat split; discriminate. Qed.

  Theorem state_HW_storage s : state_HW s = PackedStorage.storage_HW State s.
  Proof.
    unfold state_HW.
    change ((RegisterHW.word_HW (@type.pack Core.State (fst s)) + RegisterHW.word_HW (snd s))%nat =
      (PackedStorage.storage_HW Core.State (fst s) + RegisterHW.word_HW (snd s))%nat).
    rewrite PackedStorage.pack_HW by exact core_plain. reflexivity.
  Qed.

  Lemma protect_interp s : fn.interp protect s = (s, Zmod.not (@type.pack Core.State s)).
  Proof.
    change ((s, Zmod.not (fn.interp pack_state s)) = (s, Zmod.not (@type.pack Core.State s))).
    rewrite pack_state_correct. reflexivity.
  Qed.

  Lemma tick_interp s : fn.interp tick s = fn.interp protect (fn.interp Core.tick (fst s)).
  Proof. reflexivity. Qed.

  Theorem protect_valid s : valid (fn.interp protect s).
  Proof. unfold valid. rewrite protect_interp. reflexivity. Qed.

  Theorem init_valid input : valid (fn.interp init input).
  Proof. apply protect_valid. Qed.

  Theorem tick_valid s : valid (fn.interp tick s).
  Proof. rewrite tick_interp. apply protect_valid. Qed.

  Theorem protected_HW_constant s : valid s -> state_HW s = Z.to_nat width.
  Proof.
    intro H. unfold state_HW, valid in *. rewrite H.
    apply RegisterHW.word_complement. apply eexpr.size_nonneg, core_well_formed.
  Qed.

  Fixpoint run (n : nat) (s : State) : State :=
    match n with O => s | S k => run k (fn.interp tick s) end.

  Theorem run_erasure n s : fst (run n s) = Core.run n (fst s).
  Proof.
    revert s. induction n; intros s; cbn [run Core.run]; [reflexivity|].
    rewrite IHn, tick_interp, protect_interp. reflexivity.
  Qed.

  Fixpoint trace (n : nat) (s : State) : list nat :=
    state_HW s :: match n with O => [] | S k => trace k (fn.interp tick s) end.

  Theorem trace_constant n s : valid s -> trace n s = repeat (Z.to_nat width) (S n).
  Proof.
    revert s. induction n; intros s H; cbn [trace repeat]; rewrite protected_HW_constant by exact H.
    - reflexivity.
    - rewrite IHn by apply tick_valid. reflexivity.
  Qed.

  Theorem trace_independent n s t : valid s -> valid t -> trace n s = trace n t.
  Proof. intros Hs Ht. rewrite !trace_constant by assumption. reflexivity. Qed.

  Definition curve_initial (P : Curve25519.M.point) (k : Z) : State :=
    fn.interp init (bits.of_Z 255 (F.to_Z (Curve25519.M.X0 P)), bits.of_Z 255 k).

  Theorem program_correct k (P : Curve25519.M.point) :
    0 <= k < 2^255 ->
    Zmod.unsigned (fn.interp Core.output (fst (run 5612 (curve_initial P k)))) =
    F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult k P)).
  Proof.
    intro Hk. rewrite run_erasure.
    change (Zmod.unsigned (fn.interp Core.output
      (Core.run 5612 (fn.interp Core.init
        (bits.of_Z 255 (F.to_Z (Curve25519.M.X0 P)), bits.of_Z 255 k)))) =
      F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult k P))).
    apply LadderControllerCurveBridge.controller_curve25519_correct. exact Hk.
  Qed.

  Theorem protected_ladder_correct_and_secure (P : Curve25519.M.point) k1 k2 :
    0 <= k1 < 2^255 -> 0 <= k2 < 2^255 ->
    Zmod.unsigned (fn.interp Core.output (fst (run 5612 (curve_initial P k1)))) =
      F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult k1 P)) /\
    Zmod.unsigned (fn.interp Core.output (fst (run 5612 (curve_initial P k2)))) =
      F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult k2 P)) /\
    trace 5612 (curve_initial P k1) = trace 5612 (curve_initial P k2).
  Proof.
    intros H1 H2. split; [apply program_correct; exact H1|].
    split; [apply program_correct; exact H2|].
    apply trace_independent; apply init_valid.
  Qed.
End ControllerProtection.

Print Assumptions ControllerProtection.run_erasure.
Print Assumptions ControllerProtection.state_HW_storage.
Print Assumptions ControllerProtection.trace_independent.
Print Assumptions ControllerProtection.protected_ladder_correct_and_secure.
