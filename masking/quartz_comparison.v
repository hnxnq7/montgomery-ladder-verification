From Stdlib Require Import List ZArith Bits.
From quartz.lang Require Import Syntax.
From LadderQuartz Require Import controller_protection masked_controller_storage.
From Crypto Require Import Spec.Curve25519 Arithmetic.PrimeFieldTheorems.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import noisy_leakage noisy_channel_bridge noisy_shares
  quartz_noise_bridge quartz_masked_ladder_security.

Set Default Proof Mode "Classic".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module QuartzComparison.
Module D := ControllerProtection.
Module B := QuartzNoiseBridge.
Module M := QuartzMaskedLadderSecurity.
Module C := M.C.
Module Storage := MaskedControllerStorage.

Definition ticks := 8680%nat.

Lemma common_horizon : C.scheduled_edges = ticks /\ ticks.+1 = 8681%nat.
Proof. split; reflexivity. Qed.

Section Comparison.
Variable R : realType.
Variables bound count : nat.
Hypothesis dual_capacity : leq (Z.to_nat D.width + count)%nat bound.
Hypothesis masked_capacity : leq (16 + C.groups * (256 * 255) + count)%nat bound.

(* Both laws observe actual stored HW through the same scalar channel. *)
Definition dual_law point scalar :=
  @B.binomial_run R bound count ticks (D.curve_initial point scalar).
Definition masked_law point scalar := @M.curve_trace R 255 bound count point scalar.

Lemma dual_laws_equal point scalar1 scalar2 :
  dual_law point scalar1 = dual_law point scalar2.
Proof.
rewrite /dual_law /B.binomial_run.
apply: B.observed_run_equal; exact: D.init_valid.
Qed.

Lemma dual_TV_zero point scalar1 scalar2 :
  TV (dual_law point scalar1) (dual_law point scalar2) = 0.
Proof. by rewrite (dual_laws_equal point scalar1 scalar2) TV_self. Qed.

Lemma dual_iid_TV_zero q point scalar1 scalar2 :
  TV (iid (dual_law point scalar1) q) (iid (dual_law point scalar2) q) = 0.
Proof. by rewrite (dual_laws_equal point scalar1 scalar2) TV_self. Qed.

Definition dual_unclipped point scalar :=
  forall h (coins : repetitions_type [the finType of (bool : Type)] count),
    List.In h (D.trace ticks (D.curve_initial point scalar)) ->
    val (inord (h + NoisyShares.noise_sum coins) : 'I_bound.+1) =
      (h + NoisyShares.noise_sum coins)%nat.

Lemma dual_no_clip point scalar : dual_unclipped point scalar.
Proof.
move=> h coins Hin.
exact (@B.binomial_no_clip bound count ticks (D.curve_initial point scalar) h coins
  (D.init_valid _) Hin dual_capacity).
Qed.

Definition masked_unclipped :=
  forall (state : Syntax.type.interp (C.State 255))
    (coins : repetitions_type [the finType of (bool : Type)] count),
    val (inord (Storage.state_HW 255 state + NoisyShares.noise_sum coins) : 'I_bound.+1) =
      (Storage.state_HW 255 state + NoisyShares.noise_sum coins)%nat.

(* Correctness is at each implementation's own completion time; release is not observed. *)
Definition dual_correct point scalar :=
  Zmod.unsigned (fn.interp D.Core.output (fst (D.run 5612 (D.curve_initial point scalar)))) =
    F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult scalar point)).

Definition masked_correct point scalar :=
  forall masks coins,
    M.B.canonical 255 C.groups (@M.curve_run 255 point scalar masks coins).2 /\
    C.reconstruct_group 255 (fn.interp (C.output 255) (@M.curve_run 255 point scalar masks coins)) =
      Curve25519.M.X0 (Curve25519.M.scalarmult scalar point) /\
    fn.interp (C.ready 255) (@M.curve_run 255 point scalar masks coins) = bits.of_Z 1 1.

Theorem common_budget_correct_and_secure q (point : Curve25519.M.point) (scalar1 scalar2 : Z) :
  (Z.le 0 scalar1 /\ Z.lt scalar1 (Z.pow 2 255)) ->
  (Z.le 0 scalar2 /\ Z.lt scalar2 (Z.pow 2 255)) -> leq q (2 ^ 32) ->
  dual_correct point scalar1 /\ dual_correct point scalar2 /\
  masked_correct point scalar1 /\ masked_correct point scalar2 /\
  TV (dual_law point scalar1) (dual_law point scalar2) = 0 /\
  TV (iid (dual_law point scalar1) q) (iid (dual_law point scalar2) q) = 0 /\
  TV (masked_law point scalar1) (masked_law point scalar2) <= (2:R)^-66 /\
  TV (iid (masked_law point scalar1) q) (iid (masked_law point scalar2) q) <= (2:R)^-34 /\
  dual_unclipped point scalar1 /\ dual_unclipped point scalar2 /\ masked_unclipped.
Proof.
move=> H1 H2 Hq.
have [HM1 [HM2 [HT [HQ HC]]]] :=
  @M.ladder_correct_and_noisy_secure_256 R bound count masked_capacity q point scalar1 scalar2 H1 H2 Hq.
split; first exact: D.program_correct H1.
split; first exact: D.program_correct H2.
split; first exact HM1.
split; first exact HM2.
split; first exact: dual_TV_zero.
split; first exact: dual_iid_TV_zero.
split; first exact HT.
split; first exact HQ.
split; first exact: dual_no_clip.
split; [exact: dual_no_clip | exact HC].
Qed.

End Comparison.
End QuartzComparison.
Print Assumptions QuartzComparison.common_horizon.
Print Assumptions QuartzComparison.common_budget_correct_and_secure.
