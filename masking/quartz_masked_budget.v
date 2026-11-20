From Stdlib Require Import ZArith Bits.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import masked_arithmetic masked_controller masked_controller_schedule masked_controller_storage.
From Masking Require Import cube_encoding curve_snapshot_budget curve_trace_budget
  quartz_masked_execution noisy_leakage noisy_shares noisy_channel_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module QuartzMaskedBudget.
Module C := MaskedController.
Module Schedule := MaskedControllerSchedule.
Module E := QuartzMaskedExecution.
Module Storage := MaskedControllerStorage.

Lemma binary_headroom c b :
  Z.le (Z.of_nat c) (Z.pow 2 (Z.of_nat b)) -> leq c (2 ^ b).
Proof.
move=> H. apply/leP. apply (proj2 (Nat2Z.inj_le _ _)).
by rewrite CubeEncoding.expn_nat Nat2Z.inj_pow.
Qed.

Lemma schedule_factor : leq (C.scheduled_edges * C.groups) (2 ^ 22).
Proof.
apply: binary_headroom.
rewrite C.scheduled_edges_value /C.groups mulnE Nat2Z.inj_mul.
vm_compute. discriminate.
Qed.

Lemma scheduled_cost (R : realType) :
  C.scheduled_edges%:R * (C.groups%:R * (2:R)^-88) <= (2:R)^-66.
Proof.
apply: (@CurveTraceBudget.dyadic_headroom R (C.scheduled_edges * C.groups) 22 66).
- by rewrite mulrA natrM.
- exact: schedule_factor.
Qed.

(* This identifies the horizon with the checked launch-and-work schedule, not its arithmetic result. *)
Theorem scheduled_horizon : C.scheduled_edges = (1 + Schedule.work_edges)%nat /\
  C.scheduled_edges = 8680%nat /\ C.scheduled_edges.+1 = 8681%nat.
Proof.
split; first exact: esym Schedule.edge_count.
split; first exact: C.scheduled_edges_value.
by rewrite C.scheduled_edges_value.
Qed.

Theorem scheduled_ready n input first_randomness randomness :
  fn.interp (C.ready n)
    (Schedule.ticks n Schedule.work_edges randomness (Schedule.launch n input first_randomness)) =
  bits.of_Z 1 1.
Proof. exact: Schedule.complete_tick_ready. Qed.

Section Execution.
Variable R : realType.
Variables bound count : nat.
Variables H A : finType.
Local Notation O := [the finType of 'I_bound.+1].
Local Notation S := [the finType of (E.Bank 255 * H)%type].
Variables reset start : nat -> bits 1.
Variables port1 port2 : A -> (type.interp C.Load * type.interp (MaskedArithmetic.Masks 256))%type.
Variables policy1 policy2 : nat -> S -> R.-fdist A.
Variables update1 update2 : nat -> H -> A -> O -> H.
Variables initial_update1 initial_update2 : H -> O -> H.
Hypothesis capacity : leq (16 + C.groups * (256 * 255) + count)%nat bound.
Local Notation noise := (NoisyChannelBridge.scalar_channel R bound count).
Local Notation run1 := (@E.initial_execution R 255 H A O reset start (fun _ => noise) noise
  port1 policy1 update1 initial_update1 C.scheduled_edges).
Local Notation run2 := (@E.initial_execution R 255 H A O reset start (fun _ => noise) noise
  port2 policy2 update2 initial_update2 C.scheduled_edges).

Lemma actual_linear_contract q (d e : R.-fdist H) :
  NoisyLeakage.TV (run1 d) (run2 e) <= C.scheduled_edges%:R * (C.groups%:R * (2:R)^-88) /\
  NoisyLeakage.TV (NoisyLeakage.iid (run1 d) q) (NoisyLeakage.iid (run2 e) q) <=
    q%:R * (C.scheduled_edges%:R * (C.groups%:R * (2:R)^-88)) /\
  forall (state : type.interp (C.State 255))
      (coins : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count),
    val (inord (Storage.state_HW 255 state + NoisyShares.noise_sum coins) : 'I_bound.+1) =
      (Storage.state_HW 255 state + NoisyShares.noise_sum coins)%nat.
Proof.
apply: (@E.binomial_execution_contract R 255 bound count H A reset start
  port1 port2 policy1 policy2 update1 update2 initial_update1 initial_update2 ((2:R)^-88)).
- by [].
- by rewrite invr_ge0 exprn_ge0 ?ler0n.
- exact: CurveSnapshotBudget.real_budget_256.
- exact: capacity.
Qed.

Theorem execution_256 (d e : R.-fdist H) :
  NoisyLeakage.TV (run1 d) (run2 e) <= (2:R)^-66.
Proof.
have [Hsingle _] := actual_linear_contract 0%nat d e.
exact: le_trans Hsingle (scheduled_cost R).
Qed.

Theorem repeated_execution_256 q (d e : R.-fdist H) :
  leq q (2 ^ 32) ->
  NoisyLeakage.TV (NoisyLeakage.iid (run1 d) q) (NoisyLeakage.iid (run2 e) q) <= (2:R)^-34.
Proof.
move=> Hq. have [_ [Hrepeat _]] := actual_linear_contract q d e.
apply: (@CurveTraceBudget.dyadic_headroom R q 32 34) _ Hq.
apply: le_trans Hrepeat _.
apply: ler_wpM2l (scheduled_cost R). exact: ler0n.
Qed.

(* All 8681 samples include the full stored-state HW; the initial sample is public. *)
Theorem binomial_execution_256 q (d e : R.-fdist H) :
  leq q (2 ^ 32) ->
  NoisyLeakage.TV (run1 d) (run2 e) <= (2:R)^-66 /\
  NoisyLeakage.TV (NoisyLeakage.iid (run1 d) q) (NoisyLeakage.iid (run2 e) q) <= (2:R)^-34 /\
  forall (state : type.interp (C.State 255))
      (coins : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count),
    val (inord (Storage.state_HW 255 state + NoisyShares.noise_sum coins) : 'I_bound.+1) =
      (Storage.state_HW 255 state + NoisyShares.noise_sum coins)%nat.
Proof.
move=> Hq. split; first exact: execution_256.
split; first exact: repeated_execution_256 Hq.
have [_ [_ Hclip]] := actual_linear_contract q d e. exact Hclip.
Qed.
End Execution.
End QuartzMaskedBudget.

Print Assumptions QuartzMaskedBudget.schedule_factor.
Print Assumptions QuartzMaskedBudget.scheduled_ready.
Print Assumptions QuartzMaskedBudget.execution_256.
Print Assumptions QuartzMaskedBudget.repeated_execution_256.
Print Assumptions QuartzMaskedBudget.binomial_execution_256.
