From Stdlib Require Import List ZArith Bits.
From quartz.lang Require Import Syntax.
From LadderQuartz Require Import controller_protection.
From Crypto Require Import Spec.Curve25519 Arithmetic.PrimeFieldTheorems.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import noisy_leakage noisy_channel_bridge noisy_shares.

Set Default Proof Mode "Classic".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module QuartzNoiseBridge.
Module Protected := ControllerProtection.

Section Observation.
Variable R : realType.
Variable O : finType.
Variable channel : nat -> R.-fdist O.

(* Each snapshot passes through the same channel; the controller trace is unchanged. *)
Fixpoint observe_trace (count : nat) (raw : list nat) : R.-fdist (repetitions_type O count) :=
  match count with
  | 0%N => fdist1 tt
  | k.+1 => channel (List.hd 0%N raw) >>= (fun y =>
      fdistmap (fun rest => (y, rest)) (observe_trace k (List.tl raw)))
  end.

Definition observed_run n s :=
  observe_trace n.+1 (Protected.trace n s).

Lemma raw_trace_length n s : List.length (Protected.trace n s) = n.+1.
Proof.
elim: n s => [|n IH] s; first reflexivity.
change (S (List.length (Protected.trace n (fn.interp Protected.tick s))) = S n.+1).
by rewrite IH.
Qed.

Theorem observed_run_equal n s t :
  Protected.valid s -> Protected.valid t -> observed_run n s = observed_run n t.
Proof.
move=> Hs Ht. rewrite /observed_run (Protected.trace_independent n s t Hs Ht).
reflexivity.
Qed.

Theorem observed_run_zero n s t :
  Protected.valid s -> Protected.valid t ->
  bounded_indistinguishable (0 : R) (observed_run n s) (observed_run n t).
Proof.
move=> Hs Ht. rewrite /bounded_indistinguishable (observed_run_equal n Hs Ht) TV_self.
exact: Order.POrderTheory.lexx.
Qed.

End Observation.

Section Binomial.
Variable R : realType.
Variables bound noise_count : nat.

Definition binomial_run n s :=
  observed_run (NoisyChannelBridge.scalar_channel R bound noise_count) n s.

(* A common bound may be chosen large enough for both implementations being compared. *)
Theorem binomial_no_clip n s h
    (noise : repetitions_type [the finType of (bool : Type)] noise_count) :
  Protected.valid s -> List.In h (Protected.trace n s) ->
  (Z.to_nat Protected.width + noise_count <= bound)%N ->
  val (inord (h + NoisyShares.noise_sum noise) : 'I_bound.+1) =
    (h + NoisyShares.noise_sum noise)%N.
Proof.
move=> Hvalid Hin Hbound.
rewrite (Protected.trace_constant n s Hvalid) in Hin.
have -> : h = Z.to_nat Protected.width by exact: List.repeat_spec Hin.
exact: NoisyChannelBridge.scalar_channel_no_clip.
Qed.

Definition full_curve_law (P : Curve25519.M.point) (k : Z) :=
  binomial_run 5612 (Protected.curve_initial P k).

Theorem full_curve_law_equal (P : Curve25519.M.point) k1 k2 :
  full_curve_law P k1 = full_curve_law P k2.
Proof. apply: observed_run_equal; exact: Protected.init_valid. Qed.

Theorem full_curve_contract (P : Curve25519.M.point) k1 k2 :
  bounded_indistinguishable (0 : R) (full_curve_law P k1) (full_curve_law P k2).
Proof.
rewrite /bounded_indistinguishable (full_curve_law_equal P k1 k2) TV_self.
exact: Order.POrderTheory.lexx.
Qed.

Corollary full_curve_no_clip (P : Curve25519.M.point) k h
    (noise : repetitions_type [the finType of (bool : Type)] noise_count) :
  List.In h (Protected.trace 5612 (Protected.curve_initial P k)) ->
  (Z.to_nat Protected.width + noise_count <= bound)%N ->
  val (inord (h + NoisyShares.noise_sum noise) : 'I_bound.+1) =
    (h + NoisyShares.noise_sum noise)%N.
Proof.
move=> Hin Hbound. apply: binomial_no_clip Hin Hbound.
exact: Protected.init_valid.
Qed.

Theorem full_curve_snapshot_count (P : Curve25519.M.point) k :
  List.length (Protected.trace 5612 (Protected.curve_initial P k)) = 5613%N.
Proof. exact: raw_trace_length. Qed.

Definition full_curve_unclipped (P : Curve25519.M.point) k : Prop :=
  forall h (noise : repetitions_type [the finType of (bool : Type)] noise_count),
    List.In h (Protected.trace 5612 (Protected.curve_initial P k)) ->
    val (inord (h + NoisyShares.noise_sum noise) : 'I_bound.+1) =
      (h + NoisyShares.noise_sum noise)%N.

(* Unclipped HW plus binomial noise, for the actual initialized controller runs. *)
Local Open Scope Z_scope.
Theorem protected_curve_correct_and_noisy_secure (P : Curve25519.M.point) (k1 k2 : Z) :
  (Z.to_nat Protected.width + noise_count <= bound)%N ->
  0 <= k1 < 2^255 -> 0 <= k2 < 2^255 ->
  Zmod.unsigned (fn.interp Protected.Core.output
    (fst (Protected.run 5612 (Protected.curve_initial P k1)))) =
      F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult k1 P)) /\
  Zmod.unsigned (fn.interp Protected.Core.output
    (fst (Protected.run 5612 (Protected.curve_initial P k2)))) =
      F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult k2 P)) /\
  bounded_indistinguishable (0%R : R) (full_curve_law P k1) (full_curve_law P k2) /\
  full_curve_unclipped P k1 /\ full_curve_unclipped P k2.
Proof.
move=> Hbound Hk1 Hk2.
split; first exact: Protected.program_correct Hk1.
split; first exact: Protected.program_correct Hk2.
split; first exact: full_curve_contract.
split; move=> h noise Hin; exact: full_curve_no_clip Hin Hbound.
Qed.

End Binomial.
End QuartzNoiseBridge.

Print Assumptions QuartzNoiseBridge.observed_run_equal.
Print Assumptions QuartzNoiseBridge.binomial_no_clip.
Print Assumptions QuartzNoiseBridge.full_curve_contract.
Print Assumptions QuartzNoiseBridge.full_curve_no_clip.
Print Assumptions QuartzNoiseBridge.protected_curve_correct_and_noisy_secure.
