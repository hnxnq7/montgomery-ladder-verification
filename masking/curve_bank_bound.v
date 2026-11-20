From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder fiat_field arithmetic_privacy arithmetic_channel
  arithmetic_bank_refresh arithmetic_product_bound field_aggregate_spectral curve_snapshot
  curve25519_snapshot field_history noisy_leakage noisy_trace noisy_channel_bridge noisy_shares.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module CurveBankBound.
Section Bank.
Variable R : realType.
Variable I : finType.
Variable n : nat.
Hypothesis shares : (1 <= n)%N.
Variable epsilon : R.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
Hypothesis budget : @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2.
Local Notation K := FiatField.curve25519.
Local Notation V := [the finZmodType of {ffun 'I_n.+1 -> K}].
Local Notation Bank := [the finZmodType of {ffun I -> V}].
Local Notation Values := [the finZmodType of {ffun I -> K}].
Local Notation Coins := [the finZmodType of {ffun I -> {ffun 'I_n -> K}}].
Local Notation M := (255*n.+1).+1%N.
Local Notation W := [the finType of 'I_M].
Local Notation Observations := [the finType of {ffun I -> W}].
Local Notation canonical := (@ArithmeticBankRefresh.canonical_bank_law R K I n).
Local Notation observe := (@FieldAggregateSpectral.observe FiatField.curve25519_modulus
  FiatField.curve25519_modulus_gt1 255 n).

Definition group_observations (a : Bank) : Observations :=
  [ffun i => observe (a i)].
Definition observation_sum (a : Observations) : nat :=
  \sum_i val (a i).
Definition bank_HW (a : Bank) : nat :=
  observation_sum (group_observations a).

Lemma group_law (s : Values) :
  fdistmap group_observations (canonical s) =
    ArithmeticChannel.independent (fun i => Curve25519Snapshot.law n R (s i)).
Proof.
  rewrite /canonical /ArithmeticBankRefresh.canonical_bank_law /group_observations.
  change (fdistmap (fun a : Bank => [ffun i => observe (a i)])
    (ArithmeticChannel.independent (fun i => ArithmeticPrivacy.sharing_law R n (s i))) =
    ArithmeticChannel.independent (fun i => fdistmap observe (ArithmeticPrivacy.sharing_law R n (s i)))).
  exact: ArithmeticBankRefresh.independent_map.
Qed.

Theorem group_TV_bound (s t : Values) :
  NoisyLeakage.TV (fdistmap group_observations (canonical s))
    (fdistmap group_observations (canonical t)) <= #|I|%:R * epsilon.
Proof.
  rewrite !group_law.
  apply: le_trans (ArithmeticProductBound.independent_TV_bound _ _) _.
  have E : (\sum_(i : I) epsilon) = #|I|%:R * epsilon.
    by rewrite sumr_const mulr_natl.
  rewrite -E. apply: ler_sum => i _.
  exact: (@Curve25519Snapshot.actual_TV_bound n shares R epsilon (s i) (t i)
    epsilon_nonnegative budget).
Qed.

Lemma bank_HW_bound (a : Bank) : (bank_HW a <= #|I| * (255*n.+1))%N.
Proof.
  have H : (bank_HW a <= \sum_(i : I) (255*n.+1))%N.
    apply: leq_sum => i _.
    exact: (ltn_ord (group_observations a i)).
  by rewrite sum_nat_const in H.
Qed.

Lemma binomial_bank_no_clip bound count (a : Bank)
    (noise : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count) :
  (#|I| * (255*n.+1) + count <= bound)%N ->
  val (inord (bank_HW a + NoisyShares.noise_sum noise) : 'I_bound.+1) =
    (bank_HW a + NoisyShares.noise_sum noise)%N.
Proof.
  move=> Hcapacity. apply: NoisyChannelBridge.scalar_channel_no_clip.
  apply: leq_trans _ Hcapacity. exact: leq_add (bank_HW_bound a) (leqnn count).
Qed.

Section Channel.
Variable O : finType.
Variable channel : nat -> R.-fdist O.

Definition observed_bank (s : Values) :=
  canonical s >>= (fun a => channel (bank_HW a)).

Theorem observed_bank_bound (s t : Values) :
  NoisyLeakage.TV (observed_bank s) (observed_bank t) <= #|I|%:R * epsilon.
Proof.
  have E v : observed_bank v = fdistmap group_observations (canonical v) >>=
      (fun a => channel (observation_sum a)).
    by rewrite bind_map.
  rewrite !E.
  exact: le_trans (NoisyLeakage.channel_TV_contraction _ _ _) (group_TV_bound s t).
Qed.

Definition refreshed_law (a : Bank) :=
  uniform R Coins >>= (fun r => channel (bank_HW (ArithmeticBankRefresh.refresh a r))).

Lemma refreshed_lawE (a : Bank) :
  refreshed_law a = observed_bank (ArithmeticBankRefresh.values a).
Proof.
  rewrite /refreshed_law /observed_bank -ArithmeticBankRefresh.refresh_law.
  by rewrite bind_map.
Qed.

Theorem refreshed_pair_bound (a b : Bank) :
  NoisyLeakage.TV (refreshed_law a) (refreshed_law b) <= #|I|%:R * epsilon.
Proof. by rewrite !refreshed_lawE; exact: observed_bank_bound. Qed.

(* Each bank is freshly and independently refreshed after sampling the prior. *)
Theorem arbitrary_prior_bound (d e : R.-fdist Bank) :
  NoisyLeakage.TV (d >>= refreshed_law) (e >>= refreshed_law) <= #|I|%:R * epsilon.
Proof. exact: FieldHistory.mixture_TV_bound refreshed_pair_bound d e. Qed.

End Channel.

Theorem binomial_prior_bound bound count (d e : R.-fdist Bank) :
  (#|I| * (255*n.+1) + count <= bound)%N ->
  NoisyLeakage.TV
    (d >>= refreshed_law (NoisyChannelBridge.scalar_channel R bound count))
    (e >>= refreshed_law (NoisyChannelBridge.scalar_channel R bound count)) <= #|I|%:R * epsilon /\
  forall (a : Bank) (noise : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count),
    val (inord (bank_HW a + NoisyShares.noise_sum noise) : 'I_bound.+1) =
      (bank_HW a + NoisyShares.noise_sum noise)%N.
Proof.
  move=> Hcapacity. split; first exact: arbitrary_prior_bound.
  move=> a noise. exact: binomial_bank_no_clip Hcapacity.
Qed.

End Bank.
End CurveBankBound.

Print Assumptions CurveBankBound.group_TV_bound.
Print Assumptions CurveBankBound.arbitrary_prior_bound.
Print Assumptions CurveBankBound.binomial_prior_bound.
