From mathcomp Require Import boot order algebra reals field_tactic.
From infotheo Require Import fdist variation_dist.
From Masking Require Import noisy_leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module NoisyCommonMass.
Section Common.
Variable R : realType.
Variable A : finType.
Variables d e : R.-fdist A.
Variable common : A -> R.

Definition common_mass : R :=
  \sum_(a : A) common a.

Lemma common_mass_nonnegative :
  (forall a, 0 <= common a) -> 0 <= common_mass.
Proof. move=> H; exact: sumr_ge0. Qed.

Lemma common_mass_at_most_one :
  (forall a, common a <= d a) -> common_mass <= 1.
Proof.
move=> H. rewrite /common_mass -(FDist.f1 d).
by apply: ler_sum => a _; exact: H.
Qed.

Lemma pointwise_residual_bound a :
  common a <= d a -> common a <= e a ->
  `|d a - e a| <= (d a - common a) + (e a - common a).
Proof.
move=> Hd He.
have -> : d a - e a = (d a - common a) - (e a - common a) by field.
apply: le_trans (ler_normB _ _) _.
have Hdp : 0 <= d a - common a by rewrite subr_ge0.
have Hep : 0 <= e a - common a by rewrite subr_ge0.
by rewrite (ger0_norm Hdp) (ger0_norm Hep).
Qed.

Lemma common_L1_bound :
  (forall a, common a <= d a) -> (forall a, common a <= e a) ->
  var_dist d e <= (1 - common_mass) * 2.
Proof.
move=> Hd He.
have H : var_dist d e <= \sum_(a : A) ((d a - common a) + (e a - common a)).
  apply: ler_sum => a _. exact: pointwise_residual_bound (Hd a) (He a).
rewrite big_split /= !sumrB !FDist.f1 -/common_mass in H.
have E : (1 - common_mass) + (1 - common_mass) = (1 - common_mass) * 2 by field.
by rewrite E in H.
Qed.

(* Nonnegativity makes this a common subdistribution; the distance inequality only needs domination. *)
Theorem TV_common_bound :
  (forall a, common a <= d a) -> (forall a, common a <= e a) ->
  TV d e <= 1 - common_mass.
Proof.
move=> Hd He. rewrite /TV ler_pdivrMr ?ltr0n //.
exact: common_L1_bound Hd He.
Qed.

Theorem common_component_bound :
  (forall a, 0 <= common a) ->
  (forall a, common a <= d a) -> (forall a, common a <= e a) ->
  0 <= common_mass /\ common_mass <= 1 /\ TV d e <= 1 - common_mass.
Proof.
move=> H0 Hd He. split; first exact: common_mass_nonnegative.
split; [exact: common_mass_at_most_one | exact: TV_common_bound].
Qed.

End Common.

Section ChannelFamily.
Variable R : realType.
Variables I A : finType.
Variable channel : I -> R.-fdist A.
Variable common : A -> R.

(* A channel instance must prove its own common pointwise lower bound. *)
Theorem channel_common_bound :
  (forall i a, common a <= channel i a) ->
  forall i j, TV (channel i) (channel j) <= 1 - \sum_(a : A) common a.
Proof.
move=> H i j. exact: TV_common_bound (H i) (H j).
Qed.

End ChannelFamily.
End NoisyCommonMass.

Print Assumptions NoisyCommonMass.TV_common_bound.
Print Assumptions NoisyCommonMass.common_component_bound.
Print Assumptions NoisyCommonMass.channel_common_bound.
