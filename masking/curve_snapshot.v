From Stdlib Require Import ZArith.
From Crypto Require Import Spec.ModularArithmetic.
From mathcomp Require Import boot order algebra reals algC cyclotomic.
From infotheo Require Import fdist.
From Masking Require Import fiat_field field_characters field_aggregate_spectral
  field_coefficient curve_coefficient cyclic_characters arithmetic_spectral noisy_leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module CurveSnapshot.
Section Bound.
Variable q : positive.
Variable q_gt1 : Z.lt 1 (Z.pos q).
Hypothesis modulus : Z.to_nat (Z.pos q) = (2^255-19)%N.
Variable n : nat.
Hypothesis shares : (1 <= n)%N.
Variable R : realType.
Local Notation K := (FiatField.ring q_gt1).
Local Notation p := (Z.to_nat (Z.pos q)).
Local Notation M := (255*n.+1).+1%N.
Local Notation W := [the finType of 'I_M].
Local Notation mass := (@FieldAggregateSpectral.mass q q_gt1 255 n).
Local Notation law := (@FieldAggregateSpectral.law q q_gt1 255 n R).

(* n counts extra shares; the actual sharing has n+1 coordinates. *)
Definition spectral_budget : rat :=
  2 * (49/64)^+(n.+1-2).

Definition squared_budget : rat :=
  M%:R * spectral_budget^+2 / 4.

Theorem actual_TV_squared (s1 s2 : K) :
  NoisyLeakage.TV (law s1) (law s2)^+2 <= @ratr R squared_budget.
Proof.
  have [z Hz] := C_prim_root_exists (@FieldCharacters.modulus_positive q q_gt1).
  have [eta Heta] := C_prim_root_exists (ltn0Sn (255*n.+1)%N).
  pose kernel := @CyclicCharacters.kernel [the numClosedFieldType of algC] M eta.
  have Hg (b : 'I_M) (s : K) :
    (\sum_h @ratr [the numFieldType of algC] (mass s h) * kernel b h) =
      FieldCoefficient.spectrum 255 z (eta^+val b) (FiatField.to_ordinal s) n.+1.
    rewrite /kernel /CyclicCharacters.kernel.
    under eq_bigr do rewrite exprM.
    exact: (@FieldAggregateSpectral.mass_generating q q_gt1 255 n
      [the numClosedFieldType of algC] z Hz (eta^+val b) s).
  have Htransform b :
    `|ArithmeticSpectral.transform kernel
      (fun h => @ratr [the numFieldType of algC] (mass s1 h) -
        @ratr [the numFieldType of algC] (mass s2 h)) b| <=
      @ratr [the numFieldType of algC] spectral_budget.
    rewrite /ArithmeticSpectral.transform.
    under eq_bigr do rewrite mulrBl.
    rewrite sumrB !Hg /spectral_budget rmorphM rmorphXn fmorph_div !rmorph_nat.
    apply: (@CurveCoefficient.spectrum_gap [the numClosedFieldType of algC] p z Hz modulus
      (eta^+val b) (FiatField.to_ordinal s1) (FiatField.to_ordinal s2) n.+1).
    - by rewrite normrX (CyclicCharacters.root_unit Heta) expr1n.
    - exact: shares.
  have H : NoisyLeakage.TV (law s1) (law s2)^+2 <=
      @ratr R (#|W|%:R * spectral_budget^+2 / 4).
    apply: (@ArithmeticSpectral.actual_TV_from_spectral W (mass s1) (mass s2)
      R (law s1) (law s2) _ _ [the numClosedFieldType of algC] W kernel spectral_budget).
    - exact: FieldAggregateSpectral.actual_mass.
    - exact: FieldAggregateSpectral.actual_mass.
    - by rewrite card_ord.
    - move=> i j. rewrite /kernel card_ord.
      exact: (@CyclicCharacters.kernel_orthogonal [the numClosedFieldType of algC] M eta Heta i j).
    - apply: mulr_ge0; first exact: ler0n.
      apply: exprn_ge0. by apply: divr_ge0; rewrite ler0n.
    - exact: Htransform.
  by rewrite card_ord in H.
Qed.

Theorem actual_TV_bound (epsilon : R) (s1 s2 : K) :
  0 <= epsilon -> @ratr R squared_budget <= epsilon^+2 ->
  NoisyLeakage.bounded_indistinguishable epsilon (law s1) (law s2).
Proof.
  move=> He Hb. rewrite /NoisyLeakage.bounded_indistinguishable.
  rewrite -ler_sqr ?nnegrE ?NoisyLeakage.TV_nonnegative //.
  exact: le_trans (actual_TV_squared s1 s2) Hb.
Qed.

Theorem noisy_TV_squared (O : finType) (channel : 'I_M -> R.-fdist O) (s1 s2 : K) :
  NoisyLeakage.TV (law s1 >>= channel) (law s2 >>= channel)^+2 <= @ratr R squared_budget.
Proof.
  have H := NoisyLeakage.channel_TV_contraction (law s1) (law s2) channel.
  apply: le_trans _ (actual_TV_squared s1 s2).
  apply: lerXn2r H; exact: NoisyLeakage.TV_nonnegative.
Qed.

Theorem noisy_TV_bound (O : finType) (channel : 'I_M -> R.-fdist O)
    (epsilon : R) (s1 s2 : K) :
  0 <= epsilon -> @ratr R squared_budget <= epsilon^+2 ->
  NoisyLeakage.bounded_indistinguishable epsilon (law s1 >>= channel) (law s2 >>= channel).
Proof.
  move=> He Hb. rewrite /NoisyLeakage.bounded_indistinguishable.
  rewrite -ler_sqr ?nnegrE ?NoisyLeakage.TV_nonnegative //.
  exact: le_trans (noisy_TV_squared channel s1 s2) Hb.
Qed.

End Bound.
End CurveSnapshot.

Print Assumptions CurveSnapshot.actual_TV_squared.
Print Assumptions CurveSnapshot.noisy_TV_squared.
