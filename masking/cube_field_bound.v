From Stdlib Require Import ZArith.
From mathcomp Require Import boot order algebra reals field_tactic.
From Masking Require Import cube_spectral cube_bound cube_encoding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module CubeFieldBound.
Section Bound.
Variable C : numClosedFieldType.

Definition term w (z t : C) x :=
  z ^+ x * t ^+ (CubeEncoding.canonical_HW w (Z.of_nat x)).

Definition coefficient w p (z t : C) :=
  (\sum_(x < p) term w z t x) / p%:R.

Lemma normalized_cube w (z t : C) :
  coefficient w (2 ^ w) z t = \prod_(j < w) ((1 + t*z ^+ (2 ^ j))/2).
Proof.
  rewrite /coefficient /term CubeEncoding.weighted_canonical_product big_split /=.
  by rewrite prodr_const card_ord natrX exprVn.
Qed.

Lemma term_unit w (z t : C) x : `|z| = 1 -> `|t| = 1 -> `|term w z t x| = 1.
Proof. by move=> Hz Ht; rewrite /term normrM !normrX Hz Ht !expr1n mul1r. Qed.

(* The 19 excluded encodings contribute at most 19 to the unnormalized sum. *)
Theorem canonical_coefficient_bound w (z t : C) :
  (39520 <= 2 ^ w)%N -> `|z| = 1 -> z != 1 ->
  z ^+ (2 ^ w - 19) = 1 -> `|t| = 1 ->
  `|coefficient w (2 ^ w - 19) z t| <= 32/33.
Proof.
  move=> HQ Hz Hnz Hp Ht.
  have HQpos : (0 < 2 ^ w)%N by rewrite expn_gt0.
  have H19 : (19 <= 2 ^ w)%N by apply: leq_trans HQ.
  have HPpos : (0 < 2 ^ w - 19)%N by rewrite subn_gt0; exact: leq_trans HQ.
  have HQne : ((2 ^ w)%:R : C) != 0 by rewrite pnatr_eq0 (gtn_eqF HQpos).
  have HPne : ((2 ^ w - 19)%:R : C) != 0 by rewrite pnatr_eq0 (gtn_eqF HPpos).
  pose tail := \sum_(i < 19) term w z t (2 ^ w - 19 + i)%N.
  have Htail : `|tail| <= 19.
    apply: le_trans (ler_norm_sum _ _ _) _.
    under eq_bigr do rewrite term_unit //.
    by rewrite sumr_const card_ord.
  have Hsum : \sum_(x < 2 ^ w) term w z t x =
      (\sum_(x < 2 ^ w - 19) term w z t x) + tail.
    have E : \sum_(x < (2 ^ w - 19) + 19) term w z t x =
        (\sum_(x < 2 ^ w - 19) term w z t x) + tail.
      by rewrite big_split_ord.
    by rewrite subnK in E.
  have Hdecomp : (2 ^ w)%:R * coefficient w (2 ^ w) z t =
      ((2 ^ w)%:R - 19) * coefficient w (2 ^ w - 19) z t + tail.
    rewrite -natrB // /coefficient.
    by rewrite mulrC divfK // [X in _ = X + _]mulrC divfK.
  apply: (CubeSpectral.truncation_bound _ Hdecomp _ Htail).
  - by rewrite ler_nat.
  - rewrite normalized_cube. apply: CubeBound.rotated_cube_bound => //.
    exact: leq_trans HQ.
Qed.

End Bound.
End CubeFieldBound.

Print Assumptions CubeFieldBound.canonical_coefficient_bound.
