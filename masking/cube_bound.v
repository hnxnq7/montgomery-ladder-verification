From mathcomp Require Import boot order algebra reals field_tactic.
From Masking Require Import cube_spectral cube_roots.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module CubeBound.
Section Bound.
Variable C : numClosedFieldType.

Lemma unit_factor (u : C) : `|u| = 1 -> `|(1+u)/2| <= 1.
Proof.
  move=> Hu. rewrite normrM normfV normr_nat.
  have H : `|1+u| <= 2 by apply: le_trans (ler_normD _ _) _; rewrite normr1 Hu.
  have Hinv : 0 <= (2:C)^-1 by rewrite invr_ge0 ler0n.
  apply: le_trans (ler_wpM2r Hinv H) _.
  by rewrite divff ?pnatr_eq0.
Qed.

(* The bound is uniform in the weight-frequency phase t. *)
Theorem rotated_cube_bound (z t : C) w :
  (361 < 2 ^ w)%N -> `|z| = 1 -> z != 1 ->
  z ^+ (2 ^ w - 19) = 1 -> `|t| = 1 ->
  `|\prod_(j < w) ((1 + t * z ^+ (2 ^ j)) / 2)| <= 31/32.
Proof.
  move=> Hw Hz Hnz Hp Ht.
  have [j [Hj Hre]] := CubeRoots.cube_eligible Hw Hz Hnz Hp.
  have Hj0 : (j < w)%N := ltn_trans (ltnSn j) Hj.
  pose i : 'I_w := Ordinal Hj0.
  pose k : 'I_w := Ordinal Hj.
  have Hik : i != k by rewrite /i /k -val_eqE /= (ltn_eqF (ltnSn j)).
  apply: (CubeSpectral.product_pair_bound Hik).
  - move=> a. apply: unit_factor. by rewrite normrM normrX Ht Hz expr1n mul1r.
  - have Hu : `|t * z ^+ (2 ^ j)| = 1 by rewrite normrM normrX Ht Hz expr1n mul1r.
    have Hv : `|z ^+ (2 ^ j)| = 1 by rewrite normrX Hz expr1n.
    have H := CubeSpectral.wide_half_plane_pair Hu Hv Hre.
    have E : t * z ^+ (2 ^ j) * z ^+ (2 ^ j) = t * z ^+ (2 ^ j.+1).
      by rewrite -mulrA -exprD addnn -mul2n -expnS.
    by rewrite E in H.
Qed.

End Bound.
End CubeBound.

Print Assumptions CubeBound.rotated_cube_bound.
