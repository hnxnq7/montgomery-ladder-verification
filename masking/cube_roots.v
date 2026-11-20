From mathcomp Require Import boot order algebra reals field_tactic.
From Masking Require Import cube_spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module CubeRoots.
Section Roots.
Variable C : numClosedFieldType.

Lemma geometric_split (z : C) m n :
  \sum_(i < m + n) z ^+ i =
    (\sum_(i < m) z ^+ i) + z ^+ m * (\sum_(i < n) z ^+ i).
Proof.
  rewrite big_split_ord /= mulr_sumr.
  congr (_ + _); apply: eq_bigr => i _.
  by rewrite /= exprD.
Qed.

Lemma binary_product (z : C) w :
  \sum_(i < 2 ^ w) z ^+ i = \prod_(j < w) (1 + z ^+ (2 ^ j)).
Proof.
  elim: w => [|w IH].
    by rewrite expn0 big_ord_recl big_ord0 /= expr0 addr0 big_ord0.
  rewrite expnS mul2n -addnn geometric_split IH big_ord_recr /=.
  by rewrite mulrDr mulr1 mulrC.
Qed.

Lemma binary_average (z : C) w :
  (\sum_(i < 2 ^ w) z ^+ i) / (2 ^ w)%:R =
    \prod_(j < w) ((1 + z ^+ (2 ^ j)) / 2).
Proof.
  rewrite binary_product big_split /= prodr_const card_ord.
  by rewrite natrX exprVn.
Qed.

Lemma root_sum_zero (z : C) p : z != 1 -> z ^+ p = 1 ->
  \sum_(i < p) z ^+ i = 0.
Proof.
  move=> Hz Hp.
  have H := subrX1 z p.
  rewrite Hp subrr in H.
  move/eqP: H; rewrite eq_sym mulf_eq0 subr_eq0 (negbTE Hz) /=.
  exact/eqP.
Qed.

Lemma root_tail (z : C) p d : z != 1 -> z ^+ p = 1 ->
  \sum_(i < p + d) z ^+ i = \sum_(i < d) z ^+ i.
Proof. by move=> Hz Hp; rewrite geometric_split (root_sum_zero Hz Hp) Hp add0r mul1r. Qed.

Lemma root_tail_norm (z : C) p d :
  `|z| = 1 -> z != 1 -> z ^+ p = 1 ->
  `|\sum_(i < p + d) z ^+ i| <= d%:R.
Proof.
  move=> Hu Hz Hp; rewrite (root_tail d Hz Hp).
  apply: le_trans (ler_norm_sum _ _ _) _.
  under eq_bigr do rewrite normrX Hu expr1n.
  by rewrite sumr_const card_ord.
Qed.

Lemma cube_tail_norm (z : C) w :
  (19 <= 2 ^ w)%N -> `|z| = 1 -> z != 1 -> z ^+ (2 ^ w - 19) = 1 ->
  `|\sum_(i < 2 ^ w) z ^+ i| <= 19.
Proof.
  move=> Hw Hu Hz Hp.
  have H := root_tail_norm 19 Hu Hz Hp.
  by rewrite subnK in H.
Qed.

Lemma cube_average_norm (z : C) w :
  (19 <= 2 ^ w)%N -> `|z| = 1 -> z != 1 -> z ^+ (2 ^ w - 19) = 1 ->
  `|(\sum_(i < 2 ^ w) z ^+ i) / (2 ^ w)%:R| <= 19 / (2 ^ w)%:R.
Proof.
  move=> Hw Hu Hz Hp; rewrite normrM normfV normr_nat.
  apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  exact: cube_tail_norm Hw Hu Hz Hp.
Qed.

Theorem cube_half_plane (z : C) w :
  (361 < 2 ^ w)%N -> `|z| = 1 -> z != 1 -> z ^+ (2 ^ w - 19) = 1 ->
  exists j : 'I_w, 'Re (z ^+ (2 ^ j)) <= 0.
Proof.
  move=> Hw Hu Hz Hp.
  have H19 : (19 <= 2 ^ w)%N by apply: leq_trans _ (ltnW Hw).
  case E: [exists j : 'I_w, 'Re (z ^+ (2 ^ j)) <= 0].
    by apply/existsP; rewrite E.
  have /existsPn Hnone : ~~ [exists j : 'I_w, 'Re (z ^+ (2 ^ j)) <= 0] by rewrite E.
  have Hpos (j : 'I_w) : 0 < 'Re (z ^+ (2 ^ j)).
    by rewrite real_ltNge ?Creal_Re ?real0 //; exact: Hnone.
  have Hlower : (2 ^ w)%:R <= `|\sum_(i < 2 ^ w) z ^+ i|^+2.
    rewrite binary_product normr_prod -prodrXl natrX.
    rewrite -[w in (2:C)^+w]card_ord -prodr_const.
    apply: ler_prod => j _; rewrite ler0n /=.
    rewrite CubeSpectral.unit_circle_add ?normrX ?Hu ?expr1n //.
    rewrite lerDl mulr_ge0 ?ler0n //.
    exact: ltW (Hpos j).
  have Hupper : `|\sum_(i < 2 ^ w) z ^+ i|^+2 <= (19:C)^+2.
    rewrite ler_sqr ?nnegrE ?normr_ge0 ?ler0n //.
    exact: cube_tail_norm H19 Hu Hz Hp.
  have H := le_trans Hlower Hupper.
  have H361 : (19:C)^+2 = 361 by rewrite -natrX.
  move: H; rewrite H361 ler_nat => H.
  by move: Hw; rewrite ltnNge H.
Qed.

Lemma unit_square_Re (v : C) : `|v| = 1 ->
  'Re (v ^+ 2) = 2 * ('Re v)^+2 - 1.
Proof.
  move=> Hv.
  have H : 1 = ('Re v)^+2 + ('Im v)^+2.
    by rewrite -normC2_Re_Im Hv expr1n.
  rewrite expr2 ReM -!expr2 {2}H. ring.
Qed.

Lemma square_half_plane_predecessor (v : C) :
  `|v| = 1 -> 'Re (v ^+ 2) <= 0 -> 'Re v <= 3/4.
Proof.
  move=> Hv Hre.
  have Hsq : ('Re v)^+2 <= 1/2.
    rewrite ler_pdivlMr ?ltr0n // mulrC.
    by move: Hre; rewrite unit_square_Re // subr_le0.
  have Hrat : (1/2:C) <= (3/4)^+2.
    have -> : (3/4:C)^+2 = 9/16 by field.
    rewrite ler_pdivlMr ?ltr0n //.
    have -> : (1/2:C)*16 = 8 by field.
    by rewrite ler_nat.
  case: (real_leP (Creal_Re v) real0) => Hr.
    exact: le_trans Hr (divr_ge0 (ler0n C 3) (ler0n C 4)).
  have Hr0 : 0 <= 'Re v := ltW Hr.
  rewrite -ler_sqr ?nnegrE ?divr_ge0 ?ler0n ?Hr0 //.
  exact: le_trans Hsq Hrat.
Qed.

Lemma half_plane_eligible (z : C) w :
  (1 < w)%N -> `|z| = 1 ->
  (exists j : 'I_w, 'Re (z ^+ (2 ^ j)) <= 0) ->
  exists j : nat, (j.+1 < w)%N /\ 'Re (z ^+ (2 ^ j)) <= 3/4.
Proof.
  move=> Hw Hu [j Hj].
  case Hnext: (j.+1 < w)%N.
    exists (val j); split => //.
    exact: le_trans Hj (divr_ge0 (ler0n C 3) (ler0n C 4)).
  case Ej: (val j) => [|k].
    by move: Hnext; rewrite Ej Hw.
  exists k; split.
    by have := ltn_ord j; rewrite Ej.
  apply: square_half_plane_predecessor.
    by rewrite normrX Hu expr1n.
  by rewrite -exprM -expnSr; move: Hj; rewrite Ej.
Qed.

Corollary cube_eligible (z : C) w :
  (361 < 2 ^ w)%N -> `|z| = 1 -> z != 1 -> z ^+ (2 ^ w - 19) = 1 ->
  exists j : nat, (j.+1 < w)%N /\ 'Re (z ^+ (2 ^ j)) <= 3/4.
Proof.
  move=> Hw Hu Hz Hp.
  have Hw2 : (1 < w)%N by case: w Hw Hp => [|[|w]] //.
  exact: half_plane_eligible Hw2 Hu (cube_half_plane Hw Hu Hz Hp).
Qed.

End Roots.
End CubeRoots.

Print Assumptions CubeRoots.binary_average.
Print Assumptions CubeRoots.cube_average_norm.
Print Assumptions CubeRoots.cube_half_plane.
Print Assumptions CubeRoots.cube_eligible.
