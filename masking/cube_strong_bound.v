From mathcomp Require Import boot order algebra reals field_tactic.
From Masking Require Import cube_roots cube_spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module CubeStrongBound.
Section Bound.
Variable C : numClosedFieldType.

Lemma unit_factor (u : C) : `|u| = 1 -> `|(1+u)/2| <= 1.
Proof.
move=> Hu. rewrite normrM normfV normr_nat ler_pdivrMr ?ltr0n // mul1r.
apply: le_trans (ler_normD _ _) _. by rewrite normr1 Hu.
Qed.

Lemma unit_deficit (u : C) : `|u| = 1 ->
  `|1-u| ^+ 2 = 4 * (1 - `|(1+u)/2| ^+ 2).
Proof.
move=> Hu.
have Hminus : `|1-u| ^+ 2 = 2 - 2 * 'Re u.
  by rewrite (CubeSpectral.unit_circle_add (v := -u)) ?normrN // raddfN mulrN.
rewrite Hminus normrM normfV normr_nat exprMn (CubeSpectral.unit_circle_add Hu).
field.
Qed.

Lemma product_deficit w (f : nat -> C) :
  (forall i, (i < w)%N -> 0 <= f i <= 1) ->
  (\prod_(i < w) f i) * (\sum_(i < w) (1-f i)) <= 1 - \prod_(i < w) f i.
Proof.
elim: w => [|w IH] Hf; first by rewrite !big_ord0 mulr0 subrr.
have Htail i : (i < w)%N -> 0 <= f i <= 1.
  move=> Hi. exact: Hf (ltn_trans Hi (ltnSn w)).
have /andP[Hx0 Hx1] := Hf w (ltnSn w).
have HI := IH Htail.
have HP0 : 0 <= \prod_(i < w) f i.
  apply: prodr_ge0 => i _. exact: (andP (Htail i (ltn_ord i))).1.
have HP1 : \prod_(i < w) f i <= 1.
  apply: prodr_ile1 => i _. exact: Htail (ltn_ord i).
have Hprod : (\prod_(i < w) f i) * f w <= 1 by exact: mulr_ile1 HP0 Hx0 HP1 Hx1.
have Hdef : 0 <= 1-f w by rewrite subr_ge0.
have HA := ler_wpM2l Hx0 HI.
have HB := ler_wpM2r Hdef Hprod.
have H := lerD HA HB.
rewrite !big_ord_recr /=.
have E1 : f w * ((\prod_(i < w) f i) * (\sum_(i < w) (1-f i))) +
    (\prod_(i < w) f i) * f w * (1-f w) =
    ((\prod_(i < w) f i) * f w) * ((\sum_(i < w) (1-f i)) + (1-f w)) by ring.
have E2 : f w * (1-\prod_(i < w) f i) + 1*(1-f w) =
    1-(\prod_(i < w) f i)*f w by ring.
by rewrite E1 E2 in H.
Qed.

Lemma product_below_factor (I : finType) (f : I -> C) i :
  (forall j, `|f j| <= 1) -> `|\prod_j f j| <= `|f i|.
Proof.
move=> Hf. rewrite (bigD1 i) //= normrM.
have Hrest : `|\prod_(j | j != i) f j| <= 1.
  apply: CubeSpectral.product_norm_bound => j _. exact: Hf.
by move: (ler_wpM2l (normr_ge0 (f i)) Hrest); rewrite mulr1.
Qed.

Lemma adjacent_distance (u v t : C) :
  `|u| = 1 -> `|v| = 1 -> t*v = u^+2 ->
  `|1-t| ^+ 2 <= 5 * (`|1-u| ^+ 2 + `|1-v| ^+ 2).
Proof.
move=> Hu Hv Hrel.
have Heq : (1-t)*v = v-u^+2 by rewrite mulrBl mul1r Hrel.
have Hnorm : `|1-t| = `|v-u^+2| by rewrite -Heq normrM Hv mulr1.
have Hd : `|1-t| <= 2*`|1-u| + `|1-v|.
  rewrite Hnorm.
  have E : v-u^+2 = (v-1)+(1-u)*(1+u) by ring.
  rewrite E. apply: le_trans (ler_normD _ _) _.
  rewrite normrM (distrC v 1) addrC [2*_]mulrC.
  apply: lerD => //.
  apply: ler_wpM2l; first exact: normr_ge0.
  apply: le_trans (ler_normD _ _) _. by rewrite normr1 Hu.
have Hsq : `|1-t| ^+ 2 <= (2*`|1-u| + `|1-v|)^+2.
  apply: lerXn2r; rewrite ?nnegrE ?normr_ge0 //.
  by apply: addr_ge0; [apply: mulr_ge0; rewrite ?ler0n ?normr_ge0 | exact: normr_ge0].
apply: le_trans Hsq _.
rewrite -subr_ge0.
have -> : 5 * (`|1-u| ^+ 2 + `|1-v| ^+ 2) - (2 * `|1-u| + `|1-v|)^+2 =
    (`|1-u| - 2 * `|1-v|)^+2 by ring.
apply: real_exprn_even_ge0 => //.
apply: rpredB; first exact: normr_real.
by apply: rpredM; rewrite ?realn ?normr_real.
Qed.

Definition phase (z t : C) (j : nat) :=
  t * z ^+ (2 ^ j).

Definition factor (z t : C) (j : nat) :=
  (1 + phase z t j) / 2.

Definition rotated (z t : C) :=
  \prod_(j < 255) factor z t j.

Definition distance (z t : C) (j : nat) :=
  `|1 - phase z t j| ^+ 2.

Lemma phase_unit z t : `|z| = 1 -> `|t| = 1 -> forall j, `|phase z t j| = 1.
Proof. by move=> Hz Ht j; rewrite /phase normrM normrX Hz Ht expr1n mulr1. Qed.

Lemma phase_relation z t j : t * phase z t j.+1 = (phase z t j)^+2.
Proof.
rewrite /phase expnS mulnC exprM !expr2. ring.
Qed.

Lemma total_deficit z t : `|z| = 1 -> `|t| = 1 ->
  `|rotated z t| ^+ 2 * (\sum_(j < 255) distance z t j) <= 4 * (1 - `|rotated z t| ^+ 2).
Proof.
move=> Hz Ht.
have Hu := phase_unit Hz Ht.
have Hf j : (j < 255)%N -> 0 <= `|factor z t j| ^+ 2 <= 1.
  move=> _. apply/andP; split; first exact: exprn_ge0 (normr_ge0 _).
  apply: exprn_ile1; first exact: normr_ge0.
  exact: unit_factor (Hu j).
have H := product_deficit Hf.
have EP : (\prod_(j < 255) `|factor z t j| ^+ 2) = `|rotated z t| ^+ 2.
  by rewrite prodrXl -normr_prod.
rewrite EP in H.
have ES : (\sum_(j < 255) distance z t j) = 4 * \sum_(j < 255) (1 - `|factor z t j| ^+ 2).
  under eq_bigr => j _ do rewrite /distance (unit_deficit (Hu j)).
  by rewrite -big_distrr.
rewrite ES.
have E (a b : C) : a * (4*b) = 4*(a*b) by ring.
rewrite E. apply: ler_wpM2l H. exact: ler0n.
Qed.

Lemma adjacent_total z t : `|z| = 1 -> `|t| = 1 ->
  254 * `|1-t| ^+ 2 <= 10 * \sum_(j < 255) distance z t j.
Proof.
move=> Hz Ht. have Hu := phase_unit Hz Ht.
have H0 j : 0 <= distance z t j by exact: exprn_ge0 (normr_ge0 _).
have Hpoint j : `|1-t| ^+ 2 <= 5 * (distance z t j + distance z t j.+1).
  exact: adjacent_distance (Hu j) (Hu j.+1) (phase_relation z t j).
have HS : (\sum_(j < 254) `|1-t| ^+ 2) <=
    \sum_(j < 254) 5 * (distance z t j + distance z t j.+1).
  by apply: ler_sum => j _; exact: Hpoint.
rewrite sumr_const card_ord -(mulr_natl (`|1-t| ^+ 2) 254)
  -big_distrr /= big_split /= in HS.
have Hfirst : (\sum_(j < 254) distance z t j) <= \sum_(j < 255) distance z t j.
  by rewrite [X in _ <= X]big_ord_recr /= lerDl.
have Hlast : (\sum_(j < 254) distance z t j.+1) <= \sum_(j < 255) distance z t j.
  by rewrite [X in _ <= X]big_ord_recl /= lerDr.
have Hends := lerD Hfirst Hlast.
have H := le_trans HS (ler_wpM2l (ler0n C 5) Hends).
have E (a : C) : 5*(a+a) = 10*a by ring.
by rewrite E in H.
Qed.

Lemma large_product_rotation z t : `|z| = 1 -> `|t| = 1 ->
  3/4 < `|rotated z t| -> `|1-t| < 3/8.
Proof.
move=> Hz Ht HB.
pose P := `|rotated z t| ^+ 2.
have HP0 : 0 <= P by exact: exprn_ge0 (normr_ge0 _).
have HP : 9/16 <= P.
  have E : (3/4:C)^+2 = 9/16 by field.
  rewrite -E /P ler_sqr ?nnegrE ?divr_ge0 ?ler0n ?normr_ge0 //.
  exact: ltW HB.
have HPpos : 0 < P.
  apply: lt_le_trans (_ : (0:C) < 9/16) HP. by rewrite divr_gt0 ?ltr0n.
have HS := total_deficit Hz Ht.
have HA := ler_wpM2r HP0 (adjacent_total Hz Ht).
have E (a b : C) : (10*a)*b = 10*(b*a) by ring.
rewrite E in HA.
have H := le_trans HA (ler_wpM2l (ler0n C 10) HS).
have E40 : 10*(4*(1-P)) = 40*(1-P) by ring.
change (is_true ((254 * `|1-t| ^+ 2)*P <= 10*(4*(1-P)))) in H.
rewrite E40 in H.
have Hcap : 40*(1-P) <= 254*P/8.
  rewrite -subr_ge0.
  have -> : 254*P/8 - 40*(1-P) = (287/4)*(P-9/16)+23/64 by field.
  apply: addr_ge0; last by apply: divr_ge0; exact: ler0n.
  apply: mulr_ge0; [by apply: divr_ge0; exact: ler0n | by rewrite subr_ge0].
have Hsmall := le_trans H Hcap.
have Eleft : (254 * `|1-t| ^+ 2)*P = (254*P)*`|1-t| ^+ 2 by ring.
have H254 : 0 < 254*P by apply: mulr_gt0; [exact: ltr0n | exact: HPpos].
rewrite Eleft (ler_pM2l H254) in Hsmall.
have Hrat : (1/8:C) < (3/8)^+2.
  rewrite -subr_gt0. have -> : (3/8:C)^+2-1/8 = 1/64 by field.
  by rewrite divr_gt0 ?ltr0n.
rewrite mul1r in Hrat.
have Hstrict := le_lt_trans Hsmall Hrat.
by move: Hstrict; rewrite ltr_sqr ?nnegrE ?normr_ge0 ?divr_ge0 ?ler0n.
Qed.

Lemma linear_growth (h : C) n : 0 <= h -> 1 + n%:R*h <= (1+h)^+n.
Proof.
move=> Hh. elim: n => [|n IH]; first by rewrite expr0 mul0r addr0.
rewrite exprS -[n.+1]addn1 natrD.
apply: le_trans (_ : 1 + (n%:R+1)*h <= (1+h)*(1+n%:R*h)) _.
  rewrite -subr_ge0.
  have -> : (1+h)*(1+n%:R*h) - (1+(n%:R+1)*h) = n%:R*h^+2 by ring.
  by apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0].
apply: ler_wpM2l IH. by apply: addr_ge0; [exact: ler01 | exact: Hh].
Qed.

Lemma threshold_growth : (19:C) < (17/16)^+255.
Proof.
have Hh : (0:C) <= 1/16 by apply: divr_ge0; [exact: ler01 | exact: ler0n].
have H16 := linear_growth 16 Hh.
have Ebase : (1+1/16:C) = 17/16 by field.
have Elinear : (1+16*(1/16):C) = 2 by field.
rewrite Ebase Elinear in H16.
have H80 : (2:C)^+5 <= (17/16)^+80.
  change (is_true ((2:C)^+5 <= (17/16)^+(16*5))).
  rewrite exprM. apply: lerXn2r; rewrite ?nnegrE ?ler0n //.
  apply: exprn_ge0. by apply: divr_ge0; exact: ler0n.
have Hbase : (1:C) <= 17/16 by rewrite ler_pdivlMr ?ltr0n // mul1r ler_nat.
have Hmono : (17/16:C)^+80 <= (17/16)^+255.
  apply: ler_weXn2l; [exact: Hbase | by []].
have H32 : (19:C) < 2^+5 by rewrite -natrX ltr_nat.
exact: lt_le_trans H32 (le_trans H80 Hmono).
Qed.

Lemma cube_size : (19 <= 2 ^ 255)%N.
Proof.
apply: leq_trans (_ : 19 <= 2^5)%N _; first by [].
by rewrite leq_exp2l.
Qed.

Lemma small_unrotated_factor z : `|z| = 1 -> z != 1 -> z ^+ (2^255-19) = 1 ->
  exists j : 'I_255, `|factor z 1 j| <= 17/32.
Proof.
move=> Hz Hnz Hp.
have Havg : `|rotated z 1| <= 19/(2^255)%:R.
  rewrite /rotated /factor /phase.
  under eq_bigr do rewrite mul1r.
  rewrite -CubeRoots.binary_average.
  exact: CubeRoots.cube_average_norm cube_size Hz Hnz Hp.
have Hthreshold : (19:C)/(2^255)%:R < (17/32)^+255.
  rewrite natrX ltr_pdivrMr ?exprn_gt0 ?ltr0n // -exprMn.
  have -> : (17/32:C)*2 = 17/16 by field.
  exact: threshold_growth.
case E: [exists j : 'I_255, `|factor z 1 j| <= 17/32].
  by apply/existsP; rewrite E.
have /existsPn Hnone : ~~ [exists j : 'I_255, `|factor z 1 j| <= 17/32] by rewrite E.
have Hlower : (17/32:C)^+255 <= `|rotated z 1|.
  rewrite /rotated normr_prod -{1}(card_ord 255) -prodr_const.
  apply: ler_prod => j _. apply/andP; split; first by apply: divr_ge0; exact: ler0n.
  apply: ltW. rewrite real_ltNge ?normr_real ?rpred_div ?realn //.
have Hbad := lt_le_trans Hthreshold (le_trans Hlower Havg).
by move: Hbad; rewrite ltxx.
Qed.

Lemma factor_rotation z t j : `|z| = 1 ->
  `|factor z t j| <= `|factor z 1 j| + `|1-t|/2.
Proof.
move=> Hz.
have E : factor z t j = factor z 1 j + (t-1)*z^+(2^j)/2.
  rewrite /factor /phase mul1r. field.
rewrite E. apply: le_trans (ler_normD _ _) _.
by rewrite !normrM normfV normr_nat normrX Hz expr1n mulr1 (distrC t 1).
Qed.

(* Uniform over the rotation t; the root condition is the only Curve25519-specific premise. *)
Theorem rotated_cube_bound (z t : C) :
  `|z| = 1 -> z != 1 -> z ^+ (2^255-19) = 1 -> `|t| = 1 ->
  `|\prod_(j < 255) ((1 + t*z^+(2^j))/2)| <= 3/4.
Proof.
move=> Hz Hnz Hp Ht.
change (is_true (`|rotated z t| <= 3/4)).
have Hreal : (3/4:C) \is Num.real by apply: rpred_div; exact: realn.
case: (real_leP (normr_real (rotated z t)) Hreal) => HB //.
have Hclose := large_product_rotation Hz Ht HB.
have [j Hj] := small_unrotated_factor Hz Hnz Hp.
have Hsingle : `|rotated z t| <= `|factor z t j|.
  apply: product_below_factor => i. apply: unit_factor. exact: phase_unit Hz Ht (val i).
have Hperturb := factor_rotation t j Hz.
have Hupper := le_trans Hsingle (le_trans Hperturb (lerD Hj (lexx (`|1-t|/2)))).
have Hnoise : `|1-t|/2 < 3/16.
  rewrite ltr_pdivrMr ?ltr0n //.
  have -> : (3/16:C)*2 = 3/8 by field. exact: Hclose.
have Hstrict : (17/32:C)+`|1-t|/2 < 3/4.
  have H : (17/32:C)+`|1-t|/2 < 17/32+3/16 by rewrite ltrD2l.
  have E : (17/32+3/16:C) = 23/32 by field.
  rewrite E in H. apply: lt_trans H _.
  rewrite -subr_gt0. have -> : (3/4-23/32:C) = 1/32 by field.
  by rewrite divr_gt0 ?ltr0n.
have Hbad := lt_trans HB (le_lt_trans Hupper Hstrict).
by move: Hbad; rewrite ltxx.
Qed.

End Bound.
End CubeStrongBound.

Print Assumptions CubeStrongBound.product_deficit.
Print Assumptions CubeStrongBound.adjacent_distance.
Print Assumptions CubeStrongBound.large_product_rotation.
Print Assumptions CubeStrongBound.rotated_cube_bound.
