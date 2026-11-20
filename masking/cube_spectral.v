From mathcomp Require Import boot order algebra reals field_tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module CubeSpectral.
Section Pair.
Variable C : numClosedFieldType.

Lemma unit_circle_add (v : C) : `|v| = 1 -> `|1+v|^+2 = 2 + 2 * 'Re v.
Proof.
  move=> Hv.
  have Hvprod : v*v^* = 1 by rewrite -normCK Hv expr1n.
  rewrite normCK rmorphD rmorph1 /= ReE.
  have -> : (1+v)*(1+v^*) = (1+v+v^*) + v*v^* by ring.
  rewrite Hvprod. field.
Qed.

Lemma half_plane_norm (v : C) : `|v| = 1 -> 'Re v <= 0 -> `|1+v| <= 99/70.
Proof.
  move=> Hv Hre.
  have Hsq : `|1+v|^+2 <= 2.
    rewrite unit_circle_add // -[X in _ <= X]addr0 lerD2l.
    have := ler_wpM2l (ler0n C 2) Hre. by rewrite mulr0.
  have Hr : (2:C) <= (99/70)^+2.
    have -> : (99/70:C)^+2 = 9801/4900 by field.
    by rewrite ler_pdivlMr ?ltr0n // -natrM ler_nat.
  rewrite -ler_sqr ?nnegrE ?normr_ge0 ?divr_ge0 ?ler0n //.
  exact: le_trans Hsq Hr.
Qed.

Lemma pair_expand (u v : C) :
  (1 + u) * (1 + u*v) = (1 + u^+2*v) + u*(1+v).
Proof. ring. Qed.

Lemma pair_norm (u v : C) : `|u| = 1 -> `|v| = 1 ->
  `|(1+u)*(1+u*v)| <= 2 + `|1+v|.
Proof.
  move=> Hu Hv. rewrite pair_expand.
  apply: le_trans (ler_normD _ _) _.
  rewrite normrM Hu mul1r.
  apply: lerD => //.
  apply: le_trans (ler_normD _ _) _.
  by rewrite normr1 normrM normrX Hu Hv expr1n mul1r.
Qed.

Lemma wide_half_plane_norm (v : C) : `|v| = 1 -> 'Re v <= 3/4 -> `|1+v| <= 15/8.
Proof.
  move=> Hv Hre.
  have Hsq : `|1+v|^+2 <= 7/2.
    rewrite unit_circle_add //.
    have H := lerD (lexx (2:C)) (ler_wpM2l (ler0n C 2) Hre).
    have E : (2 + 2*(3/4):C) = 7/2 by field.
    by rewrite E in H.
  have Hr : (7/2:C) <= (15/8)^+2.
    have -> : (15/8:C)^+2 = 225/64 by field.
    rewrite ler_pdivlMr ?ltr0n //.
    have -> : (7/2:C)*64 = 224 by field.
    by rewrite ler_nat.
  rewrite -ler_sqr ?nnegrE ?normr_ge0 ?divr_ge0 ?ler0n //.
  exact: le_trans Hsq Hr.
Qed.

Theorem pair_bound (u v radius : C) : `|u| = 1 -> `|v| = 1 ->
  `|1+v| <= radius -> `|((1+u)/2)*((1+u*v)/2)| <= (2+radius)/4.
Proof.
  move=> Hu Hv Hsep.
  have -> : ((1+u)/2)*((1+u*v)/2) = ((1+u)*(1+u*v))/4 by field.
  rewrite normrM normfV normr_nat.
  have H := le_trans (pair_norm Hu Hv) (lerD (lexx (2:C)) Hsep).
  have H4 : 0 <= (4:C)^-1 by rewrite invr_ge0 ler0n.
  apply: le_trans (ler_wpM2r H4 H) _. exact: lexx.
Qed.

Theorem pair_factor_bound (u v : C) : `|u| = 1 -> `|v| = 1 ->
  `|1+v| <= 99 / 70 ->
  `|((1+u)/2)*((1+u*v)/2)| <= 239 / 280.
Proof.
  move=> Hu Hv Hvsep.
  have Heq : ((1+u)/2)*((1+u*v)/2) = ((1+u)*(1+u*v))/4 by field.
  rewrite Heq normrM normfV normr_nat.
  have H := le_trans (pair_norm Hu Hv) (lerD (lexx 2) Hvsep).
  have H4 : 0 <= (4:C)^-1 by rewrite invr_ge0 ler0n.
  apply: le_trans (ler_wpM2r H4 H) _.
  have -> : (2 + 99/70) * (4:C)^-1 = 239/280 by field.
  exact: lexx.
Qed.

Corollary half_plane_pair (u v : C) : `|u| = 1 -> `|v| = 1 -> 'Re v <= 0 ->
  `|((1+u)/2)*((1+u*v)/2)| <= 239/280.
Proof. move=> Hu Hv Hre. apply: pair_factor_bound => //. exact: half_plane_norm. Qed.

Corollary wide_half_plane_pair (u v : C) : `|u| = 1 -> `|v| = 1 -> 'Re v <= 3/4 ->
  `|((1+u)/2)*((1+u*v)/2)| <= 31/32.
Proof.
  move=> Hu Hv Hre. have H := pair_bound Hu Hv (wide_half_plane_norm Hv Hre).
  have E : ((2+15/8)/4:C) = 31/32 by field.
  by rewrite E in H.
Qed.

Lemma product_norm_bound (I : finType) (f : I -> C) (P : pred I) :
  (forall i, P i -> `|f i| <= 1) -> `|\prod_(i | P i) f i| <= 1.
Proof.
  move=> H. rewrite normr_prod.
  have Hprod : \prod_(i | P i) `|f i| <= \prod_(i : I | P i) (1:C).
    apply: ler_prod => i Hi. apply/andP; split; [exact: normr_ge0|exact: H].
  have Hone : \prod_(i : I | P i) (1:C) = 1 by apply: big1 => i Hi.
  by rewrite Hone in Hprod.
Qed.

Theorem product_pair_bound (I : finType) (f : I -> C) i j rho :
  i != j -> (forall k, `|f k| <= 1) -> `|f i * f j| <= rho ->
  `|\prod_k f k| <= rho.
Proof.
  move=> Hij Hunit Hpair.
  have Hji : j != i by rewrite eq_sym.
  rewrite (bigD1 i) //= (bigD1 j) //=.
  rewrite mulrA normrM.
  have Hrest : `|\prod_(k | (k != i) && (k != j)) f k| <= 1.
    apply: product_norm_bound => k _. exact: Hunit.
  apply: le_trans (ler_wpM2l (normr_ge0 _) Hrest) _.
  by rewrite mulr1.
Qed.

End Pair.

Section Truncation.
Variable C : numClosedFieldType.

(* Transfer a cube bound through a 19-term remainder. *)
Theorem truncation_bound (Q cube value tail : C) :
  39520 <= Q -> Q*cube = (Q-19)*value + tail ->
  `|cube| <= 31/32 -> `|tail| <= 19 -> `|value| <= 32/33.
Proof.
  move=> HQ Heq Hcube Htail.
  have HQ0 : 0 <= Q := le_trans (ler0n C 39520) HQ.
  have HP : 0 < Q-19.
    rewrite subr_gt0. apply: lt_le_trans (_ : (19:C) < 39520) HQ.
    by rewrite ltr_nat.
  have HP0 := ltW HP.
  have HPne : Q-19 != 0 by rewrite (gt_eqF HP).
  have Hnum : Q*cube-tail = (Q-19)*value by rewrite Heq addrK.
  have Hvalue : value = (Q*cube-tail)/(Q-19).
    by rewrite Hnum mulrAC mulfV // mul1r.
  rewrite Hvalue normrM normfV (ger0_norm HP0).
  have Hnumerator : `|Q*cube-tail| <= Q*(31/32)+19.
    apply: le_trans (ler_normB _ _) _.
    rewrite normrM (ger0_norm HQ0).
    exact: lerD (ler_wpM2l HQ0 Hcube) Htail.
  have Hinv : 0 <= (Q-19)^-1 by rewrite invr_ge0.
  apply: le_trans (ler_wpM2r Hinv Hnumerator) _.
  rewrite ler_pdivrMr // -subr_ge0.
  have -> : (32/33)*(Q-19) - (Q*(31/32)+19) = (Q-39520)/1056 by field.
  by apply: divr_ge0; rewrite ?subr_ge0 ?ler0n.
Qed.

End Truncation.
End CubeSpectral.

Print Assumptions CubeSpectral.pair_factor_bound.
Print Assumptions CubeSpectral.wide_half_plane_pair.
Print Assumptions CubeSpectral.product_pair_bound.
Print Assumptions CubeSpectral.truncation_bound.
