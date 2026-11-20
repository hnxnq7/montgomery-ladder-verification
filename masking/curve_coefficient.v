From Stdlib Require Import ZArith.
From mathcomp Require Import boot order algebra reals field_tactic.
From Masking Require Import cube_strong_bound cube_field_bound field_coefficient
  arithmetic_spectral cyclic_characters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module CurveCoefficient.
Section Truncation.
Variable C : numClosedFieldType.

Lemma truncation_bound (Q cube value tail : C) :
  2147 <= Q -> Q*cube = (Q-19)*value + tail ->
  `|cube| <= 3/4 -> `|tail| <= 19 -> `|value| <= 49/64.
Proof.
move=> HQ Heq Hcube Htail.
have HQ0 : 0 <= Q := le_trans (ler0n C 2147) HQ.
have HP : 0 < Q-19.
  rewrite subr_gt0. apply: lt_le_trans (_ : (19:C) < 2147) HQ.
  by rewrite ltr_nat.
have HPne : Q-19 != 0 by rewrite (gt_eqF HP).
have Hvalue : value = (Q*cube-tail)/(Q-19).
  by rewrite Heq addrK mulrAC mulfV // mul1r.
rewrite Hvalue normrM normfV (ger0_norm (ltW HP)).
have Hnum : `|Q*cube-tail| <= Q*(3/4)+19.
  apply: le_trans (ler_normB _ _) _.
  rewrite normrM (ger0_norm HQ0).
  exact: lerD (ler_wpM2l HQ0 Hcube) Htail.
have Hinv : 0 <= (Q-19)^-1 by rewrite invr_ge0; exact: ltW HP.
apply: le_trans (ler_wpM2r Hinv Hnum) _.
rewrite ler_pdivrMr // -subr_ge0.
have -> : (49/64)*(Q-19) - (Q*(3/4)+19) = (Q-2147)/64 by field.
by apply: divr_ge0; rewrite ?subr_ge0 ?ler0n.
Qed.

Lemma cube_size : (2147 <= 2^255)%N.
Proof.
apply: leq_trans (_ : 2147 <= 2^12)%N _; first by [].
by rewrite leq_exp2l.
Qed.

(* Keep the sum split symbolic; the HW and 19-term remainder are unchanged. *)
Lemma canonical_transfer w (z t : C) :
  (2147 <= 2^w)%N -> `|z| = 1 -> `|t| = 1 ->
  `|CubeFieldBound.coefficient w (2^w) z t| <= 3/4 ->
  `|CubeFieldBound.coefficient w (2^w-19) z t| <= 49/64.
Proof.
move=> HQ Hz Ht Hcube.
have HQpos : (0 < 2^w)%N by rewrite expn_gt0.
have H19 : (19 <= 2^w)%N by apply: leq_trans HQ.
have HPpos : (0 < 2^w-19)%N by rewrite subn_gt0; exact: leq_trans HQ.
have HQne : ((2^w)%:R : C) != 0 by rewrite pnatr_eq0 (gtn_eqF HQpos).
have HPne : ((2^w-19)%:R : C) != 0 by rewrite pnatr_eq0 (gtn_eqF HPpos).
pose tail := \sum_(i < 19) CubeFieldBound.term w z t (2^w-19+i)%N.
have Htail : `|tail| <= 19.
  apply: le_trans (ler_norm_sum _ _ _) _.
  under eq_bigr do rewrite CubeFieldBound.term_unit //.
  by rewrite sumr_const card_ord.
have Hsum : \sum_(x < 2^w) CubeFieldBound.term w z t x =
    (\sum_(x < 2^w-19) CubeFieldBound.term w z t x) + tail.
  have E : \sum_(x < (2^w-19)+19) CubeFieldBound.term w z t x =
      (\sum_(x < 2^w-19) CubeFieldBound.term w z t x) + tail.
    by rewrite big_split_ord.
  by rewrite subnK in E.
have Hdecomp : (2^w)%:R * CubeFieldBound.coefficient w (2^w) z t =
    ((2^w)%:R-19) * CubeFieldBound.coefficient w (2^w-19) z t + tail.
  rewrite -natrB // /CubeFieldBound.coefficient.
  by rewrite mulrC divfK // [X in _ = X+_]mulrC divfK.
apply: (truncation_bound _ Hdecomp Hcube Htail).
by rewrite ler_nat.
Qed.

Theorem canonical_coefficient_bound (z t : C) :
  `|z| = 1 -> z != 1 -> z^+(2^255-19) = 1 -> `|t| = 1 ->
  `|CubeFieldBound.coefficient 255 (2^255-19) z t| <= 49/64.
Proof.
move=> Hz Hnz Hp Ht.
apply: (canonical_transfer cube_size Hz Ht).
rewrite CubeFieldBound.normalized_cube.
exact: CubeStrongBound.rotated_cube_bound Hz Hnz Hp Ht.
Qed.

End Truncation.

Section Coefficients.
Variable C : numClosedFieldType.
Variable p : nat.
Variable z : C.
Hypothesis primitive : p.-primitive_root z.
Hypothesis modulus : p = (2^255-19)%N.

Theorem coefficient_nontrivial t (a : 'I_p) : `|t| = 1 -> val a != 0%N ->
  `|FieldCoefficient.coefficient 255 z t a| <= 49/64.
Proof.
move=> Ht Ha. rewrite FieldCoefficient.coefficientE.
have Hz : `|z^+val a| = 1.
  by rewrite normrX (CyclicCharacters.root_unit primitive) expr1n.
have Hnz : z^+val a != 1.
  rewrite -[X in _ != X](expr0 z) (eq_prim_root_expr primitive).
  by rewrite modn_small ?ltn_ord // mod0n.
have Hp : (z^+val a)^+(2^255-19) = 1.
  by rewrite -modulus -exprM mulnC exprM (prim_expr_order primitive) expr1n.
have H := canonical_coefficient_bound Hz Hnz Hp Ht.
by rewrite -modulus in H.
Qed.

Theorem coefficient_energy t : `|t| = 1 ->
  \sum_(a : 'I_p) `|FieldCoefficient.coefficient 255 z t a| ^+ 2 = 1.
Proof.
exact: (@FieldCoefficient.coefficient_energy C 255 p z primitive t).
Qed.

Theorem spectrum_gap t (s1 s2 : 'I_p) count : `|t| = 1 -> (2 <= count)%N ->
  `|FieldCoefficient.spectrum 255 z t s1 count - FieldCoefficient.spectrum 255 z t s2 count| <=
    2 * (49/64)^+(count-2).
Proof.
move=> Ht Hcount.
pose zero : 'I_p := Ordinal (prim_order_gt0 primitive).
rewrite /FieldCoefficient.spectrum.
apply: (@ArithmeticSpectral.coefficient_gap_n C [the finType of 'I_p] zero
  (FieldCoefficient.coefficient 255 z t) (fun a => (CyclicCharacters.kernel z a s1)^*)
  (fun a => (CyclicCharacters.kernel z a s2)^*) (49/64)) => //.
- by apply: divr_ge0; rewrite ler0n.
- move=> a. by rewrite norm_conjC (CyclicCharacters.kernel_unit primitive).
- move=> a. by rewrite norm_conjC (CyclicCharacters.kernel_unit primitive).
- move=> a Ha. apply: coefficient_nontrivial Ht _.
  by move: Ha; rewrite -val_eqE /=.
- by rewrite coefficient_energy.
Qed.

End Coefficients.
End CurveCoefficient.

Print Assumptions CurveCoefficient.canonical_coefficient_bound.
Print Assumptions CurveCoefficient.coefficient_nontrivial.
Print Assumptions CurveCoefficient.coefficient_energy.
Print Assumptions CurveCoefficient.spectrum_gap.
