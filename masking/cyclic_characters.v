From mathcomp Require Import boot order algebra reals field_tactic.
From Masking Require Import arithmetic_spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module CyclicCharacters.
Section Grid.
Variable C : numClosedFieldType.
Variable m : nat.
Variable z : C.
Hypothesis primitive : m.-primitive_root z.

Lemma modulus_positive : (0 < m)%N.
Proof. exact: prim_order_gt0 primitive. Qed.

Lemma root_nonzero : z != 0.
Proof. by rewrite (prim_root_eq0 primitive) (gtn_eqF modulus_positive). Qed.

Lemma root_unit : `|z| = 1.
Proof.
apply/eqP. rewrite -(pexpr_eq1 modulus_positive (normr_ge0 z)).
by rewrite -normrX (prim_expr_order primitive) normr1.
Qed.

Lemma unit_conjugate (w : C) : `|w| = 1 -> w^* = w^-1.
Proof. move=> H. by rewrite invC_norm H expr1n invr1 mul1r. Qed.

Definition kernel (a x : 'I_m) : C :=
  z ^+ (val a * val x).

Lemma kernelE a x : kernel a x = (z ^+ val x) ^+ val a.
Proof. by rewrite /kernel mulnC exprM. Qed.

Lemma kernel_unit a x : `|kernel a x| = 1.
Proof. by rewrite /kernel normrX root_unit expr1n. Qed.

Lemma geometric_zero (w : C) : w ^+ m = 1 -> w != 1 -> \sum_(a < m) w ^+ a = 0.
Proof.
move=> Horder Hne.
have /eqP : (w - 1) * (\sum_(a < m) w ^+ a) = 0.
  by rewrite -subrX1 Horder subrr.
by rewrite mulf_eq0 subr_eq0 (negbTE Hne) orFb => /eqP.
Qed.

Lemma ratio_order (x y : 'I_m) : (z ^+ val x / z ^+ val y) ^+ m = 1.
Proof.
rewrite exprMn exprVn -!exprM (mulnC (val x) m) (mulnC (val y) m) !exprM.
by rewrite (prim_expr_order primitive) !expr1n invr1 mulr1.
Qed.

Lemma ratio_nontrivial (x y : 'I_m) : x != y -> z ^+ val x / z ^+ val y != 1.
Proof.
move=> Hxy. have Hy : z ^+ val y != 0 by exact: expf_neq0 root_nonzero.
have Hpowers : z ^+ val x != z ^+ val y.
  by rewrite (eq_prim_root_expr primitive) !modn_small ?ltn_ord // -val_eqE.
apply/eqP => H.
have E := congr1 (fun w => w * z ^+ val y) H.
rewrite (divfK Hy) mul1r in E.
by move: Hpowers; rewrite E eqxx.
Qed.

Lemma kernel_cross a x y :
  kernel a x * (kernel a y)^* = (z ^+ val x / z ^+ val y) ^+ val a.
Proof.
rewrite !kernelE rmorphXn /=.
have Hy : `|z ^+ val y| = 1 by rewrite normrX root_unit expr1n.
by rewrite (unit_conjugate Hy) exprMn exprVn.
Qed.

(* Ordinal indices work for both prime field moduli and composite weight grids. *)
Theorem kernel_orthogonal (x y : 'I_m) :
  \sum_a kernel a x * (kernel a y)^* = if x == y then m%:R else 0.
Proof.
case: eqP => [->|Hxy].
- under eq_bigr do rewrite -normCK kernel_unit expr1n.
  by rewrite sumr_const card_ord.
- under eq_bigr do rewrite kernel_cross.
  apply: geometric_zero (ratio_order x y) _.
  apply: ratio_nontrivial. by apply/eqP.
Qed.

Definition normalized_transform (g : 'I_m -> C) (a : 'I_m) : C :=
  (\sum_x kernel a x * g x) / m%:R.

Theorem normalized_energy (g : 'I_m -> C) :
  (forall x, `|g x| = 1) -> \sum_a `|normalized_transform g a| ^+ 2 = 1.
Proof.
move=> Hg.
have Hparseval := @ArithmeticSpectral.finite_parseval C [the finType of 'I_m]
  [the finType of 'I_m] kernel m%:R kernel_orthogonal g.
have Hsum a : (\sum_x kernel a x * g x) = ArithmeticSpectral.transform kernel g a.
  by apply: eq_bigr => x _; rewrite mulrC.
under eq_bigr do rewrite /normalized_transform normrM normfV normr_nat exprMn Hsum.
rewrite -big_distrl /= Hparseval.
under eq_bigr do rewrite Hg expr1n.
rewrite sumr_const card_ord.
have Hm : (m%:R : C) != 0 by rewrite pnatr_eq0 (gtn_eqF modulus_positive).
field.
Qed.

End Grid.
End CyclicCharacters.

Print Assumptions CyclicCharacters.kernel_orthogonal.
Print Assumptions CyclicCharacters.normalized_energy.
