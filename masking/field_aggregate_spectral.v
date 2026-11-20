From Stdlib Require Import ZArith.
From Crypto Require Import Spec.ModularArithmetic Arithmetic.ModularArithmeticTheorems.
From mathcomp Require Import boot order algebra reals field_tactic.
From infotheo Require Import fdist.
From Masking Require Import fiat_field cube_encoding field_characters arithmetic_shares
  arithmetic_privacy arithmetic_aggregate cyclic_characters field_coefficient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FieldAggregateSpectral.

Section Fibers.
Variable C : numClosedFieldType.
Variables X Y : finType.
Variable P : pred X.
Variable observe : X -> Y.

Lemma weighted_fiber_count (f : Y -> C) :
  \sum_y #|[pred x | P x && (observe x == y)]|%:R * f y =
    \sum_(x | P x) f (observe x).
Proof.
  rewrite (partition_big observe predT) //.
  apply: eq_bigr => y _.
  transitivity (\sum_(x | P x && (observe x == y)) f y).
    by rewrite sumr_const -[RHS]mulr_natl.
  by apply: eq_bigr => x /andP [_ /eqP ->].
Qed.

End Fibers.

Section Field.
Variable q : positive.
Variable q_gt1 : Z.lt 1 (Z.pos q).
Variables w n : nat.
Local Notation K := (FiatField.ring q_gt1).
Local Notation p := (Z.to_nat (Z.pos q)).
Local Notation V := [the finType of {ffun 'I_n.+1 -> K}].
Local Notation M := (w * n.+1).+1%N.

Definition hw (x : K) : nat :=
  CubeEncoding.canonical_HW w (F.to_Z x).

Lemma hw_bound x : (hw x <= w)%N.
Proof.
  have H : (hw x <= \sum_(j < w) 1)%N.
    apply: leq_sum => j _; exact: leq_b1.
  by rewrite sum_nat_const card_ord muln1 in H.
Qed.

Definition total_HW (r : V) : nat := \sum_i hw (r i).

Lemma total_HW_bound r : (total_HW r <= w * n.+1)%N.
Proof.
  have H : (total_HW r <= \sum_(i : 'I_n.+1) w)%N.
    apply: leq_sum => i _; exact: hw_bound.
  by rewrite sum_nat_const card_ord mulnC in H.
Qed.

Lemma total_HW_noalias r : (total_HW r < M)%N.
Proof. by rewrite ltnS; exact: total_HW_bound. Qed.

Definition observe (r : V) : 'I_M := Ordinal (total_HW_noalias r).

Lemma observe_value r : val (observe r) = total_HW r.
Proof. by []. Qed.

Definition count s h := ArithmeticAggregate.joint_count observe s h.

Definition mass s h : rat := (count s h)%:R / (p%:R)^+n.

Definition law (R : realType) s :=
  fdistmap observe (ArithmeticPrivacy.sharing_law R n s).

Theorem actual_mass (R : realType) s h : law R s h = @ratr R (mass s h).
Proof.
  rewrite /law ArithmeticAggregate.aggregate_count_formula /mass /count.
  by rewrite fmorph_div rmorphXn !rmorph_nat FieldCharacters.field_card.
Qed.

Section Transform.
Variable C : numClosedFieldType.
Variable zeta : C.
Hypothesis primitive : p.-primitive_root zeta.
Local Notation chi := (FieldCharacters.character zeta).

Lemma count_generating (t : C) s :
  \sum_h (count s h)%:R * t ^+ val h =
    \sum_(r : V | ArithmeticShares.reconstruct r == s) \prod_i t ^+ hw (r i).
Proof.
  rewrite /count /ArithmeticAggregate.joint_count weighted_fiber_count.
  by apply: eq_bigr => r _; rewrite observe_value /total_HW prodrXr.
Qed.

Lemma tuple_product (t : C) a :
  \sum_(r : V) (\prod_i chi a (r i)) * (\prod_i t ^+ hw (r i)) =
    (\sum_(x : K) chi a x * t ^+ hw x)^+n.+1.
Proof.
  under eq_bigr do rewrite -big_split.
  rewrite -(bigA_distr_bigA (fun (_ : 'I_n.+1) (x : K) => chi a x * t ^+ hw x)).
  by rewrite prodr_const card_ord.
Qed.

Lemma single_coefficient (t : C) a :
  (\sum_(x : K) chi a x * t ^+ hw x) / p%:R = FieldCoefficient.coefficient w zeta t a.
Proof.
  rewrite /FieldCoefficient.coefficient /CyclicCharacters.normalized_transform.
  congr (_ / _).
  rewrite (reindex (fun i : 'I_p => (FiatField.of_ordinal i : K))).
  - apply: onW_bij; exists (@FiatField.to_ordinal q).
    + exact: FieldCharacters.ordinal_reverse.
    + exact: FiatField.ordinal_cancel.
  - apply: eq_bigr => i _.
    by rewrite /FieldCharacters.character /hw (FieldCharacters.ordinal_reverse q_gt1)
      (FieldCharacters.canonical_of_ordinal q_gt1).
Qed.

Lemma filtered_generating (t : C) s :
  (\sum_(r : V | ArithmeticShares.reconstruct r == s) \prod_i t ^+ hw (r i)) =
    (\sum_a (chi a s)^* * (\sum_(x : K) chi a x * t ^+ hw x)^+n.+1) / p%:R.
Proof.
  rewrite big_mkcond.
  have E (r : V) : (if ArithmeticShares.reconstruct r == s then \prod_i t ^+ hw (r i) else 0) =
      \sum_a ((chi a s)^* * ((\prod_i chi a (r i)) * (\prod_i t ^+ hw (r i)))) / p%:R.
    transitivity (((\sum_a (chi a s)^* * \prod_i chi a (r i)) / p%:R) *
      (\prod_i t ^+ hw (r i))).
      rewrite -(FieldCharacters.reconstruction_filter primitive).
      by case: ifP => _; rewrite ?mul1r ?mul0r.
    rewrite !mulr_suml; apply: eq_bigr => a _. ring.
  under eq_bigr do rewrite E.
  rewrite exchange_big mulr_suml.
  apply: eq_bigr => a _.
  by rewrite -mulr_suml -mulr_sumr tuple_product.
Qed.

Theorem mass_generating (t : C) s :
  \sum_h @ratr C (mass s h) * t ^+ val h =
    FieldCoefficient.spectrum w zeta t (FiatField.to_ordinal s) n.+1.
Proof.
  rewrite /mass.
  under eq_bigr do rewrite fmorph_div rmorphXn !rmorph_nat mulrAC.
  rewrite -mulr_suml count_generating filtered_generating /FieldCoefficient.spectrum.
  rewrite !mulr_suml.
  apply: eq_bigr => a _.
  rewrite -single_coefficient exprMn exprVn [(p%:R : C)^+n.+1]exprS
    invfM /FieldCharacters.character.
  ring.
Qed.

End Transform.
End Field.
End FieldAggregateSpectral.

Print Assumptions FieldAggregateSpectral.actual_mass.
Print Assumptions FieldAggregateSpectral.mass_generating.
