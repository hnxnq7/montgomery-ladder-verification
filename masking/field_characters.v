From Stdlib Require Import ZArith Lia.
From Crypto Require Import Spec.ModularArithmetic Arithmetic.ModularArithmeticTheorems.
From mathcomp Require Import boot order algebra reals.
From Masking Require Import fiat_field cube_encoding cyclic_characters arithmetic_shares.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module FieldCharacters.
Section Field.
Variable q : positive.
Variable q_gt1 : Z.lt 1 (Z.pos q).
Local Notation K := (FiatField.ring q_gt1).
Local Notation p := (Z.to_nat (Z.pos q)).

Lemma modulus_positive : (0 < p)%N.
Proof. apply/ltP; have := Pos2Z.is_pos q; lia. Qed.

Lemma ordinal_Z (i : 'I_p) : Z.le 0 (Z.of_nat i) /\ Z.lt (Z.of_nat i) (Z.pos q).
Proof.
  have Hi : Nat.lt (val i) p by apply/ltP; exact: ltn_ord.
  have Hq := Pos2Z.is_pos q.
  have Hz := proj1 (Nat2Z.inj_lt (val i) p) Hi.
  have Ep : Z.of_nat p = Z.pos q by apply Z2Nat.id; lia.
  rewrite Ep in Hz; split; [exact: Nat2Z.is_nonneg | exact Hz].
Qed.

Lemma ordinal_reverse : cancel (@FiatField.of_ordinal q) (@FiatField.to_ordinal q).
Proof.
  move=> i; apply/val_inj.
  change (Z.to_nat (F.to_Z (F.of_Z q (Z.of_nat i))) = val i).
  rewrite F.to_Z_of_Z.
  rewrite (Z.mod_small _ _ (ordinal_Z i)).
  exact: Nat2Z.id.
Qed.

Lemma field_card : #|K| = p.
Proof.
  rewrite -(card_ord p); apply: bij_eq_card.
  exists (@FiatField.of_ordinal q).
  - exact: FiatField.ordinal_cancel.
  - exact: ordinal_reverse.
Qed.

Lemma canonical_ordinal (x : K) : Z.of_nat (FiatField.to_ordinal x) = F.to_Z x.
Proof.
  rewrite /FiatField.to_ordinal /= Z2Nat.id //.
  exact: (proj1 (F.to_Z_range x (Pos2Z.is_pos q))).
Qed.

Lemma canonical_of_ordinal (i : 'I_p) : F.to_Z (FiatField.of_ordinal i) = Z.of_nat i.
Proof.
  rewrite /FiatField.of_ordinal F.to_Z_of_Z.
  exact: Z.mod_small (ordinal_Z i).
Qed.

Lemma ordinal_add (x y : K) :
  val (FiatField.to_ordinal (x + y)) =
    ((val (FiatField.to_ordinal x) + val (FiatField.to_ordinal y)) %% p)%N.
Proof.
  have Hx := proj1 (F.to_Z_range x (Pos2Z.is_pos q)).
  have Hy := proj1 (F.to_Z_range y (Pos2Z.is_pos q)).
  have Hq := Pos2Z.is_pos q.
  change (Z.to_nat (F.to_Z (F.add x y)) =
    ((Z.to_nat (F.to_Z x) + Z.to_nat (F.to_Z y)) %% p)%N).
  rewrite F.to_Z_add.
  rewrite Z2Nat.inj_mod; try lia.
  rewrite Z2Nat.inj_add; try lia.
  by rewrite -CubeEncoding.modn_nat ?modulus_positive // plusE.
Qed.

Section Characters.
Variable C : numClosedFieldType.
Variable zeta : C.
Hypothesis primitive : p.-primitive_root zeta.

Definition character (a : 'I_p) (x : K) : C :=
  CyclicCharacters.kernel zeta a (FiatField.to_ordinal x).

Lemma character_unit a x : `|character a x| = 1.
Proof. by rewrite /character (CyclicCharacters.kernel_unit primitive). Qed.

Lemma character_zero a : character a 0 = 1.
Proof.
  rewrite /character /CyclicCharacters.kernel /FiatField.to_ordinal /=.
  by rewrite muln0 expr0.
Qed.

Lemma character_trivial x : character (Ordinal modulus_positive) x = 1.
Proof. by rewrite /character /CyclicCharacters.kernel /= mul0n expr0. Qed.

Lemma character_add a x y : character a (x + y) = character a x * character a y.
Proof.
  rewrite /character /CyclicCharacters.kernel ordinal_add.
  rewrite -[LHS](prim_expr_mod primitive) modnMmr (prim_expr_mod primitive).
  by rewrite mulnDr exprD.
Qed.

Lemma character_sum (I : finType) (f : I -> K) a :
  character a (\sum_i f i) = \prod_i character a (f i).
Proof. exact: (big_morph (character a) (character_add a) (character_zero a)). Qed.

Lemma character_orthogonal x y :
  \sum_a character a x * (character a y)^* = if x == y then p%:R else 0.
Proof.
  rewrite /character (CyclicCharacters.kernel_orthogonal primitive).
  have Hinj : injective (fun x : K => FiatField.to_ordinal x).
    exact: can_inj (@FiatField.ordinal_cancel q).
  by rewrite (inj_eq Hinj).
Qed.

Theorem reconstruction_filter n (r : {ffun 'I_n -> K}) s :
  (if ArithmeticShares.reconstruct r == s then 1 else 0) =
    (\sum_a (character a s)^* * \prod_i character a (r i)) / p%:R.
Proof.
  under eq_bigr do rewrite -character_sum mulrC.
  rewrite -/(@ArithmeticShares.reconstruct K n r) character_orthogonal.
  case: ifP => _; last by rewrite mul0r.
  by rewrite divff // pnatr_eq0 (gtn_eqF modulus_positive).
Qed.

End Characters.
End Field.
End FieldCharacters.

Print Assumptions FieldCharacters.field_card.
Print Assumptions FieldCharacters.character_add.
Print Assumptions FieldCharacters.reconstruction_filter.
