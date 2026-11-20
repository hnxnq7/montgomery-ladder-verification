From Stdlib Require Import ZArith.
From mathcomp Require Import boot order algebra reals.
From Masking Require Import arithmetic_spectral cyclic_characters cube_encoding cube_field_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module FieldCoefficient.
Section Coefficient.
Variable C : numClosedFieldType.
Variables w p : nat.
Variable z : C.
Hypothesis primitive : p.-primitive_root z.
Hypothesis modulus : p = (2 ^ w - 19)%N.
Hypothesis width : (39520 <= 2 ^ w)%N.

Definition coefficient (t : C) (a : 'I_p) :=
  CyclicCharacters.normalized_transform z
    (fun x : 'I_p => t ^+ CubeEncoding.canonical_HW w (Z.of_nat x)) a.

Lemma coefficientE t a :
  coefficient t a = CubeFieldBound.coefficient w p (z ^+ val a) t.
Proof.
  rewrite /coefficient /CyclicCharacters.normalized_transform /CubeFieldBound.coefficient.
  congr (_ / _). apply: eq_bigr => x _.
  by rewrite /CyclicCharacters.kernel /CubeFieldBound.term exprM.
Qed.

Theorem coefficient_nontrivial t a : `|t| = 1 -> val a != 0%N ->
  `|coefficient t a| <= 32/33.
Proof.
  move=> Ht Ha. rewrite coefficientE.
  have Hz : `|z ^+ val a| = 1.
    by rewrite normrX (CyclicCharacters.root_unit primitive) expr1n.
  have Hnz : z ^+ val a != 1.
    rewrite -[X in _ != X](expr0 z) (eq_prim_root_expr primitive).
    by rewrite modn_small ?ltn_ord // mod0n.
  have Hp : (z ^+ val a) ^+ (2 ^ w - 19) = 1.
    rewrite -modulus -exprM mulnC exprM (prim_expr_order primitive).
    by rewrite expr1n.
  have H := CubeFieldBound.canonical_coefficient_bound width Hz Hnz Hp Ht.
  by rewrite -modulus in H.
Qed.

Theorem coefficient_energy t : `|t| = 1 -> \sum_a `|coefficient t a| ^+ 2 = 1.
Proof.
  move=> Ht. rewrite /coefficient.
  apply: (@CyclicCharacters.normalized_energy C p z primitive).
  by move=> x; rewrite normrX Ht expr1n.
Qed.

Definition spectrum (t : C) (s : 'I_p) (count : nat) :=
  \sum_a (CyclicCharacters.kernel z a s)^* * coefficient t a ^+ count.

(* The exact aggregate-distribution bridge must identify its transform with this sum. *)
Theorem spectrum_gap t s1 s2 count : `|t| = 1 -> (2 <= count)%N ->
  `|spectrum t s1 count - spectrum t s2 count| <=
    2 * (32/33) ^+ (count - 2).
Proof.
  move=> Ht Hcount.
  pose zero : 'I_p := Ordinal (prim_order_gt0 primitive).
  rewrite /spectrum.
  apply: (@ArithmeticSpectral.coefficient_gap_n C [the finType of 'I_p] zero
    (coefficient t) (fun a => (CyclicCharacters.kernel z a s1)^*)
    (fun a => (CyclicCharacters.kernel z a s2)^*) (32/33)) => //.
  - by apply: divr_ge0; rewrite ler0n.
  - move=> a. by rewrite norm_conjC (CyclicCharacters.kernel_unit primitive).
  - move=> a. by rewrite norm_conjC (CyclicCharacters.kernel_unit primitive).
  - move=> a Ha. apply: coefficient_nontrivial Ht _.
    by move: Ha; rewrite -val_eqE /=.
  - by rewrite coefficient_energy.
Qed.

End Coefficient.
End FieldCoefficient.

Print Assumptions FieldCoefficient.coefficient_nontrivial.
Print Assumptions FieldCoefficient.coefficient_energy.
Print Assumptions FieldCoefficient.spectrum_gap.
