From Stdlib Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import boot algebra.
From Crypto Require Import Spec.ModularArithmetic Arithmetic.ModularArithmeticTheorems.
Require Import ladder_math.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Set Warnings "-redundant-canonical-projection".

Module FiatField.

Section FiniteCarrier.
Variable q : positive.

Lemma to_nat_bound (x : F q) :
  ssrnat.ltn (Z.to_nat (F.to_Z x)) (Z.to_nat (Z.pos q)).
Proof.
  apply/ltP.
  have Hrange := F.to_Z_range x (Pos2Z.is_pos q).
  apply (proj1 (Z2Nat.inj_lt _ _ (proj1 Hrange) (Z.lt_le_incl _ _ (Pos2Z.is_pos q)))).
  exact (proj2 Hrange).
Qed.

(* The ordinal witnesses finiteness; field values remain Fiat's canonical residues. *)
Definition to_ordinal (x : F q) : 'I_(Z.to_nat (Z.pos q)) :=
  Ordinal (to_nat_bound x).

Definition of_ordinal (i : 'I_(Z.to_nat (Z.pos q))) : F q :=
  F.of_Z q (Z.of_nat i).

Lemma ordinal_cancel : cancel to_ordinal of_ordinal.
Proof.
  move=> x; rewrite /of_ordinal /to_ordinal /=.
  have Hnonneg := proj1 (F.to_Z_range x (Pos2Z.is_pos q)).
  rewrite Z2Nat.id //.
  exact: F.of_Z_to_Z.
Qed.

HB.instance Definition _ := Finite.copy (F q) (can_type ordinal_cancel).

Lemma add_associative : associative (@F.add q).
Proof. exact (Radd_assoc (F.ring_theory q)). Qed.

Lemma add_commutative : commutative (@F.add q).
Proof. exact (Radd_comm (F.ring_theory q)). Qed.

Lemma add_zero : left_id (@F.zero q) (@F.add q).
Proof. exact (Radd_0_l (F.ring_theory q)). Qed.

Lemma add_opposite : left_inverse (@F.zero q) (@F.opp q) (@F.add q).
Proof.
  move=> x; rewrite add_commutative.
  exact (Ropp_def (F.ring_theory q) x).
Qed.

HB.instance Definition _ := GRing.isZmodule.Build (F q)
  add_associative add_commutative add_zero add_opposite.

Lemma mul_associative : associative (@F.mul q).
Proof. exact (Rmul_assoc (F.ring_theory q)). Qed.

Lemma mul_commutative : commutative (@F.mul q).
Proof. exact (Rmul_comm (F.ring_theory q)). Qed.

Lemma mul_one : left_id (@F.one q) (@F.mul q).
Proof. exact (Rmul_1_l (F.ring_theory q)). Qed.

Lemma mul_distributive : left_distributive (@F.mul q) (@F.add q).
Proof. exact (Rdistr_l (F.ring_theory q)). Qed.

Variable q_gt1 : (1 < Z.pos q)%Z.

Lemma one_not_zero : @F.one q != @F.zero q.
Proof.
  apply/eqP => H.
  have Hz := f_equal (@F.to_Z q) H.
  change (F.to_Z (F.of_Z q 1) = F.to_Z (F.of_Z q 0)) in Hz.
  rewrite !F.to_Z_of_Z !Z.mod_small in Hz; lia.
Qed.

HB.instance Definition _ := GRing.Zmodule_isComNzRing.Build (F q)
  mul_associative mul_commutative mul_one mul_distributive one_not_zero.

Definition ring : finComNzRingType :=
  [the finComNzRingType of (F q : Type)].

End FiniteCarrier.

Section Encoding.
Variable q : positive.
Variable q_gt1 : (1 < Z.pos q)%Z.
Local Notation K := (ring q_gt1).

Definition encode (z : Z) : K :=
  F.of_Z q z.

Lemma encode_zero : encode 0 = 0%R.
Proof. reflexivity. Qed.

Lemma encode_one : encode 1 = 1%R.
Proof. reflexivity. Qed.

Lemma encode_add x y : encode (x + y) = (encode x + encode y)%R.
Proof. exact: F.of_Z_add. Qed.

Lemma encode_sub x y : encode (x - y) = (encode x - encode y)%R.
Proof. exact: F.of_Z_sub. Qed.

Lemma encode_mul x y : encode (x * y) = (encode x * encode y)%R.
Proof. exact: F.of_Z_mul. Qed.

Lemma encode_opp x : encode (- x) = (- encode x)%R.
Proof. exact: F.of_Z_opp. Qed.

Lemma encode_mod x : encode (x mod Z.pos q) = encode x.
Proof. symmetry. exact: F.of_Z_mod. Qed.

Lemma encode_to_Z (x : K) : encode (F.to_Z x) = x.
Proof. exact: F.of_Z_to_Z. Qed.

Lemma encode_fadd x y :
  encode (fadd (Z.pos q) x y) = (encode x + encode y)%R.
Proof.
  change (F.of_Z q ((x + y) mod Z.pos q) = F.add (F.of_Z q x) (F.of_Z q y)).
  rewrite <- F.of_Z_mod. exact: F.of_Z_add.
Qed.

Lemma encode_fsub x y :
  encode (fsub (Z.pos q) x y) = (encode x - encode y)%R.
Proof.
  change (F.of_Z q ((x - y) mod Z.pos q) = F.sub (F.of_Z q x) (F.of_Z q y)).
  rewrite <- F.of_Z_mod. exact: F.of_Z_sub.
Qed.

Lemma encode_fmul x y :
  encode (fmul (Z.pos q) x y) = (encode x * encode y)%R.
Proof.
  change (F.of_Z q ((x * y) mod Z.pos q) = F.mul (F.of_Z q x) (F.of_Z q y)).
  rewrite <- F.of_Z_mod. exact: F.of_Z_mul.
Qed.

End Encoding.

Definition curve25519_modulus : positive :=
  (2 ^ 255 - 19)%positive.

Lemma curve25519_modulus_gt1 : (1 < Z.pos curve25519_modulus)%Z.
Proof. vm_compute; reflexivity. Qed.

Definition curve25519 : finComNzRingType :=
  ring curve25519_modulus_gt1.

Lemma curve25519_zero : (0 : curve25519)%R = F.zero.
Proof. reflexivity. Qed.

Lemma curve25519_one : (1 : curve25519)%R = F.one.
Proof. reflexivity. Qed.

Lemma curve25519_add (x y : curve25519) : (x + y)%R = F.add x y.
Proof. reflexivity. Qed.

Lemma curve25519_mul (x y : curve25519) : (x * y)%R = F.mul x y.
Proof. reflexivity. Qed.

Lemma curve25519_opp (x : curve25519) : (- x)%R = F.opp x.
Proof. reflexivity. Qed.

Lemma curve25519_sub (x y : curve25519) : (x - y)%R = F.sub x y.
Proof. reflexivity. Qed.

End FiatField.
