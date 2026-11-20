From HB Require Import structures.
From mathcomp Require Import boot order algebra reals field_tactic.
From infotheo Require Import fdist variation_dist.
From Masking Require Import finite_masking word_masking shared_ladder leakage_counterexamples
  noisy_leakage noisy_bit_example.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory FiniteMasking NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FieldLeakageTests.
(* F2 regression only, not a Curve25519 execution or whole-bank leakage theorem. *)
Local Notation bit := (WordMasking.word 0).
Local Notation K := [the finZmodType of bit].

(* One-bit values have HW zero or one; this is not a whole-bank observation. *)
Definition bit_HW (x : bit) : bool := x != 0.

Lemma bit_HW_value x : nat_of_bool (bit_HW x) = val x.
Proof. case: x => -[|[|i]] // H; by vm_compute. Qed.

Definition cross_HW (s r : bit) : bool :=
  bit_HW (LeakageCounterexamples.square_cross s r).

Section Noise.
Variable R : realType.

(* The mask is uniform in F2; noise is exactly the existing binomial-two channel. *)
Definition intermediate_law (s : bit) : R.-fdist 'I_5 :=
  uniform R K >>= (fun r => NoisyBitExample.plain_law R (cross_HW s r)).

Lemma mask_mass r : uniform R K r = 2^-1.
Proof. by rewrite /uniform fdist_uniformE WordMasking.word_cardinality. Qed.

Lemma zero_secret_mass y :
  intermediate_law 0 y =
    (NoisyBitExample.plain_law R false y + NoisyBitExample.plain_law R true y) / 2.
Proof.
rewrite /intermediate_law fdistbindE.
under eq_bigr do rewrite mask_mass.
rewrite !big_ord_recr big_ord0 /=.
change (0 + 2^-1 * NoisyBitExample.plain_law R false y +
  2^-1 * NoisyBitExample.plain_law R true y =
  (NoisyBitExample.plain_law R false y + NoisyBitExample.plain_law R true y) / 2).
field by rewrite ?pnatr_eq0.
Qed.

Lemma one_secret_mass y : intermediate_law 1 y = NoisyBitExample.plain_law R false y.
Proof.
rewrite /intermediate_law fdistbindE.
under eq_bigr do rewrite mask_mass.
rewrite !big_ord_recr big_ord0 /=.
change (0 + 2^-1 * NoisyBitExample.plain_law R false y +
  2^-1 * NoisyBitExample.plain_law R false y = NoisyBitExample.plain_law R false y).
field by rewrite ?pnatr_eq0.
Qed.

Theorem intermediate_TV : TV (intermediate_law 0) (intermediate_law 1) = 1 / 4.
Proof.
have H y : intermediate_law 0 y - intermediate_law 1 y =
    (NoisyBitExample.plain_law R true y - NoisyBitExample.plain_law R false y) / 2.
  rewrite zero_secret_mass one_secret_mass. field by rewrite ?pnatr_eq0.
rewrite /TV /var_dist.
under eq_bigr do rewrite H normrM normfV normr_nat.
rewrite -big_distrl.
change (TV (NoisyBitExample.plain_law R true) (NoisyBitExample.plain_law R false) / 2 = 1 / 4).
rewrite /TV symmetric_var_dist -/(TV (NoisyBitExample.plain_law R false)
  (NoisyBitExample.plain_law R true)) NoisyBitExample.plain_TV.
field by rewrite ?pnatr_eq0.
Qed.

Theorem intermediate_laws_distinct : intermediate_law 0 <> intermediate_law 1.
Proof.
move=> H. have E := equal_law_TV_zero H.
rewrite intermediate_TV in E.
have Hnz : (1 / 4 : R) != 0 by rewrite mulf_eq0 oner_eq0 invr_eq0 pnatr_eq0.
by rewrite E eqxx in Hnz.
Qed.

(* Fresh output refresh does not remove the preceding intermediate observation. *)
Theorem final_Y_uniform (s r : bit) :
  fdistmap (fun fresh => (SharedLadder.shared_mul (split s r) (split s r) fresh).2)
    (uniform R K) = uniform R K.
Proof. exact: SharedLadder.shared_mul_output_uniform. Qed.

End Noise.
End FieldLeakageTests.

Print Assumptions FieldLeakageTests.intermediate_TV.
Print Assumptions FieldLeakageTests.intermediate_laws_distinct.
Print Assumptions FieldLeakageTests.final_Y_uniform.
