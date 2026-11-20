From Stdlib Require Import ZArith.
From mathcomp Require Import boot order algebra reals field_tactic.
From infotheo Require Import fdist.
From Masking Require Import cube_encoding curve_snapshot noisy_leakage fiat_field field_aggregate_spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module CurveSnapshotBudget.

Lemma squared_budgetE n :
  CurveSnapshot.squared_budget n = (255*n.+1).+1%:R * (49/64)^+(2*(n.+1-2)).
Proof.
rewrite /CurveSnapshot.squared_budget /CurveSnapshot.spectral_budget.
have E (a x : rat) : a*(2*x)^+2/4 = a*x^+2 by field.
by rewrite E -exprM (mulnC (n.+1-2)%N 2).
Qed.

Lemma rational_certificate M k t :
  (M * 49 ^ k * 2 ^ t <= 64 ^ k)%N ->
  M%:R * (49/64:rat)^+k <= 2^-t.
Proof.
move=> H.
have E : M%:R * (49/64:rat)^+k = (M * 49 ^ k)%:R/(64 ^ k)%:R.
  by rewrite natrM !natrX exprMn exprVn mulrA.
rewrite E ler_pdivrMr ?natrX ?exprn_gt0 ?ltr0n //.
rewrite mulrC ler_pdivlMr ?exprn_gt0 ?ltr0n //.
rewrite -natrX -natrM -[64 ^+ k]natrX.
by rewrite ler_nat.
Qed.

(* Only the closed cross-products are evaluated, after conversion to binary integers. *)
Lemma binary_certificate (M k t : nat) :
  Z.le (Z.mul (Z.mul (Z.of_nat M) (Z.pow 49 (Z.of_nat k)))
    (Z.pow 2 (Z.of_nat t))) (Z.pow 64 (Z.of_nat k)) ->
  (M * 49 ^ k * 2 ^ t <= 64 ^ k)%N.
Proof.
move=> H. apply/leP. apply (proj2 (Nat2Z.inj_le _ _)).
by rewrite !mulnE !CubeEncoding.expn_nat !Nat2Z.inj_mul !Nat2Z.inj_pow.
Qed.

Lemma integer_certificate_128 : (32641 * 49^252 * 2^80 <= 64^252)%N.
Proof.
apply: binary_certificate.
vm_compute. discriminate.
Qed.

Lemma integer_certificate_256 : (65281 * 49^508 * 2^176 <= 64^508)%N.
Proof.
apply: binary_certificate.
vm_compute. discriminate.
Qed.

(* The API counts extra shares: 127 means 128 total, and 255 means 256 total. *)
Theorem squared_budget_128 : CurveSnapshot.squared_budget 127 <= (2:rat)^-80.
Proof.
rewrite squared_budgetE.
change (is_true (32641%:R * (49/64:rat)^+252 <= 2^-80)).
exact: rational_certificate integer_certificate_128.
Qed.

Theorem squared_budget_256 : CurveSnapshot.squared_budget 255 <= (2:rat)^- 176.
Proof.
rewrite squared_budgetE.
change (is_true (65281%:R * (49/64:rat)^+508 <= 2^- 176)).
exact: rational_certificate integer_certificate_256.
Qed.

Lemma real_certificate (R : realType) (b : rat) t :
  b <= (2:rat)^-(t*2) -> @ratr R b <= ((2:R)^-t)^+2.
Proof.
move=> H.
rewrite -(@ler_rat R) in H.
rewrite -exprVn -exprM exprVn.
by rewrite fmorphV rmorphXn rmorph_nat /= in H.
Qed.

Lemma real_budget_128 (R : realType) :
  @ratr R (CurveSnapshot.squared_budget 127) <= ((2:R)^-40)^+2.
Proof. exact: (@real_certificate R _ 40 squared_budget_128). Qed.

Lemma real_budget_256 (R : realType) :
  @ratr R (CurveSnapshot.squared_budget 255) <= ((2:R)^-88)^+2.
Proof. exact: (@real_certificate R _ 88 squared_budget_256). Qed.

Section Snapshot.
Variable q : positive.
Variable q_gt1 : Z.lt 1 (Z.pos q).
Hypothesis modulus : Z.to_nat (Z.pos q) = (2^255-19)%N.
Variable R : realType.
Local Notation K := (FiatField.ring q_gt1).
Local Notation law n := (@FieldAggregateSpectral.law q q_gt1 255 n R).

Theorem actual_TV_128 (s1 s2 : K) :
  NoisyLeakage.bounded_indistinguishable ((2:R)^-40) (law 127 s1) (law 127 s2).
Proof.
apply: (@CurveSnapshot.actual_TV_bound q q_gt1 modulus 127 erefl R).
- by rewrite invr_ge0 exprn_ge0 ?ler0n.
- exact: real_budget_128.
Qed.

Theorem actual_TV_256 (s1 s2 : K) :
  NoisyLeakage.bounded_indistinguishable ((2:R)^-88) (law 255 s1) (law 255 s2).
Proof.
apply: (@CurveSnapshot.actual_TV_bound q q_gt1 modulus 255 erefl R).
- by rewrite invr_ge0 exprn_ge0 ?ler0n.
- exact: real_budget_256.
Qed.

(* A single snapshot followed by the same channel for both secrets. *)
Theorem noisy_TV_128 (O : finType) (channel : 'I_(255*128).+1 -> R.-fdist O)
    (s1 s2 : K) :
  NoisyLeakage.bounded_indistinguishable ((2:R)^-40)
    (law 127 s1 >>= channel) (law 127 s2 >>= channel).
Proof.
apply: (@CurveSnapshot.noisy_TV_bound q q_gt1 modulus 127 erefl R).
- by rewrite invr_ge0 exprn_ge0 ?ler0n.
- exact: real_budget_128.
Qed.

Theorem noisy_TV_256 (O : finType) (channel : 'I_(255*256).+1 -> R.-fdist O)
    (s1 s2 : K) :
  NoisyLeakage.bounded_indistinguishable ((2:R)^-88)
    (law 255 s1 >>= channel) (law 255 s2 >>= channel).
Proof.
apply: (@CurveSnapshot.noisy_TV_bound q q_gt1 modulus 255 erefl R).
- by rewrite invr_ge0 exprn_ge0 ?ler0n.
- exact: real_budget_256.
Qed.

End Snapshot.
End CurveSnapshotBudget.

Print Assumptions CurveSnapshotBudget.squared_budget_128.
Print Assumptions CurveSnapshotBudget.squared_budget_256.
Print Assumptions CurveSnapshotBudget.actual_TV_128.
Print Assumptions CurveSnapshotBudget.noisy_TV_256.
