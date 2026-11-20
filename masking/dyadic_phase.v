From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Module DyadicPhase.

Lemma power_succ n : 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n.
Proof. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. Qed.

Lemma crossing bound p d :
  0 < p -> 0 < d -> 2 * d <= p -> p <= 4 * 2 ^ Z.of_nat bound * d ->
  exists j, (j <= bound)%nat /\ p <= 4 * 2 ^ Z.of_nat j * d /\ 2 * 2 ^ Z.of_nat j * d <= p.
Proof.
  revert p d. induction bound as [|bound IH]; intros p d Hp Hd Hhalf Hreach.
  - exists O. change (p <= 4*d) in Hreach.
    change ((0 <= 0)%nat /\ p <= 4*d /\ 2*d <= p). lia.
  - destruct (Z_le_dec p (4*d)) as [Hnow|Hlater].
    + exists O. change ((0 <= S bound)%nat /\ p <= 4*d /\ 2*d <= p). lia.
    + rewrite power_succ in Hreach.
      assert (Hhalf' : 2 * (2*d) <= p) by lia.
      assert (Hreach' : p <= 4 * 2 ^ Z.of_nat bound * (2*d)) by nia.
      destruct (IH p (2*d) Hp ltac:(lia) Hhalf' Hreach') as [j [Hj [Hlow Hhigh]]].
      exists (S j). rewrite power_succ. split; [lia|]. split; nia.
Qed.

Definition prime : Z := 2^255 - 19.

Lemma prime_positive : 0 < prime.
Proof. vm_compute. reflexivity. Qed.

Lemma nearest_positive a : 0 < a < prime -> 0 < Z.min a (prime-a).
Proof. intros H. apply Z.min_glb_lt; lia. Qed.

Lemma nearest_half a : 2 * Z.min a (prime-a) <= prime.
Proof.
  pose proof (Z.le_min_l a (prime-a)).
  pose proof (Z.le_min_r a (prime-a)). lia.
Qed.

Theorem curve25519_crossing a : 0 < a < prime ->
  exists j, (j <= 253)%nat /\
    prime <= 4 * 2 ^ Z.of_nat j * Z.min a (prime-a) /\
    2 * 2 ^ Z.of_nat j * Z.min a (prime-a) <= prime.
Proof.
  intro Ha. apply crossing; try apply prime_positive; try apply nearest_half.
  - apply nearest_positive. exact Ha.
  - pose proof (nearest_positive a Ha) as Hd.
    assert (Hp : prime < 4 * 2 ^ Z.of_nat 253) by (vm_compute; reflexivity).
    assert (Hpow : 0 < 2 ^ Z.of_nat 253) by (apply Z.pow_pos_nonneg; lia).
    nia.
Qed.

(* A nonzero frequency has two adjacent bit phases separated by at least a quarter turn. *)
Theorem curve25519_phase a : 0 < a < prime ->
  exists j, (j <= 253)%nat /\
    prime <= 4 * ((a * 2 ^ Z.of_nat j) mod prime) /\
    4 * ((a * 2 ^ Z.of_nat j) mod prime) <= 3 * prime.
Proof.
  intro Ha. destruct (curve25519_crossing a Ha) as [j [Hj [Hlo Hhi]]].
  pose proof prime_positive as Hp.
  pose proof (nearest_positive a Ha) as Hd.
  assert (Hpow : 0 < 2 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
  exists j. split; [exact Hj|].
  destruct (Z_le_dec a (prime-a)) as [Hnear|Hfar].
  - rewrite Z.min_l in Hlo, Hhi by exact Hnear.
    rewrite Z.mod_small by nia. split; nia.
  - rewrite Z.min_r in Hlo, Hhi by lia.
    replace (a * 2 ^ Z.of_nat j) with
      ((prime - (prime-a) * 2 ^ Z.of_nat j) + (2 ^ Z.of_nat j - 1) * prime) by ring.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_small by nia. split; nia.
Qed.

Print Assumptions curve25519_phase.
End DyadicPhase.
