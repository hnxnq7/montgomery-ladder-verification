From Stdlib Require Import ZArith Bits List Vector Lia.
Import ListNotations.
Open Scope Z_scope.

Module RegisterHW.

Definition bit_count {n} (w : bits n) (indices : list nat) : nat :=
  List.fold_right (fun i acc =>
    ((if Z.testbit (Zmod.unsigned w) (Z.of_nat i) then 1 else 0) + acc)%nat) 0%nat indices.

Definition word_HW {n} (w : bits n) : nat :=
  bit_count w (List.seq 0 (Z.to_nat n)).

Lemma complement_bit n (w : bits n) i :
  0 <= i < n ->
  Z.testbit (Zmod.unsigned (Zmod.not w)) i = negb (Z.testbit (Zmod.unsigned w) i).
Proof.
  intros Hi. rewrite bits.unsigned_not, Z.ldiff_spec, Z.ones_spec_low by lia.
  reflexivity.
Qed.

Lemma complement_count n (w : bits n) indices :
  List.Forall (fun i => 0 <= Z.of_nat i < n) indices ->
  (bit_count w indices + bit_count (Zmod.not w) indices)%nat = List.length indices.
Proof.
  intros H; induction H.
  - reflexivity.
  - change (((if Z.testbit (Zmod.unsigned w) (Z.of_nat x) then 1 else 0) + bit_count w l) +
      ((if Z.testbit (Zmod.unsigned (Zmod.not w)) (Z.of_nat x) then 1 else 0) +
      bit_count (Zmod.not w) l) = S (List.length l))%nat.
    rewrite complement_bit by assumption.
    destruct (Z.testbit (Zmod.unsigned w) (Z.of_nat x)); simpl in *; lia.
Qed.

Theorem word_complement n (w : bits n) :
  0 <= n -> (word_HW w + word_HW (Zmod.not w))%nat = Z.to_nat n.
Proof.
  intros Hn. unfold word_HW.
  rewrite complement_count.
  - apply List.length_seq.
  - apply List.Forall_forall. intros i Hi.
    apply List.in_seq in Hi. destruct Hi as [_ Hi].
    apply (proj1 (Nat2Z.inj_lt i (Z.to_nat n))) in Hi.
    rewrite Z2Nat.id in Hi by assumption. lia.
Qed.

Fixpoint bank_HW {n count} (words : Vector.t (bits n) count) : nat :=
  match words with
  | Vector.nil _ => 0%nat
  | Vector.cons _ w _ rest => (word_HW w + bank_HW rest)%nat
  end.

Theorem bank_complement n count (words : Vector.t (bits n) count) :
  0 <= n ->
  (bank_HW words + bank_HW (Vector.map Zmod.not words))%nat = (count * Z.to_nat n)%nat.
Proof.
  intros Hn. induction words; simpl.
  - reflexivity.
  - pose proof (word_complement n h Hn). lia.
Qed.

End RegisterHW.

Print Assumptions RegisterHW.word_complement.
Print Assumptions RegisterHW.bank_complement.
