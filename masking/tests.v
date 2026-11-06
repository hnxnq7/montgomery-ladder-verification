From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking word_masking shared_ladder ladder_distribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Example equal_totals_do_not_imply_equal_distributions :
  foldr addn 0 [:: 0; 2] = foldr addn 0 [:: 1; 1] /\
  ~~ perm_eq [:: 0; 2]%N [:: 1; 1]%N.
Proof. by split. Qed.

Example equal_marginals_do_not_imply_equal_joint_distributions :
  let a := [:: (false, false); (true, true)] in
  let b := [:: (false, true); (true, false)] in
  perm_eq (map fst a) (map fst b) /\
  perm_eq (map snd a) (map snd b) /\ ~~ perm_eq a b.
Proof. by split => //; split. Qed.

Lemma observing_both_shares_distinguishes (R : realType) :
  @FiniteMasking.share_distribution R [the finZmodType of WordMasking.word 1] 0 <>
  @FiniteMasking.share_distribution R [the finZmodType of WordMasking.word 1] 1.
Proof.
move/FiniteMasking.both_shares_reveal => /eqP.
by rewrite eq_sym oner_eq0.
Qed.

Example shared_multiply_wraps_modulo_four :
  FiniteMasking.reconstruct
    (SharedLadder.shared_mul
      (FiniteMasking.split (3 : WordMasking.word 1) 2)
      (FiniteMasking.split (3 : WordMasking.word 1) 1) 3) = 1.
Proof. apply/val_inj. by vm_compute. Qed.

Example shared_ladder_two_bit (m : SharedLadder.mask_tape [the finComNzRingType of WordMasking.word 1]) :
  SharedLadder.reconstruct_coordinates
    (SharedLadder.shared_step
      (FiniteMasking.split (2 : WordMasking.word 1) 1)
      (FiniteMasking.split 1 2) (FiniteMasking.split 1 3) (FiniteMasking.split 0 1)
      (FiniteMasking.split 1 2) (FiniteMasking.split 1 3) m) = ((1, 0), (0, 0)).
Proof.
rewrite SharedLadder.shared_step_correct !FiniteMasking.split_correct.
rewrite /SharedLadder.clear_step.
by congr ((_, _), (_, _)); apply/val_inj; vm_compute.
Qed.

Print Assumptions FiniteMasking.uniform_add.
Print Assumptions FiniteMasking.copies_permutation.
Print Assumptions FiniteMasking.both_shares_reveal.
Print Assumptions FiniteMasking.output_distribution_independent.
Print Assumptions WordMasking.every_width_independent.
Print Assumptions SharedLadder.shared_step_correct.
Print Assumptions MaskedLadder.correct_and_output_independent.
