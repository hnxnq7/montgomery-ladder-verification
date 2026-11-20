From Stdlib Require Import ZArith Lia.
From LadderQuartz Require Import accelerator accelerator_correctness.
Require Import ladder_math.
Import LadderAccelerator AcceleratorCorrectness.
Open Scope Z_scope.

Module AcceleratorLadderBridge.

Definition mathematical_step x1 x2 z2 x3 z3 :=
  let '(xd, zd, xa, za) := LadderStep prime 121666 x1 x2 z2 x3 z3 in
  ((xd, zd), (xa, za)).

Lemma formula_matches_math x1 x2 z2 x3 z3 :
  ladder_formula (field_operation Add) (field_operation Sub) (field_operation Mul)
    121666 x1 x2 z2 x3 z3 = mathematical_step x1 x2 z2 x3 z3.
Proof. reflexivity. Qed.

Theorem ladder_step_matches_math x1 x2 z2 x3 z3 :
  0 <= x1 < prime -> 0 <= x2 < prime -> 0 <= z2 < prime ->
  0 <= x3 < prime -> 0 <= z3 < prime ->
  output_Z (run 18 (initial x1 x2 z2 x3 z3)) = mathematical_step x1 x2 z2 x3 z3.
Proof.
  intros. rewrite ladder_step_correct; try (unfold prime in *; lia).
  exact (formula_matches_math x1 x2 z2 x3 z3).
Qed.

End AcceleratorLadderBridge.

Print Assumptions AcceleratorLadderBridge.ladder_step_matches_math.
