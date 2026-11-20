From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import accelerator accelerator_correctness.
From Stdlib Require Import ZArith Bits Lia.
Import LadderAccelerator AcceleratorCorrectness.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module AcceleratorCorrectnessTests.
  Example reduce_maximum :
    Zmod.unsigned (fn.interp reduce (bits.of_Z 512 (2^512-1))) = 1443.
  Proof.
    rewrite reduce_correct, bits.unsigned_of_Z_small by lia.
    vm_compute. reflexivity.
  Qed.

  Example subtract_full_width :
    Zmod.unsigned (fn.interp (arithmetic Sub) (bits.of_Z 255 0, bits.of_Z 255 (2^255-1))) =
    prime-18.
  Proof.
    rewrite arithmetic_correct, !bits.unsigned_of_Z_small by lia.
    vm_compute. reflexivity.
  Qed.

  Example square_full_width :
    Zmod.unsigned (fn.interp (arithmetic Mul)
      (bits.of_Z 255 (2^255-1), bits.of_Z 255 (2^255-1))) = 324.
  Proof.
    rewrite arithmetic_correct, !bits.unsigned_of_Z_small by lia.
    vm_compute. reflexivity.
  Qed.

  Example basepoint_step :
    output_Z (run 18 (initial 9 1 0 9 1)) = ((1,0),(324,36)).
  Proof.
    rewrite ladder_step_correct by lia.
    vm_compute. reflexivity.
  Qed.

  Example zero_step :
    output_Z (run 18 (initial 0 0 0 0 0)) = ((0,0),(0,0)).
  Proof.
    rewrite ladder_step_correct by lia.
    vm_compute. reflexivity.
  Qed.

  Print Assumptions fold_mod.
  Print Assumptions fold255_correct.
  Print Assumptions three_folds_bound.
  Print Assumptions reduce_correct.
  Print Assumptions arithmetic_correct.
  Print Assumptions arithmetic_canonical.
  Print Assumptions ladder_schedule.
  Print Assumptions ladder_step_correct.
End AcceleratorCorrectnessTests.
