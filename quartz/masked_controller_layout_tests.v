From quartz.lang Require Import domain Syntax transform.
From LadderQuartz Require Import masked_controller.
From Stdlib Require Import ZArith Bits Vector.
Import Syntax.type.
Local Open Scope Z_scope.

Module MaskedControllerLayoutTests.
Module C := MaskedController.

(* Pair components pack high-first; array elements pack low-first. *)
Example pair_order :
  Zmod.unsigned (@transform.type.pack (Pair (Bits 8) (Bits 8))
    (bits.of_Z 8 18, bits.of_Z 8 52)) = 4660.
Proof. vm_compute. reflexivity. Qed.

Example array_order :
  Zmod.unsigned (@transform.type.pack (Array (Bits 8) 2)
    (Vector.cons _ (bits.of_Z 8 18) _
      (Vector.cons _ (bits.of_Z 8 52) _ (Vector.nil _)))) = 13330.
Proof. vm_compute. reflexivity. Qed.

Example control_order :
  Zmod.unsigned (@transform.type.pack C.Control
    (bits.of_Z 3 3, (bits.of_Z 8 165, bits.of_Z 5 17))) = 29873.
Proof. vm_compute. reflexivity. Qed.

Example state_256_bits :
  transform.type.size (C.State 255) = 18408976.
Proof. vm_compute. reflexivity. Qed.

Example randomness_256_bits :
  transform.type.size (C.Randomness 255) = 35048730.
Proof. vm_compute. reflexivity. Qed.

(* Encoded input volume, not a lower bound on required entropy. *)
Example scheduled_randomness_256_bits :
  transform.type.size (C.Randomness 255) * Z.of_nat C.scheduled_edges = 304222976400.
Proof. vm_compute. reflexivity. Qed.

End MaskedControllerLayoutTests.
Print Assumptions MaskedControllerLayoutTests.pair_order.
Print Assumptions MaskedControllerLayoutTests.array_order.
Print Assumptions MaskedControllerLayoutTests.control_order.
Print Assumptions MaskedControllerLayoutTests.state_256_bits.
Print Assumptions MaskedControllerLayoutTests.randomness_256_bits.
Print Assumptions MaskedControllerLayoutTests.scheduled_randomness_256_bits.
