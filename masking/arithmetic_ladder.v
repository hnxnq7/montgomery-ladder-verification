From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From Masking Require Import arithmetic_shares shared_ladder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ArithmeticShares.
Local Open Scope ring_scope.

Module ArithmeticLadder.
Section Step.
Variable K : finComNzRingType.
Variable n : nat.
Local Notation Shares := (shares K n).

Definition coordinates := ((Shares * Shares) * (Shares * Shares))%type.
Definition mask_tape := {ffun 'I_18 -> masks K n}.

(* Addresses follow clear_step's 18 operations; linear operations need no masks.
   Separate addresses do not assert probabilistic independence. *)
Definition step (a24 xP X2 Z2 X3 Z3 : Shares) (randomness : mask_tape) : coordinates :=
  let U := add X2 Z2 in
  let V := sub X2 Z2 in
  let W := add X3 Z3 in
  let T := sub X3 Z3 in
  let U2 := sequential_multiply U U (randomness (inord 4)) in
  let V2 := sequential_multiply V V (randomness (inord 5)) in
  let UT := sequential_multiply U T (randomness (inord 6)) in
  let VW := sequential_multiply V W (randomness (inord 7)) in
  let Sp := add UT VW in
  let Sm := sub UT VW in
  let Xa := sequential_multiply Sp Sp (randomness (inord 10)) in
  let Sm2 := sequential_multiply Sm Sm (randomness (inord 11)) in
  let Za := sequential_multiply Sm2 xP (randomness (inord 12)) in
  let Xd := sequential_multiply U2 V2 (randomness (inord 13)) in
  let D := sub U2 V2 in
  let AD := sequential_multiply a24 D (randomness (inord 15)) in
  let T2 := add V2 AD in
  let Zd := sequential_multiply D T2 (randomness (inord 17)) in
  ((Xd, Zd), (Xa, Za)).

Definition reconstruct_coordinates (c : coordinates) : SharedLadder.coordinates K :=
  ((reconstruct c.1.1, reconstruct c.1.2), (reconstruct c.2.1, reconstruct c.2.2)).

(* Functional reference only; temporary storage and clearing belong to the circuit trace. *)
Theorem step_correct a24 xP X2 Z2 X3 Z3 randomness :
  reconstruct_coordinates (step a24 xP X2 Z2 X3 Z3 randomness) =
  SharedLadder.clear_step (reconstruct a24) (reconstruct xP)
    (reconstruct X2) (reconstruct Z2) (reconstruct X3) (reconstruct Z3).
Proof.
rewrite /step /reconstruct_coordinates /SharedLadder.clear_step /=.
by repeat first [rewrite add_correct | rewrite sub_correct | rewrite sequential_multiply_correct].
Qed.

End Step.
End ArithmeticLadder.

Print Assumptions ArithmeticLadder.step_correct.
