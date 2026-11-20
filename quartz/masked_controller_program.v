From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From quartz.lang Require Import Syntax.
From LadderQuartz Require Import masked_controller.
From Masking Require Import fiat_field shared_ladder.
From Stdlib Require Import ZArith List Bits Lia.
Import GRing.Theory.
Local Open Scope ring_scope.

Module MaskedControllerProgram.
(* Decoded-value semantics for the controller's fixed microprogram. *)
Module C := MaskedController.
Local Notation K := FiatField.curve25519.
Definition a24 : K := FiatField.encode FiatField.curve25519_modulus_gt1 121666.
Definition Bank := nat -> K.

Definition valid_instruction (i : C.micro) : Prop :=
  (0 <= C.opcode i < 4 /\ 0 <= C.lhs i < 284 /\
    0 <= C.rhs i < 284 /\ 0 <= C.destination i < 282)%Z.

Lemma equal_encoded width x y :
  (0 <= x < 2^width)%Z -> (0 <= y < 2^width)%Z ->
  C.equal_bits (bits.of_Z width x) (bits.of_Z width y) = Z.eqb x y.
Proof.
  move=> Hx Hy. rewrite /C.equal_bits domain.Zmod.nonzero_bool /Zmod.eqb.
  by rewrite (bits.unsigned_of_Z_small _ Hx) (bits.unsigned_of_Z_small _ Hy).
Qed.

Theorem encode_instruction_exact i : valid_instruction i ->
  let ins := C.encode_instruction i in
  Zmod.unsigned ins.1 = C.opcode i /\ Zmod.unsigned ins.2.1 = C.lhs i /\
  Zmod.unsigned ins.2.2.1 = C.rhs i /\ Zmod.unsigned ins.2.2.2 = C.destination i.
Proof.
  move=> H. unfold valid_instruction in H.
  cbn [C.encode_instruction fst snd].
  repeat split; apply bits.unsigned_of_Z_small; lia.
Qed.

Theorem ladder_program_valid : List.Forall valid_instruction C.ladder_program.
Proof. repeat constructor; cbn; lia. Qed.

Theorem bit_program_valid : List.Forall valid_instruction C.bit_program.
Proof. repeat constructor; cbn; lia. Qed.

Theorem final_program_valid : List.Forall valid_instruction C.final_program.
Proof. repeat constructor; cbn; lia. Qed.

Lemma bit_copy_valid i : (0 <= i < 255)%Z -> valid_instruction (C.Micro 0 i 0 261).
Proof. unfold valid_instruction; cbn; lia. Qed.

Definition operand (a : Bank) (address : Z) : K :=
  if Z.eqb address 282 then 1 else
  if Z.eqb address 283 then a24 else a (Z.to_nat address).

Definition execute (i : C.micro) (a : Bank) : Bank :=
  let x := operand a (C.lhs i) in
  let y := operand a (C.rhs i) in
  let value := if Z.eqb (C.opcode i) 0 then x else
    if Z.eqb (C.opcode i) 1 then x + y else
    if Z.eqb (C.opcode i) 2 then x - y else x * y in
  fun j => if Nat.eqb j (Z.to_nat (C.destination i)) then value else a j.

Definition run (code : list C.micro) (a : Bank) : Bank :=
  List.fold_left (fun bank ins => execute ins bank) code a.

Theorem ladder_program_correct a :
  let out := run C.ladder_program a in
  ((out 277%nat,out 281%nat),(out 274%nat,out 276%nat)) =
  SharedLadder.clear_step a24 (a 255%nat) (a 256%nat) (a 257%nat) (a 258%nat) (a 259%nat).
Proof. reflexivity. Qed.

Theorem ladder_program_preserves_input a :
  run C.ladder_program a 255%nat = a 255%nat.
Proof. reflexivity. Qed.
Definition pair_swap_program : list C.micro :=
  C.swap_program 262 256 258 ++ C.swap_program 262 257 259.

Theorem pair_swap_correct a (bit : bool) :
  a 262%nat = (if bit then 1 else 0) ->
  let out := run pair_swap_program a in
  ((out 256%nat,out 257%nat),(out 258%nat,out 259%nat)) =
  if bit then ((a 258%nat,a 259%nat),(a 256%nat,a 257%nat))
  else ((a 256%nat,a 257%nat),(a 258%nat,a 259%nat)).
Proof.
  move=> H.
  change (((a 256%nat + a 262%nat * (a 258%nat - a 256%nat),
             a 257%nat + a 262%nat * (a 259%nat - a 257%nat)),
            (a 258%nat - a 262%nat * (a 258%nat - a 256%nat),
             a 259%nat - a 262%nat * (a 259%nat - a 257%nat))) =
    if bit then ((a 258%nat,a 259%nat),(a 256%nat,a 257%nat))
    else ((a 256%nat,a 257%nat),(a 258%nat,a 259%nat))).
  rewrite H. clear H. case: bit.
  - rewrite !mul1r. congr ((_,_),(_,_)); first [by rewrite addrC subrK | by rewrite opprB addrC subrK].
  - by rewrite !mul0r ?addr0 ?subr0.
Qed.

Theorem pair_swap_preserves_input a : run pair_swap_program a 255%nat = a 255%nat.
Proof. reflexivity. Qed.
End MaskedControllerProgram.
Print Assumptions MaskedControllerProgram.ladder_program_correct.
Print Assumptions MaskedControllerProgram.pair_swap_correct.
Print Assumptions MaskedControllerProgram.encode_instruction_exact.
Print Assumptions MaskedControllerProgram.bit_program_valid.
