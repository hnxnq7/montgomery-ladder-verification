From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import masked_controller masked_controller_program masked_controller_schedule.
From Masking Require Import fiat_field arithmetic_shares.
From Stdlib Require Import ZArith Bits Vector Lia.

Module MaskedControllerFunctional.
Module C := MaskedController.
Module M := C.M.
Module B := C.B.
Module P := MaskedControllerProgram.
Module Sched := MaskedControllerSchedule.
Import GRing.Theory.
Local Open Scope Z_scope.

Definition patched_iteration (i : nat) : list C.micro :=
  C.Micro 0 (Z.of_nat i) 0 261 :: List.tl C.bit_program.

Definition collect_values (a : P.Bank) : P.Bank := fun i =>
  if Nat.eqb i 260 then a 261%nat else
  if Nat.eqb i 259 then a 276%nat else
  if Nat.eqb i 258 then a 274%nat else
  if Nat.eqb i 257 then a 281%nat else
  if Nat.eqb i 256 then a 277%nat else a i.

Definition coords (a : P.Bank) := ((a 256%nat,a 257%nat),(a 258%nat,a 259%nat)).
Definition bitfield (b : bool) : FiatField.curve25519 := if b then 1%R else 0%R.

Definition value n (a : type.interp (C.Bank n)) (i : nat) :=
  C.reconstruct_group n (@M.read (M.Shares (S n)) C.groups a i).

Lemma anchor_decode n w (i : 'I_(S n)) :
  M.decode (S n) (fn.interp (C.anchor n) w) i =
  if i == ord0 then M.decode_word w else 0%R.
Proof.
  rewrite /M.decode ffunE C.anchor_interp (M.read_upd _ _ _ _ (elimT ltP (ltn_ord i))).
  case E: (i == ord0).
  - move/eqP: E => ->. reflexivity.
  - have Hneq : Nat.eqb (val i) 0 = false.
    { apply Nat.eqb_neq. intro H.
      have Hi : i = ord0 by apply val_inj; exact H.
      subst i. by rewrite eqxx in E. }
    rewrite Hneq C.read_default. exact: FiatField.encode_zero.
Qed.

Lemma anchor_reconstruct n w :
  C.reconstruct_group n (fn.interp (C.anchor n) w) = M.decode_word w.
Proof.
  rewrite /C.reconstruct_group /ArithmeticShares.reconstruct.
  under eq_bigr do rewrite anchor_decode.
  by rewrite -big_mkcond big_pred1_eq.
Qed.

Definition bit_word (raw : bits 255) (i : nat) : bits 255 :=
  bits.of_Z 255 (Zmod.unsigned (unop.interp (unop.Slice (Z.of_nat i) 1) raw)).

Lemma unsigned_extend_bit (b : bits 1) :
  Zmod.unsigned (bits.of_Z 255 (Zmod.unsigned b)) = Zmod.unsigned b.
Proof.
  apply bits.unsigned_of_Z_small.
  have Hb := bits.unsigned_range b ltac:(lia). cbn in *. lia.
Qed.

Lemma bit_word_unsigned raw i :
  Zmod.unsigned (bit_word raw i) = Z.b2z (Z.testbit (Zmod.unsigned raw) (Z.of_nat i)).
Proof.
  rewrite /bit_word unsigned_extend_bit.
  change (Zmod.unsigned (Zmod.firstn 1 (Zmod.skipn (Z.of_nat i) raw)) =
    Z.b2z (Z.testbit (Zmod.unsigned raw) (Z.of_nat i))).
  have Hindex : 0 <= Z.of_nat i by lia.
  rewrite bits.unsigned_firstn (bits.unsigned_skipn _ Hindex).
  symmetry. apply Z.testbit_spec'. lia.
Qed.

Definition scalar_bit (raw : bits 255) (i : nat) : FiatField.curve25519 :=
  if Z.testbit (Zmod.unsigned raw) (Z.of_nat i) then 1%R else 0%R.

Lemma bit_word_decode raw i : M.decode_word (bit_word raw i) = scalar_bit raw i.
Proof.
  rewrite /M.decode_word bit_word_unsigned /scalar_bit.
  case: (Z.testbit (Zmod.unsigned raw) (Z.of_nat i)); reflexivity.
Qed.

Lemma load_bits_read n positions raw a (j : 'I_C.groups) :
  all (fun i => ltn i 255%nat) positions ->
  @M.read (M.Shares (S n)) C.groups (fn.interp (C.load_bits n positions) (raw,a)) (val j) =
  if val j \in positions then fn.interp (C.anchor n) (bit_word raw (val j))
  else @M.read (M.Shares (S n)) C.groups a (val j).
Proof.
  revert a. induction positions as [|i rest IH]; intros a Hvalid; [reflexivity|].
  move/andP: Hvalid => [Hi Hrest].
  have HiN : Nat.lt i 255 := elimT ltP Hi.
  have HiZ : 0 <= Z.of_nat i < 2^9 by lia.
  rewrite C.load_bits_cons_interp (bits.unsigned_of_Z_small _ HiZ) Nat2Z.id.
  rewrite (IH _ Hrest) in_cons.
  case Erest: (val j \in rest); first by rewrite orbT.
  rewrite orbF (M.read_upd _ _ _ _ (elimT ltP (ltn_ord j))).
  case E: (val j == i).
  - move/eqP: E => E.
    have En : Nat.eqb (nat_of_ord j) i = true by apply Nat.eqb_eq; exact E.
    rewrite En. change (fn.interp (C.anchor n) (bit_word raw i) =
      fn.interp (C.anchor n) (bit_word raw (val j))). by rewrite E.
  - have En : Nat.eqb (nat_of_ord j) i = false.
    { apply Nat.eqb_neq. intro H. have H' : val j = i := H.
      rewrite H' eqxx in E. discriminate. }
    by rewrite En.
Qed.

Lemma collect_read n a (j : 'I_C.groups) :
  @M.read (M.Shares (S n)) C.groups (fn.interp (C.collect n) a) (val j) =
  let get i := @M.read (M.Shares (S n)) C.groups a i in
  if Nat.eqb (val j) 260 then get 261%nat else
  if Nat.eqb (val j) 259 then get 276%nat else
  if Nat.eqb (val j) 258 then get 274%nat else
  if Nat.eqb (val j) 257 then get 281%nat else
  if Nat.eqb (val j) 256 then get 277%nat else get (val j).
Proof.
  rewrite C.collect_interp.
  by rewrite !(M.read_upd _ _ _ _ (elimT ltP (ltn_ord j))).
Qed.

Lemma scalar_positions_valid : all (fun i => ltn i 255%nat) (iota 0 255).
Proof. apply/allP => i. rewrite mem_iota add0n => /andP [_ Hi]. exact Hi. Qed.

Local Opaque C.load_bits C.load_bank C.anchor C.Core.arithmetic.

Lemma load_updates_read n (a : type.interp (C.Bank n))
    (one xp : type.interp (M.Shares (S n))) (j : 'I_C.groups) :
  @M.read (M.Shares (S n)) C.groups
    (domain.Vector.upd
      (domain.Vector.upd
        (domain.Vector.upd
          (domain.Vector.upd
            (domain.Vector.upd a 255 (fun _ => xp)) 256 (fun _ => one))
          258 (fun _ => xp)) 259 (fun _ => one)) 263 (fun _ => one)) (val j) =
  if Nat.eqb (val j) 263 then one else
  if Nat.eqb (val j) 259 then one else
  if Nat.eqb (val j) 258 then xp else
  if Nat.eqb (val j) 256 then one else
  if Nat.eqb (val j) 255 then xp else @M.read (M.Shares (S n)) C.groups a (val j).
Proof. by rewrite !(M.read_upd _ _ _ _ (elimT ltP (ltn_ord j))). Qed.

Lemma load_bank_read_updates n input (j : 'I_C.groups) :
  @M.read (M.Shares (S n)) C.groups (fn.interp (C.load_bank n) input) (val j) =
  let one := fn.interp (C.anchor n) (bits.of_Z 255 1) in
  let xp := fn.interp (C.anchor n)
    (fn.interp (C.Core.arithmetic C.Core.Add) (input.1,bits.of_Z 255 0)) in
  if Nat.eqb (val j) 263 then one else
  if Nat.eqb (val j) 259 then one else
  if Nat.eqb (val j) 258 then xp else
  if Nat.eqb (val j) 256 then one else
  if Nat.eqb (val j) 255 then xp else
  @M.read (M.Shares (S n)) C.groups
    (fn.interp (C.load_bits n (iota 0 255)) (input.2,type.default (C.Bank n))) (val j).
Proof. rewrite C.load_bank_interp. exact: load_updates_read. Qed.

Lemma load_bank_read n input (j : 'I_C.groups) :
  @M.read (M.Shares (S n)) C.groups (fn.interp (C.load_bank n) input) (val j) =
  let one := fn.interp (C.anchor n) (bits.of_Z 255 1) in
  let xP := fn.interp (C.anchor n)
    (fn.interp (C.Core.arithmetic C.Core.Add) (input.1,bits.of_Z 255 0)) in
  if Nat.eqb (val j) 263 then one else
  if Nat.eqb (val j) 259 then one else
  if Nat.eqb (val j) 258 then xP else
  if Nat.eqb (val j) 256 then one else
  if Nat.eqb (val j) 255 then xP else
  if ltn (val j) 255%nat then fn.interp (C.anchor n) (bit_word input.2 (val j))
  else type.default (M.Shares (S n)).
Proof.
  rewrite load_bank_read_updates.
  rewrite (load_bits_read _ _ _ _ _ scalar_positions_valid).
  by rewrite mem_iota add0n leq0n andTb C.read_default.
Qed.

Lemma default_reconstruct n :
  C.reconstruct_group n (type.default (M.Shares (S n))) = 0%R.
Proof.
  rewrite /C.reconstruct_group /ArithmeticShares.reconstruct /M.decode.
  apply big1 => i _. rewrite ffunE C.read_default. exact: FiatField.encode_zero.
Qed.

Lemma reduced_input_decode w :
  M.decode_word (fn.interp (C.Core.arithmetic C.Core.Add) (w,bits.of_Z 255 0)) = M.decode_word w.
Proof.
  rewrite M.decode_arithmetic /M.field_operation.
  change ((M.decode_word w + 0)%R = M.decode_word w). exact: addr0.
Qed.

Definition loaded_value (input : type.interp C.Load) (i : nat) : FiatField.curve25519 :=
  if Nat.eqb i 263 then 1%R else
  if Nat.eqb i 259 then 1%R else
  if Nat.eqb i 258 then M.decode_word input.1 else
  if Nat.eqb i 256 then 1%R else
  if Nat.eqb i 255 then M.decode_word input.1 else
  if ltn i 255%nat then scalar_bit input.2 i else 0%R.

Theorem load_reconstruct n input (j : 'I_C.groups) :
  value n (fn.interp (C.load_bank n) input) (val j) = loaded_value input (val j).
Proof.
  rewrite /value load_bank_read /loaded_value.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    rewrite ?anchor_reconstruct ?default_reconstruct ?reduced_input_decode ?bit_word_decode;
    reflexivity.
Qed.

Definition a24 : FiatField.curve25519 :=
  FiatField.encode FiatField.curve25519_modulus_gt1 121666.

Definition operand_value n (a : type.interp (C.Bank n)) (i : bits 9) :=
  if C.equal_bits i (bits.of_Z 9 282) then 1%R else
  if C.equal_bits i (bits.of_Z 9 283) then a24 else
  value n a (Z.to_nat (Zmod.unsigned i)).

Theorem operand_reconstruct n a i :
  C.reconstruct_group n (fn.interp (C.read_operand n) (a,i)) = operand_value n a i.
Proof.
  rewrite C.read_operand_interp /operand_value.
  case: (C.equal_bits i (bits.of_Z 9 282)); first by rewrite anchor_reconstruct.
  case: (C.equal_bits i (bits.of_Z 9 283)); [rewrite anchor_reconstruct | reflexivity].
  reflexivity.
Qed.

Definition collected_value n (a : type.interp (C.Bank n)) (i : nat) :=
  collect_values (value n a) i.

Theorem collect_reconstruct n a (j : 'I_C.groups) :
  value n (fn.interp (C.collect n) a) (val j) = collected_value n a (val j).
Proof.
  rewrite /value collect_read /collected_value /collect_values /value.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Theorem tick_prepare_value n p (j : 'I_C.groups) :
  value n (fn.interp (C.tick n) p).2 (val j) =
  value n (fn.interp (C.prepare_bank n) (p.1,(p.2.1,p.2.2.1))) (val j).
Proof. exact: C.tick_reconstruct. Qed.

Theorem launch_reconstruct n input randomness (j : 'I_C.groups) :
  value n (Sched.launch n input randomness).2 (val j) = loaded_value input (val j).
Proof.
  rewrite /Sched.launch tick_prepare_value.
  change (value n (fn.interp (C.load_bank n) input) (val j) = loaded_value input (val j)).
  exact: load_reconstruct.
Qed.

Local Opaque C.execute C.collect C.decode.
Lemma prepare_bit_execute n index pc bank masks :
  Zmod.eqb pc (bits.of_Z 5 31) = false ->
  fn.interp (C.prepare_bank n)
    (((bits.of_Z 3 1,(index,pc)),bank),(Sched.no_command,masks)) =
  fn.interp (C.execute n)
    (fn.interp C.decode (bits.of_Z 3 1,(index,pc)),(bank,masks)).
Proof.
  intro H.
  change ((if Zmod.nonzero (Zmod.and (Zmod.embed_bool true)
      (Zmod.embed_bool (Zmod.eqb pc (bits.of_Z 5 31))))
    then fn.interp (C.collect n) bank
    else fn.interp (C.execute n)
      (fn.interp C.decode (bits.of_Z 3 1,(index,pc)),(bank,masks))) =
    fn.interp (C.execute n)
      (fn.interp C.decode (bits.of_Z 3 1,(index,pc)),(bank,masks))).
  by rewrite H.
Qed.

Lemma prepare_active_execute n phase index pc bank masks :
  phase = 2 \/ phase = 3 \/ phase = 4 \/ phase = 5 ->
  fn.interp (C.prepare_bank n)
    (((bits.of_Z 3 phase,(index,pc)),bank),(Sched.no_command,masks)) =
  fn.interp (C.execute n)
    (fn.interp C.decode (bits.of_Z 3 phase,(index,pc)),(bank,masks)).
Proof. intro H. destruct H as [H | [H | [H | H]]]; subst phase; reflexivity. Qed.

End MaskedControllerFunctional.
Print Assumptions MaskedControllerFunctional.anchor_reconstruct.
Print Assumptions MaskedControllerFunctional.bit_word_unsigned.
Print Assumptions MaskedControllerFunctional.load_bits_read.
Print Assumptions MaskedControllerFunctional.collect_read.
Print Assumptions MaskedControllerFunctional.load_reconstruct.
Print Assumptions MaskedControllerFunctional.operand_reconstruct.
Print Assumptions MaskedControllerFunctional.collect_reconstruct.
Print Assumptions MaskedControllerFunctional.launch_reconstruct.
Print Assumptions MaskedControllerFunctional.tick_prepare_value.
