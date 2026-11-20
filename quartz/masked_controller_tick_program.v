From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import masked_controller masked_controller_program
  masked_controller_schedule masked_controller_functional.
From Stdlib Require Import ZArith Bits List Lia.

Module MaskedControllerTickProgram.
Module C := MaskedController.
Module F := MaskedControllerFunctional.
Module P := MaskedControllerProgram.
Module Sched := MaskedControllerSchedule.
Local Open Scope Z_scope.

Definition default_instruction := C.Micro 0 0 0 0.

Definition agrees (a b : P.Bank) := forall j, Nat.lt j C.groups -> a j = b j.

Lemma operand_encoded n bank address : 0 <= address < 284 ->
  C.reconstruct_group n (fn.interp (C.read_operand n) (bank,bits.of_Z 9 address)) =
  P.operand (F.value n bank) address.
Proof.
  intro H. rewrite F.operand_reconstruct /F.operand_value /P.operand.
  rewrite !P.equal_encoded; try lia.
  have Hwidth : 0 <= address < 2^9 by lia.
  rewrite (bits.unsigned_of_Z_small address Hwidth). reflexivity.
Qed.

Lemma execute_encoded_value n ins bank masks (j : 'I_C.groups) : P.valid_instruction ins ->
  F.value n (fn.interp (C.execute n) (C.encode_instruction ins,(bank,masks))) (val j) =
  P.execute ins (F.value n bank) (val j).
Proof.
  intros [Hop [Hl [Hr Hd]]].
  unfold F.value at 1. rewrite C.execute_reconstruct.
  cbn [C.encode_instruction fst snd].
  have Hwidth : 0 <= C.destination ins < 2^9 by lia.
  rewrite (bits.unsigned_of_Z_small (C.destination ins) Hwidth).
  unfold P.execute.
  destruct (Nat.eqb (val j) (Z.to_nat (C.destination ins))); [|reflexivity].
  unfold C.clear_instruction. cbn [C.encode_instruction fst snd].
  rewrite !operand_encoded; try lia.
  rewrite !P.equal_encoded; try lia. reflexivity.
Qed.

Theorem execute_encoded n ins bank masks : P.valid_instruction ins ->
  agrees (F.value n (fn.interp (C.execute n) (C.encode_instruction ins,(bank,masks))))
    (P.execute ins (F.value n bank)).
Proof.
  intros Hi j Hj. have Hj' : is_true (ltn j C.groups) by apply/ltP.
  exact (execute_encoded_value n ins bank masks (Ordinal Hj') Hi).
Qed.

Lemma operand_agrees a b address : agrees a b -> 0 <= address < 284 ->
  P.operand a address = P.operand b address.
Proof.
  intros Hab Ha. unfold P.operand.
  destruct (Z.eqb_spec address 282) as [H|H]; [reflexivity|].
  destruct (Z.eqb_spec address 283) as [H'|H']; [reflexivity|].
  apply Hab. unfold C.groups.
  apply (proj1 (Z2Nat.inj_lt address 282 ltac:(lia) ltac:(lia))). lia.
Qed.

Lemma execute_agrees ins a b : P.valid_instruction ins -> agrees a b ->
  agrees (P.execute ins a) (P.execute ins b).
Proof.
  intros [Hop [Hl [Hr Hd]]] Hab j Hj.
  unfold P.execute. rewrite (operand_agrees _ _ _ Hab Hl) (operand_agrees _ _ _ Hab Hr).
  destruct (Nat.eqb j (Z.to_nat (C.destination ins))); [reflexivity|exact (Hab j Hj)].
Qed.

Lemma run_agrees code a b : List.Forall P.valid_instruction code -> agrees a b ->
  agrees (P.run code a) (P.run code b).
Proof.
  revert a b. induction code as [|ins code IH]; intros a b Hvalid Hab; [exact Hab|].
  inversion Hvalid; subst.
  change (agrees (P.run code (P.execute ins a)) (P.run code (P.execute ins b))).
  apply IH; [assumption|]. apply execute_agrees; assumption.
Qed.

Lemma collect_agrees a b : agrees a b -> agrees (F.collect_values a) (F.collect_values b).
Proof.
  intros Hab j Hj. unfold F.collect_values.
  repeat match goal with |- context [if ?x then _ else _] => destruct x end;
    apply Hab; unfold C.groups in *; lia.
Qed.

Lemma ticks_add n a b randomness s :
  Sched.ticks n (Nat.add a b) randomness s =
  Sched.ticks n b randomness (Sched.ticks n a (fun i => randomness (Nat.add b i)) s).
Proof.
  revert s. induction a; intro s; cbn [Sched.ticks Nat.add]; first reflexivity.
  rewrite IHa. replace (Nat.add a b) with (Nat.add b a) by lia. reflexivity.
Qed.

Fixpoint scheduled (c : type.interp C.Control) (code : list C.micro) : Prop :=
  match code with
  | List.nil => True
  | ins :: rest => P.valid_instruction ins /\
      (forall n bank masks,
        fn.interp (C.prepare_bank n) ((c,bank),(Sched.no_command,masks)) =
        fn.interp (C.execute n) (C.encode_instruction ins,(bank,masks))) /\
      scheduled (fn.interp C.advance c) rest
  end.

Lemma scheduled_valid c code : scheduled c code -> List.Forall P.valid_instruction code.
Proof.
  revert c. induction code as [|ins code IH]; intros c H; [constructor|].
  destruct H as [Hi [Hstep Hrest]]. constructor; [exact Hi|exact (IH _ Hrest)].
Qed.

Lemma scheduled_from_trace c code : List.Forall P.valid_instruction code ->
  (forall pc, Nat.lt pc (List.length code) -> forall n bank masks,
    fn.interp (C.prepare_bank n) ((Sched.run pc c,bank),(Sched.no_command,masks)) =
    fn.interp (C.execute n) (C.encode_instruction (List.nth pc code default_instruction),(bank,masks))) ->
  scheduled c code.
Proof.
  revert c. induction code as [|ins code IH]; intros c Hvalid Htrace; [exact I|].
  inversion Hvalid; subst. split; [assumption|]. split.
  - intros n bank masks. exact (Htrace O ltac:(cbn; lia) n bank masks).
  - apply IH; [assumption|]. intros pc Hp n bank masks.
    exact (Htrace (S pc) ltac:(cbn; lia) n bank masks).
Qed.

Lemma run_succ_right count c :
  Sched.run (S count) c = fn.interp C.advance (Sched.run count c).
Proof. revert c. induction count; intro c; [reflexivity|exact (IHcount (fn.interp C.advance c))]. Qed.

Lemma patched_iteration_valid i : Nat.lt i 255 -> List.Forall P.valid_instruction (F.patched_iteration i).
Proof.
  intro Hi. constructor.
  - apply P.bit_copy_valid. lia.
  - pose proof P.bit_program_valid as H. inversion H. assumption.
Qed.

Lemma decode_iteration i pc : Nat.lt i 255 -> Nat.lt pc 31 ->
  fn.interp C.decode (Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) (Z.of_nat pc)) =
  C.encode_instruction (List.nth pc (F.patched_iteration i) default_instruction).
Proof.
  intros Hi Hp. destruct pc as [|pc].
  - rewrite Sched.decode_bit_zero.
    have HiZ : 0 <= Z.of_nat i < 2^8 by cbn; lia.
    rewrite (bits.unsigned_of_Z_small _ HiZ). reflexivity.
  - do 30 (destruct pc as [|pc]; [reflexivity|]). lia.
Qed.

Lemma advance_bit_pc index pc : Nat.lt pc 31 ->
  fn.interp C.advance (Sched.control 1 index (Z.of_nat pc)) =
  Sched.control 1 index (Z.of_nat (S pc)).
Proof. intro H. do 31 (destruct pc as [|pc]; [reflexivity|]). lia. Qed.

Lemma decode_final index pc : Nat.lt pc 8 ->
  fn.interp C.decode (Sched.control 2 index (Z.of_nat pc)) =
  C.encode_instruction (List.nth pc C.final_program default_instruction).
Proof. intro H. do 8 (destruct pc as [|pc]; [reflexivity|]). lia. Qed.

Lemma advance_final_pc index pc : Nat.lt pc 7 ->
  fn.interp C.advance (Sched.control 2 index (Z.of_nat pc)) =
  Sched.control 2 index (Z.of_nat (S pc)).
Proof. intro H. do 7 (destruct pc as [|pc]; [reflexivity|]). lia. Qed.

Lemma pc_not_collect pc : Nat.lt pc 31 ->
  Zmod.eqb (bits.of_Z 5 (Z.of_nat pc)) (bits.of_Z 5 31) = false.
Proof.
  intro H. unfold Zmod.eqb.
  have Hp : 0 <= Z.of_nat pc < 2^5 by cbn; lia.
  rewrite (bits.unsigned_of_Z_small _ Hp).
  change (Z.eqb (Z.of_nat pc) 31 = false). apply Z.eqb_neq. lia.
Qed.

Lemma prepare_iteration n i pc bank masks : Nat.lt i 255 -> Nat.lt pc 31 ->
  fn.interp (C.prepare_bank n)
    ((Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) (Z.of_nat pc),bank),(Sched.no_command,masks)) =
  fn.interp (C.execute n)
    (C.encode_instruction (List.nth pc (F.patched_iteration i) default_instruction),(bank,masks)).
Proof.
  intros Hi Hp. rewrite (F.prepare_bit_execute _ _ _ _ _ (pc_not_collect _ Hp)).
  by rewrite (decode_iteration _ _ Hi Hp).
Qed.

Lemma run_bit_prefix index pc : Nat.le pc 31 ->
  Sched.run pc (Sched.control 1 index 0) = Sched.control 1 index (Z.of_nat pc).
Proof.
  induction pc as [|pc IH]; intro H; [reflexivity|].
  rewrite run_succ_right (IH ltac:(lia)). apply advance_bit_pc. lia.
Qed.

Lemma iteration_scheduled i : Nat.lt i 255 ->
  scheduled (Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 0) (F.patched_iteration i).
Proof.
  intro Hi. apply scheduled_from_trace; [exact (patched_iteration_valid _ Hi)|].
  intros pc Hp n bank masks.
  change (Nat.lt pc 31) in Hp.
  rewrite (run_bit_prefix (bits.of_Z 8 (Z.of_nat i)) pc ltac:(lia)).
  exact (prepare_iteration _ _ _ _ _ Hi Hp).
Qed.

Lemma run_final_prefix index pc : Nat.le pc 7 ->
  Sched.run pc (Sched.control 2 index 0) = Sched.control 2 index (Z.of_nat pc).
Proof.
  induction pc as [|pc IH]; intro H; [reflexivity|].
  rewrite run_succ_right (IH ltac:(lia)). apply advance_final_pc. lia.
Qed.

Lemma final_scheduled index : scheduled (Sched.control 2 index 0) C.final_program.
Proof.
  apply scheduled_from_trace; [exact P.final_program_valid|].
  intros pc Hp n bank masks. change (Nat.lt pc 8) in Hp.
  rewrite (run_final_prefix index pc ltac:(lia)).
  have Hphase : 2 = 2 \/ 2 = 3 \/ 2 = 4 \/ 2 = 5 by left; reflexivity.
  rewrite (F.prepare_active_execute n 2 index (bits.of_Z 5 (Z.of_nat pc)) bank masks Hphase).
  by rewrite (decode_final _ _ Hp).
Qed.

Section Lift.
Local Opaque C.tick C.execute C.prepare_bank.
Variable n : nat.
Variable encoded : forall ins bank masks, P.valid_instruction ins ->
  agrees (F.value n (fn.interp (C.execute n) (C.encode_instruction ins,(bank,masks))))
    (P.execute ins (F.value n bank)).

Lemma scheduled_step c bank randomness ins : P.valid_instruction ins ->
  (forall masks, fn.interp (C.prepare_bank n) ((c,bank),(Sched.no_command,masks)) =
    fn.interp (C.execute n) (C.encode_instruction ins,(bank,masks))) ->
  agrees (F.value n (fn.interp (C.tick n) ((c,bank),(Sched.no_command,randomness))).2)
    (P.execute ins (F.value n bank)).
Proof.
  intros Hi Hstep j Hj.
  have Hj' : is_true (ltn j C.groups) by apply/ltP.
  rewrite (F.tick_prepare_value n _ (Ordinal Hj')) Hstep.
  exact (encoded ins bank randomness.1 Hi j Hj).
Qed.

Theorem scheduled_ticks_from_encoded code randomness s : scheduled s.1 code ->
  agrees (F.value n (Sched.ticks n (List.length code) randomness s).2)
    (P.run code (F.value n s.2)).
Proof.
  revert s. induction code as [|ins code IH]; intros [c bank] Hsched.
  - intros j Hj. reflexivity.
  - destruct Hsched as [Hi [Hstep Hrest]].
    set next := fn.interp (C.tick n) ((c,bank),(Sched.no_command,randomness (List.length code))).
    have Hcontrol : next.1 = fn.interp C.advance c.
    { rewrite /next C.tick_public_control. exact: Sched.next_without_commands. }
    have Hnext : scheduled next.1 code by rewrite Hcontrol.
    have Hvalues := IH next Hnext.
    have Hstep_values : agrees (F.value n next.2) (P.execute ins (F.value n bank)).
    { apply scheduled_step; [exact Hi|exact (Hstep n bank)]. }
    intros j Hj.
    change (F.value n (Sched.ticks n (List.length code) randomness next).2 j =
      P.run code (P.execute ins (F.value n bank)) j).
    transitivity (P.run code (F.value n next.2) j); [exact (Hvalues j Hj)|].
    exact (run_agrees code _ _ (scheduled_valid _ _ Hrest) Hstep_values j Hj).
Qed.

Lemma iteration_prefix_from_encoded i bank randomness : Nat.lt i 255 ->
  agrees (F.value n (Sched.ticks n 31 randomness
      (Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 0,bank)).2)
    (P.run (F.patched_iteration i) (F.value n bank)).
Proof.
  intro Hi. exact (scheduled_ticks_from_encoded (F.patched_iteration i) randomness
    (Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 0,bank) (iteration_scheduled i Hi)).
Qed.

Theorem iteration_ticks_from_encoded i bank randomness : Nat.lt i 255 ->
  agrees (F.value n (Sched.ticks n 32 randomness
      (Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 0,bank)).2)
    (F.collect_values (P.run (F.patched_iteration i) (F.value n bank))).
Proof.
  intro Hi.
  change (agrees (F.value n (Sched.ticks n (Nat.add 31 1) randomness
    (Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 0,bank)).2)
    (F.collect_values (P.run (F.patched_iteration i) (F.value n bank)))).
  rewrite ticks_add.
  set middle := Sched.ticks n 31 (fun j => randomness (Nat.add 1 j))
    (Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 0,bank).
  have Hcontrol : middle.1 = Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 31.
  { rewrite /middle Sched.ticks_public_control.
    exact (run_bit_prefix _ 31 (Nat.le_refl 31)). }
  have Hvalues := iteration_prefix_from_encoded i bank (fun j => randomness (Nat.add 1 j)) Hi.
  change (agrees (F.value n middle.2) (P.run (F.patched_iteration i) (F.value n bank))) in Hvalues.
  destruct middle as [c b]. simpl in Hcontrol. subst c.
  intros j Hj. have Hj' : is_true (ltn j C.groups) by apply/ltP.
  change (F.value n (fn.interp (C.tick n)
    ((Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 31,b),(Sched.no_command,randomness O))).2 j =
    F.collect_values (P.run (F.patched_iteration i) (F.value n bank)) j).
  rewrite (F.tick_prepare_value n _ (Ordinal Hj')) Sched.collect_edge
    (F.collect_reconstruct n b (Ordinal Hj')).
  exact (collect_agrees _ _ Hvalues j Hj).
Qed.

Theorem final_ticks_from_encoded index bank randomness :
  agrees (F.value n (Sched.ticks n 8 randomness (Sched.control 2 index 0,bank)).2)
    (P.run C.final_program (F.value n bank)).
Proof.
  exact (scheduled_ticks_from_encoded C.final_program randomness
    (Sched.control 2 index 0,bank) (final_scheduled index)).
Qed.
End Lift.

Theorem iteration_ticks n i bank randomness : Nat.lt i 255 ->
  agrees (F.value n (Sched.ticks n 32 randomness
      (Sched.control 1 (bits.of_Z 8 (Z.of_nat i)) 0,bank)).2)
    (F.collect_values (P.run (F.patched_iteration i) (F.value n bank))).
Proof. exact (iteration_ticks_from_encoded n (execute_encoded n) i bank randomness). Qed.

Theorem final_ticks n index bank randomness :
  agrees (F.value n (Sched.ticks n 8 randomness (Sched.control 2 index 0,bank)).2)
    (P.run C.final_program (F.value n bank)).
Proof. exact (final_ticks_from_encoded n (execute_encoded n) index bank randomness). Qed.

End MaskedControllerTickProgram.
Print Assumptions MaskedControllerTickProgram.decode_iteration.
Print Assumptions MaskedControllerTickProgram.prepare_iteration.
Print Assumptions MaskedControllerTickProgram.iteration_scheduled.
Print Assumptions MaskedControllerTickProgram.final_scheduled.
Print Assumptions MaskedControllerTickProgram.scheduled_ticks_from_encoded.
Print Assumptions MaskedControllerTickProgram.execute_encoded.
Print Assumptions MaskedControllerTickProgram.iteration_ticks.
Print Assumptions MaskedControllerTickProgram.final_ticks.
