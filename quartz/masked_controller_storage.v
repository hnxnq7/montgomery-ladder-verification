From Stdlib Require Import ZArith Bits List Vector Lia.
From quartz.lang Require Import Syntax transform.
From LadderQuartz Require Import masked_controller masked_arithmetic masked_bank hamming_weight packed_storage.
From Masking Require Import quartz_hw_encoding.

Set Default Proof Mode "Classic".
Open Scope Z_scope.

Module MaskedControllerStorage.
Module C := MaskedController.

Definition control_HW (c : Syntax.type.interp C.Control) : nat :=
  (RegisterHW.word_HW (fst c) +
    (RegisterHW.word_HW (fst (snd c)) + RegisterHW.word_HW (snd (snd c))))%nat.

Definition bank_HW n (bank : Syntax.type.interp (C.Bank n)) : nat :=
  List.fold_right (fun group acc => (RegisterHW.bank_HW group + acc)%nat)
    0%nat (Vector.to_list bank).

Definition state_HW n (s : Syntax.type.interp (C.State n)) : nat :=
  (control_HW (fst s) + bank_HW n (snd s))%nat.

Lemma groups_HW_exact n groups (bank : Vector.t (Vector.t (bits 255) (S n)) groups) :
  PackedStorage.storage_HW (Syntax.type.Array (Syntax.type.Array (Syntax.type.Bits 255) (S n)) groups) bank =
  List.fold_right (fun group acc => (RegisterHW.bank_HW group + acc)%nat)
    0%nat (Vector.to_list bank).
Proof.
  induction bank; cbn [PackedStorage.storage_HW PackedStorage.array_HW Vector.to_list List.fold_right].
  - reflexivity.
  - rewrite <- QuartzHWEncoding.array_HW_exact.
    apply f_equal2; [reflexivity|exact IHbank].
Qed.

Lemma state_plain n : PackedStorage.plain (C.State n).
Proof.
  unfold C.State, C.Control, C.Bank, MaskedBank.Bank, MaskedArithmetic.Shares, MaskedArithmetic.Word.
  cbn [PackedStorage.plain]. repeat split; lia.
Qed.

Theorem state_HW_storage n (s : Syntax.type.interp (C.State n)) :
  RegisterHW.word_HW (@transform.type.pack (C.State n) s) = state_HW n s.
Proof.
  rewrite PackedStorage.pack_HW by apply state_plain.
  change ((control_HW (fst s) + PackedStorage.storage_HW (C.Bank n) (snd s))%nat =
    (control_HW (fst s) + bank_HW n (snd s))%nat).
  apply f_equal2; [reflexivity|apply groups_HW_exact].
Qed.
Lemma control_HW_bound c : (control_HW c <= 16)%nat.
Proof.
  pose proof (RegisterHW.word_complement 3 (fst c) ltac:(lia)) as Hphase.
  pose proof (RegisterHW.word_complement 8 (fst (snd c)) ltac:(lia)) as Hindex.
  pose proof (RegisterHW.word_complement 5 (snd (snd c)) ltac:(lia)) as Hpc.
  unfold control_HW. cbn [Z.to_nat] in Hphase, Hindex, Hpc. lia.
Qed.

Lemma groups_HW_bound n groups (bank : Vector.t (Vector.t (bits 255) (S n)) groups) :
  (List.fold_right (fun group acc => (RegisterHW.bank_HW group + acc)%nat)
    0%nat (Vector.to_list bank) <= groups * ((S n) * 255))%nat.
Proof.
  induction bank as [|group count rest IH]; [simpl; lia|].
  change ((RegisterHW.bank_HW group +
    List.fold_right (fun group acc => (RegisterHW.bank_HW group + acc)%nat)
      0%nat (Vector.to_list rest)) <= (S count * ((S n) * 255)))%nat.
  pose proof (RegisterHW.bank_complement 255 (S n) group ltac:(lia)) as Hgroup.
  change ((RegisterHW.bank_HW group + RegisterHW.bank_HW (Vector.map Zmod.not group)) =
    (S n * 255))%nat in Hgroup.
  simpl Nat.mul. lia.
Qed.

Theorem state_HW_bound n (s : Syntax.type.interp (C.State n)) :
  (state_HW n s <= 16 + C.groups * ((S n) * 255))%nat.
Proof.
  unfold state_HW, bank_HW.
  apply Nat.add_le_mono.
  - apply control_HW_bound.
  - apply groups_HW_bound.
Qed.
Theorem tick_control_independent n
    (s1 s2 : Syntax.type.interp (C.State n))
    (c1 c2 : Syntax.type.interp C.Commands)
    (r1 r2 : Syntax.type.interp (C.Randomness n)) :
  fst s1 = fst s2 -> fst c1 = fst c2 -> fst (snd c1) = fst (snd c2) ->
  fst (fn.interp (C.tick n) (s1,(c1,r1))) = fst (fn.interp (C.tick n) (s2,(c2,r2))).
Proof.
  intros Hstate Hreset Hstart.
  rewrite !C.tick_public_control.
  change (fn.interp C.next_control (fst s1,(fst c1,fst (snd c1))) =
    fn.interp C.next_control (fst s2,(fst c2,fst (snd c2)))).
  apply f_equal. apply f_equal2; [exact Hstate|].
  apply f_equal2; assumption.
Qed.

Corollary tick_control_HW_independent n
    (s1 s2 : Syntax.type.interp (C.State n))
    (c1 c2 : Syntax.type.interp C.Commands)
    (r1 r2 : Syntax.type.interp (C.Randomness n)) :
  fst s1 = fst s2 -> fst c1 = fst c2 -> fst (snd c1) = fst (snd c2) ->
  control_HW (fst (fn.interp (C.tick n) (s1,(c1,r1)))) =
  control_HW (fst (fn.interp (C.tick n) (s2,(c2,r2)))).
Proof.
  intros Hstate Hreset Hstart. f_equal.
  now apply tick_control_independent.
Qed.
End MaskedControllerStorage.
Print Assumptions MaskedControllerStorage.state_HW_storage.
Print Assumptions MaskedControllerStorage.state_HW_bound.
Print Assumptions MaskedControllerStorage.tick_control_HW_independent.
