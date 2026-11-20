From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import masked_controller.
From Stdlib Require Import ZArith Bits Lia.

Module MaskedControllerSchedule.
Module C := MaskedController.
Local Open Scope Z_scope.

Definition control (phase : Z) (index : bits 8) (pc : Z) : type.interp C.Control :=
  (bits.of_Z 3 phase, (index, bits.of_Z 5 pc)).

Fixpoint run (edges : nat) (c : type.interp C.Control) : type.interp C.Control :=
  match edges with
  | O => c
  | S edges => run edges (fn.interp C.advance c)
  end.

Lemma run_add a b c : run (a+b) c = run b (run a c).
Proof. revert c. induction a; intro c; cbn [run Nat.add]; [reflexivity|apply IHa]. Qed.

(* The first 31 edges execute instructions; the last edge collects the coordinates. *)
Lemma iteration_shape i :
  run 32 (control 1 i 0) = fn.interp C.advance (control 1 i 31).
Proof. reflexivity. Qed.

Lemma final_swaps i : run 8 (control 2 i 0) = control 3 (bits.of_Z 8 254) 0.
Proof. reflexivity. Qed.

Lemma affine_pair_shape i :
  run 2 (control 3 i 0) = fn.interp C.advance (control 4 i 0).
Proof. reflexivity. Qed.

Lemma finish : run 1 (control 5 (bits.of_Z 8 0) 0) = control 6 (bits.of_Z 8 0) 0.
Proof. reflexivity. Qed.

Lemma index_predecessor i :
  Zmod.sub (bits.of_Z 8 (Z.of_nat (S i))) (bits.of_Z 8 1) = bits.of_Z 8 (Z.of_nat i).
Proof.
  rewrite <- Zmod.of_Z_sub. f_equal. lia.
Qed.

Lemma index_nonzero i : (i < 255)%nat ->
  Zmod.eqb (bits.of_Z 8 (Z.of_nat (S i))) (bits.of_Z 8 0) = false.
Proof.
  intro Hi. destruct (Zmod.eqb_spec (bits.of_Z 8 (Z.of_nat (S i))) (bits.of_Z 8 0)) as [H|H];
    [|reflexivity].
  apply (f_equal Zmod.unsigned) in H.
  rewrite !bits.unsigned_of_Z_small in H by (cbn; lia). lia.
Qed.

Lemma iteration_zero : run 32 (control 1 (bits.of_Z 8 0) 0) = control 2 (bits.of_Z 8 0) 0.
Proof. rewrite iteration_shape. reflexivity. Qed.

Lemma iteration_successor i : (i < 255)%nat ->
  run 32 (control 1 (bits.of_Z 8 (Z.of_nat (S i))) 0) =
  control 1 (bits.of_Z 8 (Z.of_nat i)) 0.
Proof.
  intro Hi. rewrite iteration_shape.
  change ((if Zmod.nonzero (Zmod.embed_bool
    (Zmod.eqb (bits.of_Z 8 (Z.of_nat (S i))) (bits.of_Z 8 0)))
    then control 2 (bits.of_Z 8 (Z.of_nat (S i))) 0
    else control 1 (Zmod.sub (bits.of_Z 8 (Z.of_nat (S i))) (bits.of_Z 8 1)) 0) =
    control 1 (bits.of_Z 8 (Z.of_nat i)) 0).
  rewrite Zmod.nonzero_bool, index_nonzero by exact Hi.
  rewrite index_predecessor. reflexivity.
Qed.

Lemma affine_zero : run 2 (control 3 (bits.of_Z 8 0) 0) = control 5 (bits.of_Z 8 0) 0.
Proof. rewrite affine_pair_shape. reflexivity. Qed.

Lemma affine_successor i : (i < 255)%nat ->
  run 2 (control 3 (bits.of_Z 8 (Z.of_nat (S i))) 0) =
  control 3 (bits.of_Z 8 (Z.of_nat i)) 0.
Proof.
  intro Hi. rewrite affine_pair_shape.
  change ((if Zmod.nonzero (Zmod.embed_bool
    (Zmod.eqb (bits.of_Z 8 (Z.of_nat (S i))) (bits.of_Z 8 0)))
    then control 5 (bits.of_Z 8 (Z.of_nat (S i))) 0
    else control 3 (Zmod.sub (bits.of_Z 8 (Z.of_nat (S i))) (bits.of_Z 8 1)) 0) =
    control 3 (bits.of_Z 8 (Z.of_nat i)) 0).
  rewrite Zmod.nonzero_bool, index_nonzero by exact Hi.
  rewrite index_predecessor. reflexivity.
Qed.

Lemma projective_count i : (i < 255)%nat ->
  run (32 * S i) (control 1 (bits.of_Z 8 (Z.of_nat i)) 0) = control 2 (bits.of_Z 8 0) 0.
Proof.
  induction i as [|i IH]; intro Hi; [exact iteration_zero|].
  replace (32 * S (S i))%nat with (32 + 32 * S i)%nat by lia.
  rewrite run_add, iteration_successor by lia. apply IH. lia.
Qed.

Lemma affine_count i : (i < 255)%nat ->
  run (2 * S i) (control 3 (bits.of_Z 8 (Z.of_nat i)) 0) = control 5 (bits.of_Z 8 0) 0.
Proof.
  induction i as [|i IH]; intro Hi; [exact affine_zero|].
  replace (2 * S (S i))%nat with (2 + 2 * S i)%nat by lia.
  rewrite run_add, affine_successor by lia. apply IH. lia.
Qed.

Definition start_control := control 1 (bits.of_Z 8 254) 0.
Definition done_control := control 6 (bits.of_Z 8 0) 0.
Definition work_edges : nat := (255 * 32 + 8 + 255 * 2 + 1)%nat.

Theorem complete_schedule : run work_edges start_control = done_control.
Proof.
  unfold work_edges, start_control, done_control.
  change (run (32 * 255 + (8 + (2 * 255 + 1))) (control 1 (bits.of_Z 8 254) 0) =
    control 6 (bits.of_Z 8 0) 0).
  pose proof (projective_count 254 ltac:(lia)) as Hp.
  change (run (32*255) (control 1 (bits.of_Z 8 254) 0) = control 2 (bits.of_Z 8 0) 0) in Hp.
  pose proof (affine_count 254 ltac:(lia)) as Ha.
  change (run (2*255) (control 3 (bits.of_Z 8 254) 0) = control 5 (bits.of_Z 8 0) 0) in Ha.
  rewrite run_add, Hp.
  rewrite run_add, final_swaps.
  rewrite run_add, Ha. exact finish.
Qed.

Lemma initialization :
  fn.interp C.next_control (type.default C.Control, (bits.of_Z 1 0,bits.of_Z 1 1)) = start_control.
Proof. reflexivity. Qed.

Lemma next_without_commands c :
  fn.interp C.next_control (c,(bits.of_Z 1 0,bits.of_Z 1 0)) = fn.interp C.advance c.
Proof.
  destruct c as [p [i pc]].
  change ((if Zmod.nonzero (Zmod.or
    (Zmod.embed_bool (Zmod.eqb p (bits.of_Z 3 0)))
    (Zmod.embed_bool (Zmod.eqb p (bits.of_Z 3 6))))
    then (p,(i,pc)) else fn.interp C.advance (p,(i,pc))) = fn.interp C.advance (p,(i,pc))).
  destruct (Zmod.eqb_spec p (bits.of_Z 3 0)) as [->|H0]; [reflexivity|].
  destruct (Zmod.eqb_spec p (bits.of_Z 3 6)) as [->|H6]; reflexivity.
Qed.

Definition no_command : type.interp C.Commands :=
  (bits.of_Z 1 0,(bits.of_Z 1 0,type.default C.Load)).

Fixpoint ticks n (edges : nat) (randomness : nat -> type.interp (C.Randomness n))
    (s : type.interp (C.State n)) : type.interp (C.State n) :=
  match edges with
  | O => s
  | S edges => ticks n edges randomness (fn.interp (C.tick n) (s,(no_command,randomness edges)))
  end.

Theorem ticks_public_control n edges randomness s :
  fst (ticks n edges randomness s) = run edges (fst s).
Proof.
  revert s. induction edges; intro s; cbn [ticks run]; [reflexivity|].
  rewrite IHedges, C.tick_public_control.
  change (run edges (fn.interp C.next_control (fst s,(bits.of_Z 1 0,bits.of_Z 1 0))) =
    run edges (fn.interp C.advance (fst s))).
  rewrite next_without_commands. reflexivity.
Qed.

Definition launch n (input : type.interp C.Load) (randomness : type.interp (C.Randomness n)) :=
  fn.interp (C.tick n)
    (C.initial_state n, ((bits.of_Z 1 0,(bits.of_Z 1 1,input)),randomness)).

Lemma launch_control n input randomness : fst (launch n input randomness) = start_control.
Proof. unfold launch. rewrite C.tick_public_control. exact initialization. Qed.

Theorem complete_tick_schedule n input first_randomness randomness :
  fst (ticks n work_edges randomness (launch n input first_randomness)) = done_control.
Proof. rewrite ticks_public_control, launch_control. exact complete_schedule. Qed.

Theorem complete_tick_ready n input first_randomness randomness :
  fn.interp (C.ready n) (ticks n work_edges randomness (launch n input first_randomness)) = bits.of_Z 1 1.
Proof.
  change (Zmod.embed_bool (Zmod.eqb
    (fst (fst (ticks n work_edges randomness (launch n input first_randomness)))) (bits.of_Z 3 6)) =
    bits.of_Z 1 1).
  rewrite complete_tick_schedule. reflexivity.
Qed.

Lemma done_control_holds edges : run edges done_control = done_control.
Proof. induction edges; [reflexivity|]. change (run edges done_control = done_control). exact IHedges. Qed.

Theorem done_ticks_public_control n edges randomness s :
  fst s = done_control -> fst (ticks n edges randomness s) = done_control.
Proof.
  intro H. rewrite ticks_public_control.
  exact (eq_trans (f_equal (run edges) H) (done_control_holds edges)).
Qed.

Theorem edge_count : (1 + work_edges)%nat = C.scheduled_edges.
Proof. reflexivity. Qed.

Theorem edge_count_value : (1 + work_edges)%nat = 8680%nat.
Proof. reflexivity. Qed.

(* An observed initial state adds one sample, not one execution edge. *)
Theorem initial_inclusive_samples : (1 + (1 + work_edges))%nat = 8681%nat.
Proof. reflexivity. Qed.

Lemma decode_bit_zero i :
  fn.interp C.decode (control 1 i 0) =
  (bits.of_Z 2 0,(bits.of_Z 9 (Zmod.unsigned i),(bits.of_Z 9 0,bits.of_Z 9 261))).
Proof. reflexivity. Qed.

Lemma decode_bit_rest i pc : Zmod.eqb pc (bits.of_Z 5 0) = false ->
  fn.interp C.decode (bits.of_Z 3 1,(i,pc)) = fn.interp (C.lookup_program 0 C.bit_program) pc.
Proof.
  intro H.
  change ((if Zmod.nonzero (Zmod.embed_bool (Zmod.eqb pc (bits.of_Z 5 0))) then
    (bits.of_Z 2 0,(bits.of_Z 9 (Zmod.unsigned i),(bits.of_Z 9 0,bits.of_Z 9 261))) else
    fn.interp (C.lookup_program 0 C.bit_program) pc) = fn.interp (C.lookup_program 0 C.bit_program) pc).
  rewrite Zmod.nonzero_bool, H. reflexivity.
Qed.

Lemma decode_final i pc :
  fn.interp C.decode (bits.of_Z 3 2,(i,pc)) = fn.interp (C.lookup_program 0 C.final_program) pc.
Proof. reflexivity. Qed.

Lemma decode_square i :
  fn.interp C.decode (control 3 i 0) = C.encode_instruction (C.Micro 3 263 263 263).
Proof. reflexivity. Qed.

Lemma decode_finish :
  fn.interp C.decode (control 5 (bits.of_Z 8 0) 0) = C.encode_instruction (C.Micro 3 256 263 263).
Proof. reflexivity. Qed.

Lemma collect_edge n i bank masks :
  fn.interp (C.prepare_bank n) ((control 1 i 31,bank),(no_command,masks)) = fn.interp (C.collect n) bank.
Proof. reflexivity. Qed.

End MaskedControllerSchedule.

Print Assumptions MaskedControllerSchedule.complete_schedule.
Print Assumptions MaskedControllerSchedule.complete_tick_schedule.
Print Assumptions MaskedControllerSchedule.complete_tick_ready.
