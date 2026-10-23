Require Import state_machine ladder_machine dual_circuit.
From Stdlib Require Import Lia Vectors.Vector Vectors.Fin.
From stdpp Require Import bitvector list.
Open Scope Z_scope.

Module ProcessorRefinement.
Module SM := StateMachine.
Module LM := LadderMachine.

Definition compile_instr (e : LM.instr) : SM.instr :=
  match e with
  | LM.Base e => SM.lift_instr e
  | LM.Copy rd rs => SM.Copy rd rs
  | LM.GetBit rd rs index => SM.GetBit rd rs index
  | LM.Xor rd ra rb => SM.Xor rd ra rb
  | LM.CSwap control ra rb => SM.CSwap control ra rb
  end.

Section Refinement.
  Variable n : N.
  Variable modulus : bv n.

  Definition registers_match (regs : Vector.t (bv n) 32) (values : list (bv n)) : Prop :=
    forall r, (r < length values)%nat -> SM.read_reg n regs r = read_register n values r.

  Lemma write_registers_match regs values rd value :
    (length values <= 32)%nat -> registers_match regs values ->
    registers_match (SM.write_reg n regs rd value) (write_register n values rd value).
  Proof.
    intros Hlen Hmatch r Hr. rewrite write_register_length in Hr.
    destruct (Nat.eq_dec r rd) as [-> | Hne].
    - rewrite SM.read_write_reg_same by lia.
      rewrite read_register_write_same by exact Hr. reflexivity.
    - rewrite SM.read_write_reg_diff by congruence.
      rewrite read_register_write_diff by congruence. apply Hmatch, Hr.
  Qed.

  Lemma write_register_self regs r : SM.write_reg n regs r (SM.read_reg n regs r) = regs.
  Proof.
    apply Vector.eq_nth_iff. intros j k Heq. subst k.
    destruct (Nat.eq_dec (proj1_sig (Fin.to_nat j)) r) as [Hsame | Hdiff].
    - rewrite SM.nth_write_reg_same by exact Hsame.
      unfold SM.read_reg. destruct (Fin.of_nat r 32) as [f | [extra Hextra]] eqn:Hindex.
      + assert (j = f) as ->.
        { apply Fin.to_nat_inj. rewrite Hsame. symmetry. apply SM.of_nat_inleft_to_nat, Hindex. }
        reflexivity.
      + exfalso. pose proof (proj2_sig (Fin.to_nat j)) as Hlt.
        rewrite Hsame, Hextra in Hlt. lia.
    - apply SM.nth_write_reg_diff, Hdiff.
  Qed.

  Lemma instruction_refines regs s e :
    (length (env n s) <= 32)%nat -> LM.in_bounds (length (env n s)) e ->
    registers_match regs (env n s) ->
    registers_match (SM.execute_regs n modulus regs (compile_instr e))
      (env n (LM.step n modulus s e).1).
  Proof.
    intros Hlen Hb Hmatch. unfold SM.execute_regs, compile_instr, LM.step, LM.interp_env.
    destruct e as [e | rd rs | rd rs index | rd ra rb | control ra rb];
      cbn [LM.in_bounds] in Hb; cbn [SM.exec_instr SM.exec_instr2 SM.apply_write fst env].
    - destruct e; cbn [SM.lift_instr SM.exec_instr SM.exec_instr2 SM.apply_write interp_instr fst env] in *.
      all: repeat match goal with
        | H : registers_match ?rs ?values |- context [SM.read_reg _ ?rs ?r] => rewrite (H r ltac:(lia))
        end.
      all: try (apply write_registers_match; assumption). exact Hmatch.
    - rewrite (Hmatch rs ltac:(lia)). apply write_registers_match; assumption.
    - rewrite (Hmatch rs ltac:(lia)). apply write_registers_match; assumption.
    - rewrite (Hmatch ra ltac:(lia)), (Hmatch rb ltac:(lia)). apply write_registers_match; assumption.
    - destruct (Z.eqb (bv_unsigned (SM.read_reg n regs control)) 1) eqn:Hswap.
      + rewrite (Hmatch control ltac:(lia)) in Hswap. rewrite Hswap.
        rewrite (Hmatch ra ltac:(lia)), (Hmatch rb ltac:(lia)).
        apply write_registers_match; [rewrite write_register_length; exact Hlen |].
        apply write_registers_match; assumption.
      + rewrite (Hmatch control ltac:(lia)) in Hswap. rewrite Hswap.
        rewrite write_register_self, write_register_self. exact Hmatch.
  Qed.

  Lemma run_refines regs s code :
    (length (env n s) <= 32)%nat -> Forall (LM.in_bounds (length (env n s))) code ->
    registers_match regs (env n s) ->
    registers_match (SM.run_code n modulus regs (List.map compile_instr code))
      (env n (LM.run n modulus s code).1).
  Proof.
    revert regs s. induction code as [| e code IH]; intros regs s Hlen Hbounds Hmatch.
    - exact Hmatch.
    - inversion Hbounds as [| ? ? He Hrest]; subst.
      pose proof (instruction_refines regs s e Hlen He Hmatch) as Hstep.
      pose proof (LM.step_preserves_length n modulus s e) as Hlength.
      cbn [List.map SM.run_code LM.run].
      destruct (LM.step n modulus s e) as [s' obs] eqn:Hstate. cbn in Hstep, Hlength.
      specialize (IH (SM.execute_regs n modulus regs (compile_instr e)) s'
        ltac:(rewrite Hlength; exact Hlen) ltac:(rewrite Hlength; exact Hrest) Hstep).
      destruct (LM.run n modulus s' code); exact IH.
  Qed.

  Definition initial_regs (x a24 scalar : bv n) : Vector.t (bv n) 32 :=
    Vector.of_list (env n (LM.initial_state n x a24 scalar) ++ List.repeat (bv_0 n) 4).

  Lemma initial_registers_match x a24 scalar :
    registers_match (initial_regs x a24 scalar) (env n (LM.initial_state n x a24 scalar)).
  Proof.
    intros r Hr. change (r < 28)%nat in Hr.
    do 28 (destruct r as [| r]; [reflexivity |]). lia.
  Qed.
End Refinement.

Definition bit_index_fits (e : LM.instr) : Prop :=
  match e with LM.GetBit _ _ index => (index < 256)%nat | _ => True end.

Lemma compile_in_bounds e :
  LM.in_bounds 28 e -> bit_index_fits e -> SM.instr_in_bounds (compile_instr e).
Proof.
  destruct e as [e | rd rs | rd rs index | rd ra rb | control ra rb];
    cbn [LM.in_bounds bit_index_fits compile_instr SM.instr_in_bounds]; try lia.
  destruct e; cbn [SM.lift_instr SM.instr_in_bounds]; lia.
Qed.

Lemma iteration_bit_indices index :
  (index < 256)%nat -> Forall bit_index_fits (LM.iteration index).
Proof.
  intro Hi. unfold LM.iteration, program. cbn [List.map List.app].
  repeat (apply List.Forall_cons; [cbn [bit_index_fits]; assumption || exact I |]). constructor.
Qed.

Lemma loop_bit_indices width :
  (width <= 256)%nat -> Forall bit_index_fits (LM.loop width).
Proof.
  induction width; intro Hw; cbn [LM.loop]; [constructor |].
  apply Forall_app. split; [apply iteration_bit_indices | apply IHwidth]; lia.
Qed.

Lemma projective_bit_indices width :
  (width <= 256)%nat -> Forall bit_index_fits (LM.projective_program width).
Proof.
  intro Hw. unfold LM.projective_program, LM.ladder_code. rewrite !Forall_app.
  repeat split; try (repeat constructor).
  apply loop_bit_indices, Hw.
Qed.

Lemma power_bit_indices exponent : Forall bit_index_fits (LM.power_code exponent).
Proof.
  induction exponent; cbn [LM.power_code]; rewrite ?Forall_app; repeat split;
    try assumption; repeat constructor.
Qed.

Lemma affine_bit_indices width exponent :
  (width <= 256)%nat -> Forall bit_index_fits (LM.affine_program width exponent).
Proof.
  intro Hw. unfold LM.affine_program, LM.affine_code. rewrite !Forall_app.
  split; [apply projective_bit_indices, Hw |].
  split; [apply power_bit_indices | repeat constructor].
Qed.

Lemma compiled_in_bounds code :
  Forall (LM.in_bounds 28) code -> Forall bit_index_fits code ->
  Forall SM.instr_in_bounds (List.map compile_instr code).
Proof.
  intros Hb. induction Hb; intro Hi; simpl; [constructor |].
  inversion Hi; subst. constructor; [apply compile_in_bounds; assumption | auto].
Qed.

Section Execution.
  Variable n : N.
  Variable modulus : bv n.

  Definition encoded_program (code : list LM.instr) : list (bv n) :=
    List.map (SM.encode_instr n) (List.map compile_instr code).

  Definition run_program (regs : Vector.t (bv n) 32) (code : list LM.instr) : SM.state n :=
    SM.run_ticks n modulus (SM.mk_processor_state n (encoded_program code) regs) (3 * length code).

  Theorem run_program_refines regs s code :
    (21 <= n)%N -> length (env n s) = 28%nat ->
    Forall (LM.in_bounds 28) code -> Forall bit_index_fits code ->
    Z.of_nat (length code) < 2 ^ Z.of_N n -> registers_match n regs (env n s) ->
    registers_match n (SM.Regs n (run_program regs code)) (env n (LM.run n modulus s code).1).
  Proof.
    intros Hw Hlen Hb Hi Hcap Hmatch.
    pose proof (SM.run_code_correct n modulus regs (List.map compile_instr code) Hw
      (compiled_in_bounds code Hb Hi) ltac:(rewrite List.length_map; exact Hcap)) as Hrun.
    rewrite List.length_map in Hrun. destruct Hrun as [Hregs _].
    unfold run_program, encoded_program. rewrite Hregs.
    apply run_refines; [rewrite Hlen; lia | rewrite Hlen; exact Hb | exact Hmatch].
  Qed.

  Theorem run_program_boundary regs code :
    (21 <= n)%N -> Forall (LM.in_bounds 28) code -> Forall bit_index_fits code ->
    Z.of_nat (length code) < 2 ^ Z.of_N n ->
    SM.pc n (run_program regs code) = Z_to_bv n (Z.of_nat (length code)) /\
    SM.Stage n (run_program regs code) = SM.Fetch.
  Proof.
    intros Hw Hb Hi Hcap.
    pose proof (SM.run_code_correct n modulus regs (List.map compile_instr code) Hw
      (compiled_in_bounds code Hb Hi) ltac:(rewrite List.length_map; exact Hcap)) as Hrun.
    rewrite List.length_map in Hrun. exact (proj2 Hrun).
  Qed.

  Definition projective_output (s : SM.state n) : Z * Z :=
    (bv_unsigned (SM.read_reg n (SM.Regs n s) 1%nat), bv_unsigned (SM.read_reg n (SM.Regs n s) 2%nat)).

  Definition affine_output (s : SM.state n) : Z :=
    bv_unsigned (SM.read_reg n (SM.Regs n s) 1%nat).

  Theorem projective_program_correct x a24 scalar width :
    (21 <= n)%N -> (width <= 256)%nat -> 0 < bv_unsigned modulus ->
    Z.of_nat (length (LM.projective_program width)) < 2 ^ Z.of_N n ->
    projective_output (run_program (initial_regs n x a24 scalar) (LM.projective_program width)) =
    ladder_math.MontLadderCSwap (bv_unsigned modulus) (bv_unsigned a24) width
      (bv_unsigned x) (bv_unsigned scalar).
  Proof.
    intros Hn Hw Hp Hcap.
    pose proof (run_program_refines (initial_regs n x a24 scalar) (LM.initial_state n x a24 scalar)
      (LM.projective_program width) Hn eq_refl (LM.projective_program_in_bounds width)
      (projective_bit_indices width Hw) Hcap (initial_registers_match n x a24 scalar)) as Hr.
    unfold projective_output. rewrite !Hr by (rewrite LM.run_preserves_length, LM.initial_state_length; lia).
    apply LM.projective_program_correct, Hp.
  Qed.

  Theorem affine_program_correct x a24 scalar width exponent :
    (21 <= n)%N -> (width <= 256)%nat -> 0 < bv_unsigned modulus ->
    Z.of_nat (length (LM.affine_program width exponent)) < 2 ^ Z.of_N n ->
    affine_output (run_program (initial_regs n x a24 scalar) (LM.affine_program width exponent)) =
    let '(X, Zc) := ladder_math.MontLadderCSwap (bv_unsigned modulus) (bv_unsigned a24) width
      (bv_unsigned x) (bv_unsigned scalar) in
    (X * Zc ^ Z.pos exponent) mod bv_unsigned modulus.
  Proof.
    intros Hn Hw Hp Hcap.
    pose proof (run_program_refines (initial_regs n x a24 scalar) (LM.initial_state n x a24 scalar)
      (LM.affine_program width exponent) Hn eq_refl (LM.affine_program_in_bounds width exponent)
      (affine_bit_indices width exponent Hw) Hcap (initial_registers_match n x a24 scalar)) as Hr.
    unfold affine_output. rewrite Hr by (rewrite LM.run_preserves_length, LM.initial_state_length; lia).
    apply LM.affine_program_correct, Hp.
  Qed.
End Execution.
End ProcessorRefinement.
