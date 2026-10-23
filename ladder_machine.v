Require Import ladder_math dual_circuit.
From stdpp Require Import bitvector list.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Module LadderMachine.

(* Instruction-level ladder, connected to processor cycles in processor_refinement.v. *)
Inductive instr :=
  | Base (e : dual_circuit.instr)
  | Copy (rd rs : nat)
  | GetBit (rd rs index : nat)
  | Xor (rd rs1 rs2 : nat)
  | CSwap (control ra rb : nat).

Section Machine.
  Variable n : N.
  Variable p : bv n.

  Definition bit_value (b : bool) : bv n :=
    Z_to_bv n (Z.b2z b).

  Definition interp_env (regs : Env n) (e : instr) : Env n * list (Observation n) :=
    let get := read_register n regs in
    match e with
    | Base e => interp_instr n p regs e
    | Copy rd rs => (write_register n regs rd (get rs), [])
    | GetBit rd rs index => (write_register n regs rd (bit_value (Z.testbit (bv_unsigned (get rs)) (Z.of_nat index))), [])
    | Xor rd rs1 rs2 => (write_register n regs rd (bv_xor (get rs1) (get rs2)), [])
    | CSwap control ra rb =>
        if Z.eqb (bv_unsigned (get control)) 1 then
          (write_register n (write_register n regs ra (get rb)) rb (get ra), [])
        else (regs, [])
    end.

  (* Both swap operands are read before either write; complements update atomically. *)
  Definition step (s : state n) (e : instr) : state n * list (Observation n) :=
    let '(regs, obs) := interp_env (env n s) e in
    ({| env := regs; denv := map bv_not regs |}, obs).

  Fixpoint run (s : state n) (code : list instr) : state n * list (Observation n) :=
    match code with
    | [] => (s, [])
    | e :: rest =>
        let '(s', obs) := step s e in
        let '(final, later) := run s' rest in
        (final, obs ++ later)
    end.

  Fixpoint hw_trace (s : state n) (code : list instr) : list nat :=
    num_1s_in_state n s ::
      match code with
      | [] => []
      | e :: rest => hw_trace (step s e).1 rest
      end.

  Definition no_observe (e : instr) : Prop :=
    match e with Base (Observe _) => False | _ => True end.

  Definition in_bounds (registers : nat) (e : instr) : Prop :=
    match e with
    | Base e =>
        match e with
        | IAdd rd ra rb | ISub rd ra rb | IMul rd ra rb => (rd < registers /\ ra < registers /\ rb < registers)%nat
        | Observe r => (r < registers)%nat
        end
    | Copy rd rs | GetBit rd rs _ => (rd < registers /\ rs < registers)%nat
    | Xor rd ra rb => (rd < registers /\ ra < registers /\ rb < registers)%nat
    | CSwap control ra rb => (control < registers /\ ra < registers /\ rb < registers)%nat
    end.

  Definition writes (e : instr) : list nat :=
    match e with
    | Base e => match e with IAdd rd _ _ | ISub rd _ _ | IMul rd _ _ => [rd] | Observe _ => [] end
    | Copy rd _ | GetBit rd _ _ | Xor rd _ _ => [rd]
    | CSwap _ ra rb => [ra; rb]
    end.

  Lemma step_read_other s e r : ~ In r (writes e) -> read_register n (env n (step s e).1) r = read_register n (env n s) r.
  Proof.
    intro Hr. unfold step, interp_env. destruct e; cbn [writes] in Hr; cbn.
    - destruct (interp_instr n p (env n s) e) as [regs obs] eqn:Hstep. cbn.
      pose proof (interp_instr_read_other n p (env n s) e r) as H. rewrite Hstep in H. cbn in H.
      apply H. destruct e; cbn in *; intuition congruence.
    - apply read_register_write_diff. cbn in Hr. intuition congruence.
    - apply read_register_write_diff. cbn in Hr. intuition congruence.
    - apply read_register_write_diff. cbn in Hr. intuition congruence.
    - destruct (Z.eqb _ _); cbn; [| reflexivity].
      change (read_register n (write_register n (write_register n (env n s) ra (read_register n (env n s) rb)) rb (read_register n (env n s) ra)) r = read_register n (env n s) r).
      rewrite !read_register_write_diff by (cbn in Hr; intuition congruence). reflexivity.
  Qed.

  Lemma run_read_other s code r : Forall (fun e => ~ In r (writes e)) code -> read_register n (env n (run s code).1) r = read_register n (env n s) r.
  Proof.
    intro Hcode. revert s. induction Hcode as [| e code He Hcode IH]; intro s; cbn [run]; [reflexivity |].
    pose proof (step_read_other s e r He) as H.
    destruct (step s e) as [s' obs] eqn:Hstep. cbn in H.
    specialize (IH s'). destruct (run s' code); cbn in *. congruence.
  Qed.

  Lemma step_preserves_length s e : length (env n (step s e).1) = length (env n s).
  Proof.
    unfold step, interp_env. destruct e; cbn.
    - destruct (interp_instr n p (env n s) e) as [regs obs] eqn:Hstep. cbn.
      pose proof (interp_instr_preserves_length n p (env n s) e) as H. rewrite Hstep in H. exact H.
    - apply write_register_length.
    - apply write_register_length.
    - apply write_register_length.
    - destruct (Z.eqb _ _); cbn; rewrite ?write_register_length; reflexivity.
  Qed.

  Lemma step_preserves_valid s e : valid_state n (step s e).1.
  Proof.
    unfold step. destruct (interp_env (env n s) e). reflexivity.
  Qed.

  Lemma run_preserves_valid s code : valid_state n s -> valid_state n (run s code).1.
  Proof.
    revert s. induction code as [| e code IH]; intros s Hvalid; cbn [run].
    - exact Hvalid.
    - destruct (step s e) as [s' obs] eqn:Hstep.
      pose proof (step_preserves_valid s e) as H. rewrite Hstep in H. cbn in H.
      specialize (IH s' H). destruct (run s' code); exact IH.
  Qed.

  Lemma run_preserves_length s code : length (env n (run s code).1) = length (env n s).
  Proof.
    revert s. induction code as [| e code IH]; intro s; cbn [run]; [reflexivity |].
    destruct (step s e) as [s' obs] eqn:Hstep.
    pose proof (step_preserves_length s e) as H. rewrite Hstep in H. cbn in H.
    specialize (IH s'). destruct (run s' code); cbn in *. congruence.
  Qed.

  Theorem hw_trace_constant s code :
    valid_state n s ->
    hw_trace s code = repeat (length (env n s) * N.to_nat n)%nat (S (length code)).
  Proof.
    revert s. induction code as [| e code IH]; intros s Hvalid; cbn [hw_trace length repeat].
    - rewrite valid_state_num_1s by exact Hvalid. reflexivity.
    - rewrite valid_state_num_1s by exact Hvalid.
      rewrite IH by apply step_preserves_valid. rewrite step_preserves_length. reflexivity.
  Qed.

  Lemma run_no_observe s code : Forall no_observe code -> (run s code).2 = [].
  Proof.
    intro Hcode. revert s. induction Hcode as [| e code He Hcode IH]; intro s; cbn [run]; [reflexivity |].
    assert (Hobs : (step s e).2 = []).
    { unfold step, interp_env. destruct e; cbn in *; try reflexivity.
      - destruct e; cbn in *; tauto.
      - destruct (Z.eqb _ _); reflexivity. }
    destruct (step s e) as [s' obs]. cbn in Hobs. subst obs.
    specialize (IH s'). destruct (run s' code); exact IH.
  Qed.

  Lemma bit_value_unsigned b : (0 < bv_unsigned p)%Z -> bv_unsigned (bit_value b) = Z.b2z b.
  Proof.
    intro Hp. unfold bit_value. apply Z_to_bv_small.
    pose proof (bv_unsigned_in_range n p). destruct b; cbn; lia.
  Qed.

  Lemma bit_value_xor b c : (0 < bv_unsigned p)%Z -> bv_xor (bit_value b) (bit_value c) = bit_value (xorb b c).
  Proof.
    intro Hp. apply bv_eq. rewrite bv_xor_unsigned, !bit_value_unsigned by exact Hp.
    destruct b, c; reflexivity.
  Qed.

  Lemma cswap_correct regs control ra rb b :
    (0 < bv_unsigned p)%Z ->
    read_register n regs control = bit_value b ->
    interp_env regs (CSwap control ra rb) =
    (if b then write_register n (write_register n regs ra (read_register n regs rb)) rb (read_register n regs ra)
     else regs, []).
  Proof.
    intros Hp Hcontrol. unfold interp_env. rewrite Hcontrol, bit_value_unsigned by exact Hp.
    destruct b; reflexivity.
  Qed.

  (* Registers 0..23 retain the original layout; 24..27 hold scalar, previous bit, current bit, and swap bit. *)
  Definition iteration (index : nat) : list instr :=
    [GetBit 26 24 index; Xor 27 26 25; CSwap 27 1 3; CSwap 27 2 4] ++ map Base program ++
    [Copy 1 19; Copy 2 23; Copy 3 16; Copy 4 18; Copy 25 26].

  Definition point_regs (s : state n) : Z * Z * Z * Z :=
    let get := fun r => bv_unsigned (read_register n (env n s) r) in
    (get 1%nat, get 2%nat, get 3%nat, get 4%nat).

  Lemma iteration_length index : length (iteration index) = 27%nat.
  Proof. reflexivity. Qed.

  Lemma iteration_in_bounds index : Forall (in_bounds 28) (iteration index).
  Proof. unfold iteration, program. repeat constructor; cbn; lia. Qed.

  Lemma iteration_no_observe index : Forall no_observe (iteration index).
  Proof. unfold iteration, program. repeat constructor. Qed.

  Lemma iteration_preserves_inputs s index r : r = 0%nat \/ r = 5%nat \/ r = 24%nat -> read_register n (env n (run s (iteration index)).1) r = read_register n (env n s) r.
  Proof.
    intro Hr. apply run_read_other. unfold iteration, program.
    repeat constructor; cbn; intuition lia.
  Qed.

  Theorem iteration_secure s index :
    valid_state n s ->
    hw_trace s (iteration index) = repeat (length (env n s) * N.to_nat n)%nat 28 /\
    (run s (iteration index)).2 = [] /\
    valid_state n (run s (iteration index)).1.
  Proof.
    intro Hvalid. split.
    - rewrite hw_trace_constant by exact Hvalid. reflexivity.
    - split; [apply run_no_observe, iteration_no_observe | apply run_preserves_valid; exact Hvalid].
  Qed.

  Local Lemma run_cons s e code : run s (e :: code) = let '(s', obs) := step s e in let '(final, later) := run s' code in (final, obs ++ later).
  Proof. reflexivity. Qed.

  Theorem iteration_correct s index previous :
    (0 < bv_unsigned p)%Z ->
    (28 <= length (env n s))%nat ->
    bv_unsigned (read_register n (env n s) 25%nat) = Z.b2z previous ->
    let get := fun r => bv_unsigned (read_register n (env n s) r) in
    let result := MontLadderCSwap_step (bv_unsigned p) (get 5%nat) (get 0%nat)
      (bit_i (get 24%nat) index) previous (point_regs s) in
    let final := (run s (iteration index)).1 in
    (point_regs final, bv_unsigned (read_register n (env n final) 25%nat)) = (result.1, Z.b2z result.2).
  Proof.
    intros Hp Hlen Hprevious.
    assert (Hprev : read_register n (env n s) 25%nat = bit_value previous).
    { apply bv_eq. rewrite bit_value_unsigned by exact Hp. exact Hprevious. }
    destruct (bit_i (bv_unsigned (read_register n (env n s) 24%nat)) index) eqn:Hbit; destruct previous;
      destruct s as [regs duals]; cbn [env] in Hlen;
      do 28 (destruct regs as [| ? regs]; [cbn in Hlen; lia |]).
    all: cbn [env read_register List.nth bit_i] in Hprev, Hbit; subst.
    all: unfold bit_i in Hbit.
    all: cbv beta iota zeta delta [iteration program map app].
    all: repeat (
      rewrite run_cons;
      cbv beta iota zeta delta [step interp_env interp_instr env read_register write_register List.nth list_insert insert fst snd app];
      rewrite ?Hbit;
      rewrite ?bit_value_xor by exact Hp;
      rewrite ?bit_value_unsigned by exact Hp;
      cbn [Z.b2z xorb Z.eqb Pos.eqb]).
    all: cbv beta iota zeta delta [run point_regs env read_register List.nth fst snd].
    all: rewrite ?bit_value_unsigned by exact Hp.
    all: repeat first [rewrite fadd_bv_correct by exact Hp | rewrite fsub_bv_correct by exact Hp | rewrite fmul_bv_correct by exact Hp].
    all: unfold MontLadderCSwap_step, ladder_math.CSwap, LadderStep, fadd, fsub, fsq, fmul, bit_i; rewrite ?Hbit; reflexivity.
  Qed.

  Lemma run_app s left right : run s (left ++ right) = let '(middle, before) := run s left in let '(final, after) := run middle right in (final, before ++ after).
  Proof.
    revert s. induction left as [| e left IH]; intro s; cbn [run app].
    - destruct (run s right); reflexivity.
    - destruct (step s e) as [s' obs]. rewrite IH.
      destruct (run s' left) as [middle before]. destruct (run middle right) as [final after].
      cbn. rewrite app_assoc. reflexivity.
  Qed.

  Lemma run_app_state s left right : (run s (left ++ right)).1 = (run (run s left).1 right).1.
  Proof.
    rewrite run_app. destruct (run s left) as [middle before]. cbn. destruct (run middle right); reflexivity.
  Qed.

  (* The instruction list depends on the public width, never on the scalar. *)
  Fixpoint loop (width : nat) : list instr :=
    match width with
    | O => []
    | S index => iteration index ++ loop index
    end.

  Definition final_swap : list instr :=
    [CSwap 25 1 3; CSwap 25 2 4].

  Definition ladder_code (width : nat) : list instr :=
    loop width ++ final_swap.

  Definition projective_output (s : state n) : Z * Z :=
    let '(x, z, _, _) := point_regs s in (x, z).

  Lemma loop_length width : length (loop width) = (27 * width)%nat.
  Proof.
    induction width; cbn [loop]; [reflexivity |]. rewrite List.length_app, iteration_length, IHwidth. lia.
  Qed.

  Lemma loop_in_bounds width : Forall (in_bounds 28) (loop width).
  Proof.
    induction width; cbn [loop]; [constructor |]. apply Forall_app. split; [apply iteration_in_bounds | assumption].
  Qed.

  Lemma loop_no_observe width : Forall no_observe (loop width).
  Proof.
    induction width; cbn [loop]; [constructor |]. apply Forall_app. split; [apply iteration_no_observe | assumption].
  Qed.

  Lemma loop_preserves_inputs s width r : r = 0%nat \/ r = 5%nat \/ r = 24%nat -> read_register n (env n (run s (loop width)).1) r = read_register n (env n s) r.
  Proof.
    intro Hr. revert s. induction width; intro s; cbn [loop]; [reflexivity |].
    rewrite run_app_state, IHwidth. apply iteration_preserves_inputs. exact Hr.
  Qed.

  Theorem loop_correct s width previous :
    (0 < bv_unsigned p)%Z ->
    (28 <= length (env n s))%nat ->
    bv_unsigned (read_register n (env n s) 25%nat) = Z.b2z previous ->
    let get := fun r => bv_unsigned (read_register n (env n s) r) in
    let result := MontLadderCSwap_rec (bv_unsigned p) (get 5%nat) width
      (get 0%nat) (get 24%nat) (point_regs s, previous) in
    let final := (run s (loop width)).1 in
    (point_regs final, bv_unsigned (read_register n (env n final) 25%nat)) = (result.1, Z.b2z result.2).
  Proof.
    revert s previous. induction width as [| index IH]; intros s previous Hp Hlen Hprev.
    - exact (f_equal (fun v => (point_regs s, v)) Hprev).
    - cbv beta zeta. cbn [loop]. rewrite run_app_state.
      pose proof (iteration_correct s index previous Hp Hlen Hprev) as Hstep.
      cbv beta zeta in Hstep.
      destruct (MontLadderCSwap_step (bv_unsigned p) (bv_unsigned (read_register n (env n s) 5%nat)) (bv_unsigned (read_register n (env n s) 0%nat)) (bit_i (bv_unsigned (read_register n (env n s) 24%nat)) index) previous (point_regs s)) as [coords next] eqn:Hmath.
      pose proof (f_equal fst Hstep) as Hcoords.
      pose proof (f_equal snd Hstep) as Hnext.
      change (point_regs (run s (iteration index)).1 = coords) in Hcoords.
      change (bv_unsigned (read_register n (env n (run s (iteration index)).1) 25%nat) = Z.b2z next) in Hnext.
      specialize (IH (run s (iteration index)).1 next Hp).
      rewrite run_preserves_length in IH. specialize (IH Hlen Hnext).
      cbv beta zeta in IH.
      rewrite !iteration_preserves_inputs in IH by auto.
      rewrite Hcoords in IH.
      cbn [MontLadderCSwap_rec]. rewrite Hmath. exact IH.
  Qed.

  Lemma final_swap_correct s previous :
    (0 < bv_unsigned p)%Z ->
    (28 <= length (env n s))%nat ->
    bv_unsigned (read_register n (env n s) 25%nat) = Z.b2z previous ->
    point_regs (run s final_swap).1 = norm_regs (point_regs s) previous.
  Proof.
    intros Hp Hlen Hprevious.
    assert (Hprev : read_register n (env n s) 25%nat = bit_value previous).
    { apply bv_eq. rewrite bit_value_unsigned by exact Hp. exact Hprevious. }
    destruct previous; destruct s as [regs duals]; cbn [env] in Hlen;
      do 28 (destruct regs as [| ? regs]; [cbn in Hlen; lia |]).
    all: cbn [env read_register List.nth] in Hprev; subst.
    all: unfold final_swap.
    all: repeat (rewrite run_cons; cbv beta iota zeta delta [step interp_env env read_register write_register List.nth list_insert insert fst snd app]; rewrite ?bit_value_unsigned by exact Hp; cbn [Z.b2z Z.eqb Pos.eqb]).
    all: cbv beta iota zeta delta [run point_regs env read_register List.nth fst snd norm_regs swap_regs]; reflexivity.
  Qed.

  Theorem ladder_code_correct s width :
    (0 < bv_unsigned p)%Z ->
    (28 <= length (env n s))%nat ->
    bv_unsigned (read_register n (env n s) 25%nat) = 0 ->
    point_regs s = (1, 0, bv_unsigned (read_register n (env n s) 0%nat), 1) ->
    projective_output (run s (ladder_code width)).1 =
    MontLadderCSwap (bv_unsigned p) (bv_unsigned (read_register n (env n s) 5%nat)) width
      (bv_unsigned (read_register n (env n s) 0%nat)) (bv_unsigned (read_register n (env n s) 24%nat)).
  Proof.
    intros Hp Hlen Hprev Hinit.
    pose proof (loop_correct s width false Hp Hlen Hprev) as Hloop.
    cbv beta zeta in Hloop. rewrite Hinit in Hloop.
    destruct (MontLadderCSwap_rec (bv_unsigned p) (bv_unsigned (read_register n (env n s) 5%nat)) width (bv_unsigned (read_register n (env n s) 0%nat)) (bv_unsigned (read_register n (env n s) 24%nat)) ((1, 0, bv_unsigned (read_register n (env n s) 0%nat), 1), false)) as [coords previous] eqn:Hmath.
    pose proof (f_equal fst Hloop) as Hcoords.
    pose proof (f_equal snd Hloop) as Hprevious.
    change (point_regs (run s (loop width)).1 = coords) in Hcoords.
    change (bv_unsigned (read_register n (env n (run s (loop width)).1) 25%nat) = Z.b2z previous) in Hprevious.
    unfold ladder_code. rewrite run_app_state. unfold projective_output.
    rewrite final_swap_correct with (previous := previous) by (try assumption; rewrite run_preserves_length; exact Hlen).
    rewrite Hcoords. unfold MontLadderCSwap. rewrite Hmath.
    destruct coords as [[[x2 z2] x3] z3]. destruct previous; reflexivity.
  Qed.

  (* Scratch slots 26 and 27 initially supply public zero and one constants. *)
  Definition initial_state (x a24 scalar : bv n) : state n :=
    let regs := [x] ++ repeat (bv_0 n) 4 ++ [a24] ++ repeat (bv_0 n) 18 ++ [scalar; bv_0 n; bv_0 n; bit_value true] in
    {| env := regs; denv := map bv_not regs |}.

  Definition initialize : list instr :=
    [Copy 1 27; Copy 2 26; Copy 3 0; Copy 4 27; Copy 25 26].

  Definition projective_program (width : nat) : list instr :=
    initialize ++ ladder_code width.

  Lemma initial_state_valid x a24 scalar : valid_state n (initial_state x a24 scalar).
  Proof. reflexivity. Qed.

  Lemma initial_state_length x a24 scalar : length (env n (initial_state x a24 scalar)) = 28%nat.
  Proof. reflexivity. Qed.

  Lemma initialize_correct x a24 scalar :
    (0 < bv_unsigned p)%Z ->
    let ready := (run (initial_state x a24 scalar) initialize).1 in
    point_regs ready = (1, 0, bv_unsigned x, 1) /\
    bv_unsigned (read_register n (env n ready) 25%nat) = 0 /\
    read_register n (env n ready) 0%nat = x /\
    read_register n (env n ready) 5%nat = a24 /\
    read_register n (env n ready) 24%nat = scalar.
  Proof.
    intro Hp.
    cbv beta iota zeta delta [initial_state initialize run step interp_env point_regs env read_register write_register List.nth list_insert insert fst snd app repeat].
    rewrite bit_value_unsigned by exact Hp. rewrite bv_0_unsigned. repeat split; reflexivity.
  Qed.

  Lemma projective_program_length width : length (projective_program width) = (27 * width + 7)%nat.
  Proof.
    unfold projective_program, ladder_code. rewrite !List.length_app, loop_length. cbn [initialize final_swap length]. lia.
  Qed.

  Lemma projective_program_in_bounds width : Forall (in_bounds 28) (projective_program width).
  Proof.
    unfold projective_program, ladder_code. rewrite !Forall_app.
    split; [unfold initialize; repeat constructor; cbn; lia |].
    split; [apply loop_in_bounds | unfold final_swap; repeat constructor; cbn; lia].
  Qed.

  Lemma projective_program_no_observe width : Forall no_observe (projective_program width).
  Proof.
    unfold projective_program, ladder_code. rewrite !Forall_app.
    split; [unfold initialize; repeat constructor |].
    split; [apply loop_no_observe | unfold final_swap; repeat constructor].
  Qed.

  Theorem projective_program_correct x a24 scalar width :
    (0 < bv_unsigned p)%Z ->
    projective_output (run (initial_state x a24 scalar) (projective_program width)).1 =
    MontLadderCSwap (bv_unsigned p) (bv_unsigned a24) width (bv_unsigned x) (bv_unsigned scalar).
  Proof.
    intro Hp. pose proof (initialize_correct x a24 scalar Hp) as Hinit.
    destruct Hinit as [Hpoints [Hprev [Hx [Ha Hscalar]]]].
    unfold projective_program. rewrite run_app_state.
    rewrite ladder_code_correct.
    - rewrite Hx, Ha, Hscalar. reflexivity.
    - exact Hp.
    - rewrite run_preserves_length, initial_state_length. lia.
    - exact Hprev.
    - rewrite Hx. exact Hpoints.
  Qed.

  Theorem projective_program_secure x a24 scalar width :
    hw_trace (initial_state x a24 scalar) (projective_program width) =
      repeat (28 * N.to_nat n)%nat (27 * width + 8) /\
    (run (initial_state x a24 scalar) (projective_program width)).2 = [] /\
    valid_state n (run (initial_state x a24 scalar) (projective_program width)).1.
  Proof.
    split.
    - rewrite hw_trace_constant by apply initial_state_valid.
      rewrite initial_state_length, projective_program_length. f_equal. lia.
    - split.
      + apply run_no_observe, projective_program_no_observe.
      + apply run_preserves_valid, initial_state_valid.
  Qed.

End Machine.

Section Affine.
  Variable n : N.
  Variable p : bv n.
  Local Open Scope nat_scope.

  (* Positive exponents start at Z; register 6 is free after the ladder loop. *)
  Fixpoint power_code (exponent : positive) : list instr :=
    match exponent with
    | xH => [Copy 6 2]
    | xO e => power_code e ++ [Base (IMul 6 6 6)]
    | xI e => power_code e ++ [Base (IMul 6 6 6); Base (IMul 6 6 2)]
    end.

  Definition affine_code (exponent : positive) : list instr :=
    power_code exponent ++ [Base (IMul 1 1 6)].

  Definition affine_program (width : nat) (exponent : positive) : list instr :=
    projective_program width ++ affine_code exponent.

  Definition affine_result (s : state n) : Z :=
    bv_unsigned (read_register n (env n s) 1%nat).

  Local Open Scope Z_scope.

  Local Lemma run_cons_state s e code : (run n p s (e :: code)).1 = (run n p (step n p s e).1 code).1.
  Proof.
    cbn [run]. destruct (step n p s e) as [next obs]. cbn [fst]. destruct (run n p next code). reflexivity.
  Qed.

  Local Lemma mul_step_value s rd ra rb :
    0 < bv_unsigned p ->
    (rd < length (env n s))%nat ->
    bv_unsigned (read_register n (env n (step n p s (Base (IMul rd ra rb))).1) rd) =
    (bv_unsigned (read_register n (env n s) ra) * bv_unsigned (read_register n (env n s) rb)) mod bv_unsigned p.
  Proof.
    intros Hp Hlen. cbn [step interp_env interp_instr fst env].
    rewrite read_register_write_same by exact Hlen.
    apply fmul_bv_correct. exact Hp.
  Qed.

  Lemma power_code_preserves s exponent r : r <> 6%nat ->
    read_register n (env n (run n p s (power_code exponent)).1) r = read_register n (env n s) r.
  Proof.
    intro Hr. apply run_read_other. induction exponent; cbn [power_code]; rewrite ?Forall_app; repeat split; try assumption; repeat constructor; cbn; intuition congruence.
  Qed.

  Lemma power_code_correct s exponent :
    0 < bv_unsigned p -> (7 <= length (env n s))%nat ->
    bv_unsigned (read_register n (env n (run n p s (power_code exponent)).1) 6%nat) mod bv_unsigned p =
    (bv_unsigned (read_register n (env n s) 2%nat) ^ Z.pos exponent) mod bv_unsigned p.
  Proof.
    intros Hp Hlen. induction exponent as [e IH | e IH |].
    - cbn [power_code]. rewrite run_app_state.
      rewrite !run_cons_state. cbn [run fst].
      rewrite mul_step_value by (try exact Hp; rewrite step_preserves_length, run_preserves_length; lia).
      rewrite (step_read_other n p _ _ 2%nat) by (cbn; intuition congruence).
      rewrite mul_step_value by (try exact Hp; rewrite run_preserves_length; lia).
      rewrite (power_code_preserves s e 2%nat) by discriminate.
      rewrite Z.mod_mod by lia.
      rewrite (Z.mul_mod (bv_unsigned (read_register n (env n (run n p s (power_code e)).1) 6%nat)) _ _) by lia.
      rewrite IH.
      rewrite <- Z.mul_mod by lia.
      replace (Z.pos (xI e)) with (Z.pos e + Z.pos e + 1) by lia.
      rewrite !Z.pow_add_r by lia. rewrite Z.pow_1_r.
      repeat rewrite ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r. reflexivity.
    - cbn [power_code]. rewrite run_app_state.
      rewrite !run_cons_state. cbn [run fst].
      rewrite mul_step_value by (try exact Hp; rewrite run_preserves_length; lia).
      rewrite Z.mod_mod by lia. rewrite Z.mul_mod by lia. rewrite IH.
      rewrite <- Z.mul_mod by lia.
      replace (Z.pos (xO e)) with (Z.pos e + Z.pos e) by lia.
      rewrite Z.pow_add_r by lia. reflexivity.
    - cbn [power_code run step interp_env fst env].
      rewrite read_register_write_same by lia.
      rewrite Z.pow_1_r. reflexivity.
  Qed.

  Lemma affine_code_correct s exponent :
    0 < bv_unsigned p -> (7 <= length (env n s))%nat ->
    affine_result (run n p s (affine_code exponent)).1 =
    (affine_result s * bv_unsigned (read_register n (env n s) 2%nat) ^ Z.pos exponent) mod bv_unsigned p.
  Proof.
    intros Hp Hlen. unfold affine_code, affine_result. rewrite run_app_state.
    rewrite run_cons_state. cbn [run fst].
    rewrite mul_step_value by (try exact Hp; rewrite run_preserves_length; lia).
    rewrite (power_code_preserves s exponent 1%nat) by discriminate.
    rewrite Z.mul_mod by lia. rewrite power_code_correct by assumption.
    rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r. reflexivity.
  Qed.

  Lemma power_code_in_bounds exponent : Forall (in_bounds 28) (power_code exponent).
  Proof.
    induction exponent; cbn [power_code]; rewrite ?Forall_app; repeat split; try assumption; repeat constructor; cbn; lia.
  Qed.

  Lemma power_code_no_observe exponent : Forall no_observe (power_code exponent).
  Proof.
    induction exponent; cbn [power_code]; rewrite ?Forall_app; repeat split; try assumption; repeat constructor.
  Qed.

  Lemma affine_program_in_bounds width exponent : Forall (in_bounds 28) (affine_program width exponent).
  Proof.
    unfold affine_program, affine_code. rewrite !Forall_app.
    split; [apply projective_program_in_bounds |].
    split; [apply power_code_in_bounds | repeat constructor; cbn; lia].
  Qed.

  Lemma affine_program_no_observe width exponent : Forall no_observe (affine_program width exponent).
  Proof.
    unfold affine_program, affine_code. rewrite !Forall_app.
    split; [apply projective_program_no_observe |].
    split; [apply power_code_no_observe | repeat constructor].
  Qed.

  Theorem affine_program_correct x a24 scalar width exponent :
    0 < bv_unsigned p ->
    affine_result (run n p (initial_state n x a24 scalar) (affine_program width exponent)).1 =
    let '(X, Zc) := MontLadderCSwap (bv_unsigned p) (bv_unsigned a24) width (bv_unsigned x) (bv_unsigned scalar) in
    (X * Zc ^ Z.pos exponent) mod bv_unsigned p.
  Proof.
    intro Hp. unfold affine_program. rewrite run_app_state, affine_code_correct by (try exact Hp; rewrite run_preserves_length, initial_state_length; lia).
    pose proof (projective_program_correct n p x a24 scalar width Hp) as Hcoords.
    unfold projective_output, point_regs in Hcoords. rewrite <- Hcoords. reflexivity.
  Qed.

  Theorem affine_program_secure x a24 scalar width exponent :
    hw_trace n p (initial_state n x a24 scalar) (affine_program width exponent) =
      repeat (28 * N.to_nat n)%nat (S (length (affine_program width exponent))) /\
    (run n p (initial_state n x a24 scalar) (affine_program width exponent)).2 = [] /\
    valid_state n (run n p (initial_state n x a24 scalar) (affine_program width exponent)).1.
  Proof.
    split.
    - rewrite hw_trace_constant by apply initial_state_valid. rewrite initial_state_length. reflexivity.
    - split.
      + apply run_no_observe, affine_program_no_observe.
      + apply run_preserves_valid, initial_state_valid.
  Qed.
End Affine.
End LadderMachine.
