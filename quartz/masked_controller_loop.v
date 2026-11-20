From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import masked_controller masked_controller_schedule masked_controller_program
  masked_controller_functional masked_controller_tick_program.
From Masking Require Import fiat_field shared_ladder shared_loop shared_power ladder_bridge.
From Stdlib Require Import ZArith Bits List Lia.
Require Import ladder_math.
Import GRing.Theory.
Local Open Scope ring_scope.

Module MaskedControllerLoop.
Module C := MaskedController.
Module S := MaskedControllerSchedule.
Module P := MaskedControllerProgram.
Module F := MaskedControllerFunctional.
Module T := MaskedControllerTickProgram.
Local Notation K := FiatField.curve25519.
Local Notation bit_value := F.bitfield.
Local Notation coordinates := F.coords.

(* Decode replaces the first source address with the current public bit index. *)
Definition bit_prefix (i : nat) : list C.micro :=
  [:: C.Micro 0 (Z.of_nat i) 0 261; C.Micro 3 260 261 264; C.Micro 1 260 261 265;
      C.Micro 1 264 264 264; C.Micro 2 265 264 262].

Lemma scalar_operand a i : (i < 255)%nat -> P.operand a (Z.of_nat i) = a i.
Proof.
  intro Hi. have HiN : Nat.lt i 255 := elimT ltP Hi. unfold P.operand.
  have H282 : Z.eqb (Z.of_nat i) 282 = false by apply Z.eqb_neq; lia.
  have H283 : Z.eqb (Z.of_nat i) 283 = false by apply Z.eqb_neq; lia.
  by rewrite H282 H283 Nat2Z.id.
Qed.

Lemma prefix_current a i : P.run (bit_prefix i) a 261%nat = P.operand a (Z.of_nat i).
Proof. reflexivity. Qed.

Lemma prefix_xor a i bit prev :
  (i < 255)%nat -> a i = bit_value bit -> a 260%nat = bit_value prev ->
  P.run (bit_prefix i) a 262%nat = bit_value (xorb bit prev).
Proof.
  move=> Hi Hb Hp.
  change (a 260%nat + P.operand a (Z.of_nat i) -
    (a 260%nat * P.operand a (Z.of_nat i) + a 260%nat * P.operand a (Z.of_nat i)) =
    bit_value (xorb bit prev)).
  rewrite scalar_operand // Hb Hp /bit_value.
  clear Hb Hp.
  by case: bit; case: prev; rewrite ?mul1r ?mul0r ?addr0 ?add0r ?subr0 ?subrr.
Qed.

Lemma prefix_coordinates a i : coordinates (P.run (bit_prefix i) a) = coordinates a.
Proof. reflexivity. Qed.

Lemma prefix_input a i : P.run (bit_prefix i) a 255%nat = a 255%nat.
Proof. reflexivity. Qed.

Lemma run_app code1 code2 a : P.run (code1 ++ code2) a = P.run code2 (P.run code1 a).
Proof. exact: List.fold_left_app. Qed.

Lemma execute_frame ins a j : Nat.eqb j (Z.to_nat (C.destination ins)) = false ->
  P.execute ins a j = a j.
Proof. move=> H. by rewrite /P.execute H. Qed.

Lemma run_frame code a j :
  List.Forall (fun ins => Nat.eqb j (Z.to_nat (C.destination ins)) = false) code ->
  P.run code a j = a j.
Proof.
  move=> H. elim: H a => [|ins tail Hhead Htail IH] a; first reflexivity.
  change (P.run tail (P.execute ins a) j = a j).
  rewrite IH. exact: execute_frame Hhead.
Qed.

Lemma swap_current a : P.run P.pair_swap_program a 261%nat = a 261%nat.
Proof. reflexivity. Qed.

Lemma ladder_current a : P.run C.ladder_program a 261%nat = a 261%nat.
Proof. reflexivity. Qed.

Lemma swapped_coordinates a i bit prev :
  (i < 255)%nat -> a i = bit_value bit -> a 260%nat = bit_value prev ->
  coordinates (P.run P.pair_swap_program (P.run (bit_prefix i) a)) =
  SharedLoop.clear_swap (xorb bit prev) (coordinates a).
Proof.
  move=> Hi Hb Hp.
  rewrite /coordinates (P.pair_swap_correct (P.run (bit_prefix i) a) (xorb bit prev)
    (prefix_xor a i bit prev Hi Hb Hp)).
  change ((if xorb bit prev then
    ((P.run (bit_prefix i) a 258%nat,P.run (bit_prefix i) a 259%nat),
     (P.run (bit_prefix i) a 256%nat,P.run (bit_prefix i) a 257%nat)) else
    coordinates (P.run (bit_prefix i) a)) = SharedLoop.clear_swap (xorb bit prev) (coordinates a)).
  by case: (xorb bit prev).
Qed.

Theorem iteration_coordinates a i bit prev :
  (i < 255)%nat -> a i = bit_value bit -> a 260%nat = bit_value prev ->
  let out := P.run (bit_prefix i ++ P.pair_swap_program ++ C.ladder_program) a in
  ((out 277%nat,out 281%nat),(out 274%nat,out 276%nat)) =
  (SharedLoop.clear_iteration P.a24 (a 255%nat) bit (coordinates a,prev)).1.
Proof.
  move=> Hi Hb Hp.
  cbv zeta.
  rewrite (run_app (bit_prefix i) (P.pair_swap_program ++ C.ladder_program))
    (run_app P.pair_swap_program C.ladder_program) P.ladder_program_correct.
  rewrite P.pair_swap_preserves_input prefix_input.
  exact (f_equal (fun c : SharedLadder.coordinates K =>
    SharedLadder.clear_step P.a24 (a 255%nat) c.1.1 c.1.2 c.2.1 c.2.2)
    (swapped_coordinates a i bit prev Hi Hb Hp)).
Qed.

Theorem iteration_current a i bit :
  (i < 255)%nat -> a i = bit_value bit ->
  P.run (bit_prefix i ++ P.pair_swap_program ++ C.ladder_program) a 261%nat = bit_value bit.
Proof.
  move=> Hi Hb.
  by rewrite (run_app (bit_prefix i) (P.pair_swap_program ++ C.ladder_program))
    (run_app P.pair_swap_program C.ladder_program) ladder_current swap_current prefix_current scalar_operand.
Qed.

Theorem iteration_frame a i j :
  (Nat.le j 255 \/ j = 263%nat) ->
  P.run (bit_prefix i ++ P.pair_swap_program ++ C.ladder_program) a j = a j.
Proof.
  intro Hj. apply run_frame.
  unfold bit_prefix, P.pair_swap_program, C.swap_program, C.ladder_program.
  repeat constructor; apply Nat.eqb_neq; cbn; lia.
Qed.

Theorem final_swap_coordinates a prev : a 260%nat = bit_value prev ->
  coordinates (P.run C.final_program a) = SharedLoop.clear_swap prev (coordinates a).
Proof.
  intro H.
  pose renamed := fun j => if Nat.eqb j 262 then a 260%nat else a j.
  have Hr : renamed 262%nat = (if prev then 1 else 0) := H.
  exact (P.pair_swap_correct renamed prev Hr).
Qed.

Theorem final_swap_frame a j : (Nat.le j 255 \/ j = 263%nat) ->
  P.run C.final_program a j = a j.
Proof.
  intro Hj. apply run_frame. unfold C.final_program, C.swap_program.
  repeat constructor; apply Nat.eqb_neq; cbn; lia.
Qed.

Lemma patched_iterationE i :
  F.patched_iteration i = bit_prefix i ++ P.pair_swap_program ++ C.ladder_program.
Proof. reflexivity. Qed.

Theorem collected_iteration a i bit prev :
  (i < 255)%nat -> a i = bit_value bit -> a 260%nat = bit_value prev ->
  let out := F.collect_values (P.run (F.patched_iteration i) a) in
  coordinates out = (SharedLoop.clear_iteration P.a24 (a 255%nat) bit (coordinates a,prev)).1 /\
  out 260%nat = bit_value bit.
Proof.
  move=> Hi Hb Hp. split.
  - change (((P.run (F.patched_iteration i) a 277%nat,P.run (F.patched_iteration i) a 281%nat),
      (P.run (F.patched_iteration i) a 274%nat,P.run (F.patched_iteration i) a 276%nat)) =
      (SharedLoop.clear_iteration P.a24 (a 255%nat) bit (coordinates a,prev)).1).
    rewrite patched_iterationE. exact: iteration_coordinates Hi Hb Hp.
  - change (P.run (F.patched_iteration i) a 261%nat = bit_value bit).
    rewrite patched_iterationE. exact: iteration_current Hi Hb.
Qed.

Theorem collected_frame a i j : (Nat.le j 255 \/ j = 263%nat) ->
  F.collect_values (P.run (F.patched_iteration i) a) j = a j.
Proof.
  intro Hj. unfold F.collect_values.
  repeat match goal with |- context [if Nat.eqb ?x ?y then _ else _] =>
    destruct (Nat.eqb_spec x y); [lia|] end.
  rewrite patched_iterationE. exact: iteration_frame Hj.
Qed.

Definition inverse_exponent : Z := (C.Core.prime - 2)%Z.

Lemma bit_extract_255 (raw : bits 255) m : Nat.lt m 255 ->
  Zmod.firstn 1 (Zmod.skipn 0 (Zmod.sru raw
    (Zmod.unsigned (bits.of_Z 255 (Zmod.unsigned (bits.of_Z 8 (Z.of_nat m))))))) =
  Zmod.embed_bool (Z.testbit (Zmod.unsigned raw) (Z.of_nat m)).
Proof.
  intro Hm.
  apply Zmod.unsigned_inj.
  rewrite bits.unsigned_firstn (bits.unsigned_skipn (n := 0) _ ltac:(lia)).
  rewrite Z.div_1_r.
  rewrite (bits.unsigned_of_Z_small (n := 8) (Z.of_nat m) ltac:(lia)).
  rewrite (bits.unsigned_of_Z_small (n := 255) (Z.of_nat m) ltac:(lia)).
  rewrite (Zmod.unsigned_sru raw (Z.of_nat m) ltac:(lia)).
  rewrite (Z.shiftr_div_pow2 (Zmod.unsigned raw) (Z.of_nat m) ltac:(lia)).
  change ((Zmod.unsigned raw / 2^Z.of_nat m mod 2)%Z =
    Zmod.unsigned (Zmod.embed_bool (Z.testbit (Zmod.unsigned raw) (Z.of_nat m)))).
  pose proof (Z.testbit_spec' (Zmod.unsigned raw) (Z.of_nat m) ltac:(lia)) as H.
  destruct (Z.testbit (Zmod.unsigned raw) (Z.of_nat m)); cbn in H |- *; lia.
Qed.

Lemma exponent_bit m : Nat.lt m 255 ->
  Zmod.firstn 1 (Zmod.skipn 0 (Zmod.sru (bits.of_Z 255 inverse_exponent)
    (Zmod.unsigned (bits.of_Z 255 (Zmod.unsigned (bits.of_Z 8 (Z.of_nat m))))))) =
  Zmod.embed_bool (bit_i inverse_exponent m).
Proof.
  intro Hm. rewrite (bit_extract_255 _ m Hm).
  have He : (0 <= inverse_exponent < 2^255)%Z by unfold inverse_exponent, C.Core.prime; lia.
  rewrite (bits.unsigned_of_Z_small _ He). reflexivity.
Qed.

Theorem decode_multiply m : Nat.lt m 255 ->
  fn.interp C.decode (S.control 4 (bits.of_Z 8 (Z.of_nat m)) 0) =
  C.encode_instruction (C.Micro 3 263 (if bit_i inverse_exponent m then 257%Z else 282%Z) 263).
Proof.
  intro Hm.
  change ((bits.of_Z 2 3,(bits.of_Z 9 263,((if Zmod.nonzero
    (Zmod.firstn 1 (Zmod.skipn 0 (Zmod.sru (bits.of_Z 255 inverse_exponent)
      (Zmod.unsigned (bits.of_Z 255 (Zmod.unsigned (bits.of_Z 8 (Z.of_nat m))))))))
    then bits.of_Z 9 257 else bits.of_Z 9 282),bits.of_Z 9 263))) =
    C.encode_instruction (C.Micro 3 263 (if bit_i inverse_exponent m then 257%Z else 282%Z) 263)).
  rewrite (exponent_bit m Hm) Zmod.nonzero_bool.
  by case: (bit_i inverse_exponent m).
Qed.

Fixpoint power_steps (m : nat) (z acc : K) : K :=
  match m with
  | O => acc
  | S m => power_steps m z ((acc * acc) * (if bit_i inverse_exponent m then z else 1))
  end.

Local Notation encode := (FiatField.encode FiatField.curve25519_modulus_gt1).

Lemma power_step z prefix bit : (0 <= prefix)%Z ->
  (encode (z^prefix)%Z * encode (z^prefix)%Z) * (if bit then encode z else 1) =
  encode (z^(2*prefix + if bit then 1 else 0))%Z.
Proof.
  intro Hp. case: bit.
  - rewrite -!FiatField.encode_mul.
    replace (2*prefix+1)%Z with ((prefix+prefix)+1)%Z by lia.
    by rewrite !Z.pow_add_r ?Z.pow_1_r; try lia.
  - rewrite mulr1 -FiatField.encode_mul.
    replace (2*prefix+0)%Z with (prefix+prefix)%Z by lia.
    by rewrite Z.pow_add_r; try lia.
Qed.

Theorem power_steps_index m z prefix : (0 <= prefix)%Z ->
  power_steps m (encode z) (encode (z^prefix)%Z) = encode (z^(ladder_index m inverse_exponent prefix))%Z.
Proof.
  revert prefix. induction m as [|m IH]; intros prefix Hp; first reflexivity.
  cbn [power_steps ladder_index]. rewrite (power_step z prefix _ Hp).
  apply IH. destruct (bit_i inverse_exponent m); lia.
Qed.

Theorem power_steps_255 z : power_steps 255 (encode z) 1 = encode (z^inverse_exponent)%Z.
Proof.
  replace (1 : K) with (encode (z^0)%Z) by (rewrite Z.pow_0_r; reflexivity).
  rewrite (power_steps_index 255 z 0 ltac:(lia)).
  rewrite ladder_index_value Z.mul_0_l Z.add_0_l.
  have He : (0 <= inverse_exponent < 2 ^ Z.of_nat 255)%Z.
  { unfold inverse_exponent, C.Core.prime. cbn [Z.of_nat]. lia. }
  by rewrite (Z.mod_small _ _ He).
Qed.

Definition power_pair bit : list C.micro :=
  C.Micro 3 263 263 263 :: C.Micro 3 263 (if bit then 257%Z else 282%Z) 263 :: List.nil.

Lemma power_pair_valid bit : List.Forall P.valid_instruction (power_pair bit).
Proof. case: bit; repeat constructor; cbn; lia. Qed.

Lemma power_pair_value a bit :
  P.run (power_pair bit) a 263%nat =
  (a 263%nat * a 263%nat) * (if bit then a 257%nat else 1).
Proof. by case: bit. Qed.

Lemma power_pair_frame a bit j : j <> 263%nat -> P.run (power_pair bit) a j = a j.
Proof.
  intro Hj. apply run_frame. case: bit; repeat constructor;
    cbn; apply Nat.eqb_neq; exact Hj.
Qed.

Lemma finish_value a : P.execute (C.Micro 3 256 263 263) a 263%nat = a 256%nat * a 263%nat.
Proof. reflexivity. Qed.

Definition bit_control m : type.interp C.Control :=
  match m with
  | O => S.control 2 (bits.of_Z 8 0) 0
  | S i => S.control 1 (bits.of_Z 8 (Z.of_nat i)) 0
  end.

Lemma bit_control_next i : Nat.lt i 255 -> S.run 32 (bit_control (S i)) = bit_control i.
Proof.
  intro Hi. destruct i as [|i].
  - exact S.iteration_zero.
  - apply S.iteration_successor. lia.
Qed.

Definition bank_matches (a : P.Bank) xp bits (st : SharedLoop.clear_state K) : Prop :=
  coordinates a = st.1 /\ a 260%nat = bit_value st.2 /\ a 255%nat = xp /\
  a 263%nat = 1 /\ forall j, Nat.lt j 255 -> a j = bit_value (bits j).

Lemma agrees_coordinates a b : T.agrees a b -> coordinates a = coordinates b.
Proof.
  intro H. unfold T.agrees, C.groups in H. unfold F.coords.
  rewrite (H 256%nat ltac:(lia)) (H 257%nat ltac:(lia))
    (H 258%nat ltac:(lia)) (H 259%nat ltac:(lia)). reflexivity.
Qed.

Lemma agrees_matches a b xp bits st : T.agrees a b -> bank_matches b xp bits st ->
  bank_matches a xp bits st.
Proof.
  intros H [Hc [Hp [Hx [Ha Hb]]]]. unfold bank_matches.
  unfold T.agrees, C.groups in H.
  rewrite (agrees_coordinates _ _ H) (H 260%nat ltac:(lia))
    (H 255%nat ltac:(lia)) (H 263%nat ltac:(lia)).
  repeat split; try assumption. intros j Hj. rewrite (H j ltac:(lia)). exact (Hb j Hj).
Qed.

Lemma collected_matches a xp bits st i : Nat.lt i 255 -> bank_matches a xp bits st ->
  bank_matches (F.collect_values (P.run (F.patched_iteration i) a)) xp bits
    (SharedLoop.clear_iteration P.a24 xp (bits i) st).
Proof.
  intros Hi [Hc [Hp [Hx [Ha Hb]]]].
  have Hi' : (i < 255)%nat by apply/ltP.
  have H := collected_iteration a i (bits i) st.2 Hi' (Hb i Hi) Hp.
  cbv zeta in H. rewrite Hc Hx in H.
  have Hst : (st.1,st.2) = st by destruct st; reflexivity.
  rewrite Hst in H. destruct H as [Hout Hprev].
  split; [exact Hout|]. split; [exact Hprev|].
  split; [rewrite (collected_frame a i 255 ltac:(lia)); exact Hx|].
  split; [rewrite (collected_frame a i 263 ltac:(lia)); exact Ha|].
  intros j Hj. rewrite (collected_frame a i j ltac:(lia)). exact (Hb j Hj).
Qed.

Definition power_control m : type.interp C.Control :=
  match m with
  | O => S.control 5 (bits.of_Z 8 0) 0
  | S i => S.control 3 (bits.of_Z 8 (Z.of_nat i)) 0
  end.

Lemma power_control_next i : Nat.lt i 255 -> S.run 2 (power_control (S i)) = power_control i.
Proof.
  intro Hi. destruct i as [|i].
  - exact S.affine_zero.
  - apply S.affine_successor. lia.
Qed.

Lemma power_scheduled i : Nat.lt i 255 ->
  T.scheduled (power_control (S i)) (power_pair (bit_i inverse_exponent i)).
Proof.
  intro Hi. split; [repeat split; cbn; lia|]. split.
  - intros n bank masks. rewrite (F.prepare_active_execute n 3 _ _ _ _ ltac:(auto)).
    reflexivity.
  - change (T.scheduled (S.control 4 (bits.of_Z 8 (Z.of_nat i)) 0)
      [:: C.Micro 3 263 (if bit_i inverse_exponent i then 257%Z else 282%Z) 263]).
    split; [case: (bit_i inverse_exponent i); repeat split; cbn; lia|]. split.
    + intros n bank masks. rewrite (F.prepare_active_execute n 4 _ _ _ _ ltac:(auto)).
      rewrite (decode_multiply i Hi). reflexivity.
    + exact I.
Qed.

Definition power_matches (a : P.Bank) x z acc : Prop :=
  a 256%nat = x /\ a 257%nat = z /\ a 263%nat = acc.

Lemma agrees_power a b x z acc : T.agrees a b -> power_matches b x z acc ->
  power_matches a x z acc.
Proof.
  intros H Hb. unfold T.agrees, C.groups in H. unfold power_matches in *.
  by rewrite (H 256%nat ltac:(lia)) (H 257%nat ltac:(lia)) (H 263%nat ltac:(lia)).
Qed.

Lemma pair_matches a x z acc bit : power_matches a x z acc ->
  power_matches (P.run (power_pair bit) a) x z (acc * acc * (if bit then z else 1)).
Proof.
  intros [Hx [Hz Ha]]. unfold power_matches.
  rewrite (power_pair_frame a bit 256 ltac:(lia)) (power_pair_frame a bit 257 ltac:(lia))
    power_pair_value Hx Hz Ha. repeat split.
Qed.

Definition inverse_power : positive := Z.to_pos inverse_exponent.

Lemma power_steps_clear_power z :
  power_steps 255 z 1 = SharedPower.clear_power inverse_power z.
Proof.
  rewrite -(@FiatField.encode_to_Z FiatField.curve25519_modulus FiatField.curve25519_modulus_gt1 z)
    power_steps_255.
  rewrite (@LadderBridge.power_matches_math K encode (FiatField.encode_mul _) inverse_power).
  have He : (0 < inverse_exponent)%Z by unfold inverse_exponent, C.Core.prime; lia.
  unfold inverse_power. by rewrite (Z2Pos.id _ He).
Qed.

Definition input_bits (input : type.interp C.Load) i := Z.testbit (Zmod.unsigned input.2) (Z.of_nat i).
Definition initial_clear (input : type.interp C.Load) : SharedLoop.clear_state K :=
  (((1,0),(C.M.decode_word input.1,1)),false).

Lemma loaded_matches input : bank_matches (F.loaded_value input) (C.M.decode_word input.1)
  (input_bits input) (initial_clear input).
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros j Hj. unfold F.loaded_value.
  repeat match goal with |- context [if Nat.eqb ?x ?y then _ else _] =>
    destruct (Nat.eqb_spec x y); [lia|] end.
  have Hj' : (j < 255)%nat by apply/ltP.
  change ((if (j < 255)%nat then F.scalar_bit input.2 j else 0) = bit_value (input_bits input j)).
  rewrite Hj'. reflexivity.
Qed.

Section Actual.
Variable n : nat.
Variable encoded : forall ins bank masks, P.valid_instruction ins ->
  T.agrees (F.value n (fn.interp (C.execute n) (C.encode_instruction ins,(bank,masks))))
    (P.execute ins (F.value n bank)).

Theorem loop_ticks m randomness s xp bits st : Nat.le m 255 -> s.1 = bit_control m ->
  bank_matches (F.value n s.2) xp bits st ->
  bank_matches (F.value n (S.ticks n (Nat.mul 32 m) randomness s).2) xp bits
    (SharedLoop.clear_run m P.a24 xp bits st).
Proof.
  revert randomness s st. induction m as [|m IH]; intros randomness [c bank] st Hm Hc Hbank.
  - exact Hbank.
  - cbn [fst] in Hc. subst c.
    replace (Nat.mul 32 (S m)) with (Nat.add 32 (Nat.mul 32 m)) by lia. rewrite T.ticks_add.
    set middle := S.ticks n 32 (fun j => randomness (Nat.add (Nat.mul 32 m) j)) (bit_control (S m),bank).
    have Hmiddle : middle.1 = bit_control m.
    { rewrite /middle S.ticks_public_control. apply bit_control_next. lia. }
    have Hvalues := T.iteration_ticks_from_encoded n encoded m bank
      (fun j => randomness (Nat.add (Nat.mul 32 m) j)) ltac:(lia).
    have Hmatches : bank_matches (F.value n middle.2) xp bits
      (SharedLoop.clear_iteration P.a24 xp (bits m) st).
    { apply (agrees_matches _ _ _ _ _ Hvalues).
      apply collected_matches; [lia|exact Hbank]. }
    exact (IH randomness middle _ ltac:(lia) Hmiddle Hmatches).
Qed.

Theorem power_ticks m randomness s x z acc : Nat.le m 255 -> s.1 = power_control m ->
  power_matches (F.value n s.2) x z acc ->
  power_matches (F.value n (S.ticks n (Nat.mul 2 m) randomness s).2) x z (power_steps m z acc).
Proof.
  revert randomness s acc. induction m as [|m IH]; intros randomness [c bank] acc Hm Hc Hbank.
  - exact Hbank.
  - cbn [fst] in Hc. subst c.
    replace (Nat.mul 2 (S m)) with (Nat.add 2 (Nat.mul 2 m)) by lia. rewrite T.ticks_add.
    set middle := S.ticks n 2 (fun j => randomness (Nat.add (Nat.mul 2 m) j)) (power_control (S m),bank).
    have Hmiddle : middle.1 = power_control m.
    { rewrite /middle S.ticks_public_control. apply power_control_next. lia. }
    have Hvalues := T.scheduled_ticks_from_encoded n encoded (power_pair (bit_i inverse_exponent m))
      (fun j => randomness (Nat.add (Nat.mul 2 m) j)) (power_control (S m),bank)
      (power_scheduled m ltac:(lia)).
    have Hmatches : power_matches (F.value n middle.2) x z
      (acc * acc * (if bit_i inverse_exponent m then z else 1)).
    { apply (agrees_power _ _ _ _ _ Hvalues). exact (pair_matches _ _ _ _ _ Hbank). }
    exact (IH randomness middle _ ltac:(lia) Hmiddle Hmatches).
Qed.

Theorem affine_ticks randomness s x z : s.1 = power_control 255 ->
  power_matches (F.value n s.2) x z 1 ->
  F.value n (S.ticks n 511 randomness s).2 263%nat = x * power_steps 255 z 1.
Proof.
  intros Hc Hbank.
  change (F.value n (S.ticks n (Nat.add 510 1) randomness s).2 263%nat = x * power_steps 255 z 1).
  rewrite T.ticks_add.
  set middle := S.ticks n 510 (fun j => randomness (Nat.add 1 j)) s.
  have Hmiddle : middle.1 = power_control 0.
  { rewrite /middle S.ticks_public_control Hc. exact (S.affine_count 254 ltac:(lia)). }
  have Hvalues := power_ticks 255 (fun j => randomness (Nat.add 1 j)) s x z 1
    ltac:(lia) Hc Hbank.
  change (power_matches (F.value n middle.2) x z (power_steps 255 z 1)) in Hvalues.
  destruct middle as [c bank]. cbn in Hmiddle. subst c.
  have Hscheduled : T.scheduled (power_control 0) [:: C.Micro 3 256 263 263].
  { split; [repeat split; cbn; lia|]. split.
    - intros k b masks. rewrite (F.prepare_active_execute k 5 _ _ _ _ ltac:(auto)). reflexivity.
    - exact I. }
  have Hlast := T.scheduled_ticks_from_encoded n encoded [:: C.Micro 3 256 263 263]
    randomness (power_control 0,bank) Hscheduled.
  rewrite (Hlast 263%nat ltac:(unfold C.groups; lia)).
  change (F.value n bank 256%nat * F.value n bank 263%nat = x * power_steps 255 z 1).
  destruct Hvalues as [Hx [Hz Ha]]. by rewrite Hx Ha.
Qed.

Theorem projective_ticks randomness s xp bits st : s.1 = bit_control 255 ->
  bank_matches (F.value n s.2) xp bits st ->
  let out := S.ticks n 8168 randomness s in
  (F.value n out.2 256%nat,F.value n out.2 257%nat) =
    SharedLoop.clear_finish (SharedLoop.clear_run 255 P.a24 xp bits st) /\
  F.value n out.2 263%nat = 1.
Proof.
  intros Hc Hb. cbv zeta.
  change (let out := S.ticks n (Nat.add 8160 8) randomness s in
    (F.value n out.2 256%nat,F.value n out.2 257%nat) =
      SharedLoop.clear_finish (SharedLoop.clear_run 255 P.a24 xp bits st) /\
    F.value n out.2 263%nat = 1).
  rewrite T.ticks_add.
  set middle := S.ticks n 8160 (fun j => randomness (Nat.add 8 j)) s.
  have Hmiddle : middle.1 = bit_control 0.
  { rewrite /middle S.ticks_public_control Hc. exact (S.projective_count 254 ltac:(lia)). }
  have Hloop := loop_ticks 255 (fun j => randomness (Nat.add 8 j)) s xp bits st ltac:(lia) Hc Hb.
  change (bank_matches (F.value n middle.2) xp bits
    (SharedLoop.clear_run 255 P.a24 xp bits st)) in Hloop.
  destruct middle as [c bank]. cbn [fst] in Hmiddle. subst c.
  destruct Hloop as [Hcoords [Hprev [Hxp [Hacc Hbits]]]].
  have Hlast := T.final_ticks_from_encoded n encoded (bits.of_Z 8 0) bank randomness.
  split.
  - rewrite (Hlast 256%nat ltac:(unfold C.groups; lia)) (Hlast 257%nat ltac:(unfold C.groups; lia)).
    have Hswap := final_swap_coordinates (F.value n bank)
      (SharedLoop.clear_run 255 P.a24 xp bits st).2 Hprev.
    rewrite Hcoords in Hswap. exact (f_equal fst Hswap).
  - rewrite (Hlast 263%nat ltac:(unfold C.groups; lia))
      (final_swap_frame (F.value n bank) 263 ltac:(lia)). exact Hacc.
Qed.

Theorem complete_ticks randomness s xp bits st : s.1 = bit_control 255 ->
  bank_matches (F.value n s.2) xp bits st ->
  let p := SharedLoop.clear_finish (SharedLoop.clear_run 255 P.a24 xp bits st) in
  F.value n (S.ticks n S.work_edges randomness s).2 263%nat =
    p.1 * SharedPower.clear_power inverse_power p.2.
Proof.
  intros Hc Hb. cbv zeta.
  change (F.value n (S.ticks n (Nat.add 8168 511) randomness s).2 263%nat =
    (SharedLoop.clear_finish (SharedLoop.clear_run 255 P.a24 xp bits st)).1 *
    SharedPower.clear_power inverse_power
      (SharedLoop.clear_finish (SharedLoop.clear_run 255 P.a24 xp bits st)).2).
  rewrite T.ticks_add.
  set middle := S.ticks n 8168 (fun j => randomness (Nat.add 511 j)) s.
  have Hmiddle : middle.1 = power_control 255.
  { rewrite /middle S.ticks_public_control Hc.
    change (S.run (Nat.add 8160 8) (bit_control 255) = power_control 255).
    rewrite S.run_add (S.projective_count 254 ltac:(lia)). exact (S.final_swaps _). }
  have Hp := projective_ticks (fun j => randomness (Nat.add 511 j)) s xp bits st Hc Hb.
  change ((F.value n middle.2 256%nat,F.value n middle.2 257%nat) =
    SharedLoop.clear_finish (SharedLoop.clear_run 255 P.a24 xp bits st) /\
    F.value n middle.2 263%nat = 1) in Hp.
  destruct Hp as [Hpair Ha].
  have Hbank : power_matches (F.value n middle.2)
    (SharedLoop.clear_finish (SharedLoop.clear_run 255 P.a24 xp bits st)).1
    (SharedLoop.clear_finish (SharedLoop.clear_run 255 P.a24 xp bits st)).2 1.
  { split; [exact (f_equal fst Hpair)|]. split; [exact (f_equal snd Hpair)|exact Ha]. }
  rewrite (affine_ticks randomness middle _ _ Hmiddle Hbank) power_steps_clear_power. reflexivity.
Qed.

Theorem program_correct input first_randomness randomness :
  F.value n (S.ticks n S.work_edges randomness (S.launch n input first_randomness)).2 263%nat =
  SharedLoop.clear_affine inverse_power 255 P.a24 (C.M.decode_word input.1) (input_bits input).
Proof.
  have Hc : (S.launch n input first_randomness).1 = bit_control 255 := S.launch_control n input first_randomness.
  have Hvalues : T.agrees (F.value n (S.launch n input first_randomness).2) (F.loaded_value input).
  { intros j Hj. have Hj' : (j < C.groups)%nat by apply/ltP.
    exact (F.launch_reconstruct n input first_randomness (Ordinal Hj')). }
  have Hbank := agrees_matches _ _ _ _ _ Hvalues (loaded_matches input).
  exact (complete_ticks randomness (S.launch n input first_randomness)
    (C.M.decode_word input.1) (input_bits input) (initial_clear input) Hc Hbank).
Qed.

End Actual.

Theorem program_correct_actual n input first_randomness randomness :
  F.value n (S.ticks n S.work_edges randomness (S.launch n input first_randomness)).2 263%nat =
  SharedLoop.clear_affine inverse_power 255 P.a24 (C.M.decode_word input.1) (input_bits input).
Proof. exact (program_correct n (T.execute_encoded n) input first_randomness randomness). Qed.

End MaskedControllerLoop.

Print Assumptions MaskedControllerLoop.iteration_coordinates.
Print Assumptions MaskedControllerLoop.final_swap_coordinates.
Print Assumptions MaskedControllerLoop.decode_multiply.
Print Assumptions MaskedControllerLoop.power_steps_255.
Print Assumptions MaskedControllerLoop.program_correct_actual.
