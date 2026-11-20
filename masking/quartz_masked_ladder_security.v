From Stdlib Require Import ZArith Bits.
From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import masked_arithmetic masked_bank masked_controller
  masked_controller_schedule masked_controller_storage masked_controller_curve.
From Crypto Require Import Spec.Curve25519.
From Masking Require Import finite_masking fiat_field quartz_masked_hw quartz_masked_bank_security
  quartz_masked_execution quartz_masked_budget noisy_leakage noisy_shares noisy_channel_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module QuartzMaskedLadderSecurity.
Module M := MaskedArithmetic.
Module B := MaskedBank.
Module C := MaskedController.
Module Schedule := MaskedControllerSchedule.
Module Storage := MaskedControllerStorage.
Module Bridge := QuartzMaskedBankSecurity.
Module E := QuartzMaskedExecution.
Module Curve := MaskedControllerCurve.
Local Notation K := FiatField.curve25519.

Definition FieldMasks k := Bridge.FieldCoins k k.

Definition encode_masks k (r : FieldMasks k) : type.interp (M.Masks k) :=
  Bridge.tabulate (M.Shares k) k (fun i =>
    Bridge.tabulate M.Word k (fun j => Bridge.encode_word (r i j))).

Theorem decode_encode_masks k (r : FieldMasks k) :
  M.decode_masks k (encode_masks r) = [ffun ij => r ij.1 ij.2].
Proof.
apply/ffunP => ij.
by rewrite /M.decode_masks /encode_masks !ffunE !Bridge.read_tabulate Bridge.encode_word_decode.
Qed.

Theorem encode_masks_canonical k (r : FieldMasks k) (i j : 'I_k) :
  QuartzMaskedHW.canonical
    (@M.read M.Word k (@M.read (M.Shares k) k (encode_masks r) (val i)) (val j)).
Proof. rewrite /encode_masks !Bridge.read_tabulate. exact: Bridge.encode_word_canonical. Qed.

Definition reset (_ : nat) : bits 1 := bits.of_Z 1 0.
Definition start (time : nat) : bits 1 :=
  if time is Datatypes.O then bits.of_Z 1 1 else bits.of_Z 1 0.
Definition control := E.control_at reset start (type.default C.Control).

Definition port n (load : type.interp C.Load) (r : FieldMasks n.+1) :=
  (load,encode_masks r).

Definition tick n time (load : type.interp C.Load) (s : type.interp (C.State n))
    (masks : FieldMasks n.+1) (coins : Bridge.FieldCoins n C.groups) :=
  fn.interp (C.tick n)
    (s,((reset time,(start time,load)),(encode_masks masks,Bridge.encode_coins coins))).

Theorem tick_canonical n time load s masks coins :
  B.canonical n C.groups s.2 -> B.canonical n C.groups (tick time load s masks coins).2.
Proof.
exact (C.tick_preserves_canonical n
  (s,((reset time,(start time,load)),(encode_masks masks,Bridge.encode_coins coins)))).
Qed.

Theorem tick_control n time load (s : type.interp (C.State n)) masks coins :
  s.1 = control time -> (tick time load s masks coins).1 = control time.+1.
Proof.
move=> H. rewrite /tick C.tick_public_control.
change (fn.interp C.next_control (s.1,(reset time,start time)) = control time.+1).
by rewrite H.
Qed.

Lemma advance_run k c :
  Schedule.run k (fn.interp C.advance c) = fn.interp C.advance (Schedule.run k c).
Proof.
elim: k c => [|k IH] c; first reflexivity.
change (Schedule.run k (fn.interp C.advance (fn.interp C.advance c)) =
  fn.interp C.advance (Schedule.run k (fn.interp C.advance c))).
exact: IH.
Qed.

Theorem control_work k : control k.+1 = Schedule.run k Schedule.start_control.
Proof.
elim: k => [|k IH]; first exact: Schedule.initialization.
change (fn.interp C.next_control (control k.+1,(bits.of_Z 1 0,bits.of_Z 1 0)) =
  Schedule.run k.+1 Schedule.start_control).
rewrite IH Schedule.next_without_commands.
exact: esym (advance_run k Schedule.start_control).
Qed.

Theorem control_done : control C.scheduled_edges = Schedule.done_control.
Proof.
rewrite -Schedule.edge_count.
change (control Schedule.work_edges.+1 = Schedule.done_control).
rewrite control_work. exact: Schedule.complete_schedule.
Qed.

(* The tapes select samples; every transition is the same actual tick used by the probabilistic interpreter. *)
Fixpoint run_ticks n fuel time load (masks : nat -> FieldMasks n.+1)
    (coins : nat -> Bridge.FieldCoins n C.groups) (s : type.interp (C.State n)) :=
  match fuel with
  | Datatypes.O => s
  | Datatypes.S k => run_ticks k time.+1 load masks coins (tick time load s (masks time) (coins time))
  end.

Theorem run_ticks_canonical n fuel time load masks coins s :
  B.canonical n C.groups s.2 -> B.canonical n C.groups (@run_ticks n fuel time load masks coins s).2.
Proof.
elim: fuel time s => [|fuel IH] time s H; cbn [run_ticks]; first exact H.
apply: IH. exact: tick_canonical H.
Qed.

Theorem run_ticks_control n fuel time load masks coins s : s.1 = control time ->
  (@run_ticks n fuel time load masks coins s).1 = control (time + fuel)%nat.
Proof.
elim: fuel time s => [|fuel IH] time s H; cbn [run_ticks]; first by rewrite addn0.
rewrite (IH _ _ (@tick_control n time load s (masks time) (coins time) H)).
by rewrite addnS addSn.
Qed.

Theorem initialized_run_canonical n fuel load masks coins :
  B.canonical n C.groups (@run_ticks n fuel 0%nat load masks coins (C.initial_state n)).2.
Proof. apply: run_ticks_canonical. exact: C.initial_canonical. Qed.

Theorem run_ticks_ready n load masks coins :
  fn.interp (C.ready n) (@run_ticks n C.scheduled_edges 0%nat load masks coins (C.initial_state n)) =
  bits.of_Z 1 1.
Proof.
have H := @run_ticks_control n C.scheduled_edges 0%nat load masks coins (C.initial_state n) erefl.
rewrite add0n control_done in H.
change (Zmod.embed_bool (Zmod.eqb
  (@run_ticks n C.scheduled_edges 0%nat load masks coins (C.initial_state n)).1.1
  (bits.of_Z 3 6)) = bits.of_Z 1 1).
by rewrite H.
Qed.

Definition randomness_at n (masks : nat -> FieldMasks n.+1)
    (coins : nat -> Bridge.FieldCoins n C.groups) time : type.interp (C.Randomness n) :=
  (encode_masks (masks time),Bridge.encode_coins (coins time)).

Theorem no_command_load n (s : type.interp (C.State n)) load randomness :
  fn.interp (C.tick n) (s,((bits.of_Z 1 0,(bits.of_Z 1 0,load)),randomness)) =
  fn.interp (C.tick n) (s,(Schedule.no_command,randomness)).
Proof. reflexivity. Qed.

Theorem tick_work n time load (s : type.interp (C.State n)) masks coins :
  tick time.+1 load s masks coins =
  fn.interp (C.tick n) (s,(Schedule.no_command,(encode_masks masks,Bridge.encode_coins coins))).
Proof. exact: no_command_load. Qed.

Theorem tick_launch n load masks coins :
  @tick n 0%nat load (C.initial_state n) masks coins =
  Schedule.launch n load (encode_masks masks,Bridge.encode_coins coins).
Proof. reflexivity. Qed.

(* Schedule.ticks consumes a countdown tape; run_ticks consumes the same samples chronologically. *)
Theorem run_ticks_work n fuel time load masks coins (s : type.interp (C.State n)) :
  @run_ticks n fuel time.+1 load masks coins s =
  Schedule.ticks n fuel (fun k => randomness_at masks coins (time + fuel - k)%nat) s.
Proof.
elim: fuel time s => [|fuel IH] time s; first reflexivity.
cbn [run_ticks Schedule.ticks].
rewrite tick_work IH.
by rewrite addnS -addSn addnK.
Qed.

Lemma run_ticks_launch_work n fuel load masks coins :
  @run_ticks n fuel.+1 0%nat load masks coins (C.initial_state n) =
  Schedule.ticks n fuel
    (fun k => randomness_at masks coins (fuel - k)%nat)
    (Schedule.launch n load (randomness_at masks coins 0%nat)).
Proof.
cbn [run_ticks].
rewrite tick_launch (@run_ticks_work n fuel 0%nat).
by rewrite add0n.
Qed.

Theorem run_ticks_schedule n load masks coins :
  @run_ticks n C.scheduled_edges 0%nat load masks coins (C.initial_state n) =
  Schedule.ticks n Schedule.work_edges
    (fun k => randomness_at masks coins (Schedule.work_edges - k)%nat)
    (Schedule.launch n load (randomness_at masks coins 0%nat)).
Proof. rewrite -Schedule.edge_count. exact: run_ticks_launch_work. Qed.

Section Sampling.
Variable R : realType.
Variables n bound count : nat.
Local Notation O := [the finType of 'I_bound.+1].
Local Notation H := [the finType of (unit : Type)].
Local Notation A := (FieldMasks n.+1).
Local Notation S := [the finType of (E.Bank n * unit)%type].

(* Uniform matrices are sampled anew, independently of the bank and prior observations. *)
Definition policy (_ : nat) (_ : S) : R.-fdist A := uniform R (FieldMasks n.+1).
Definition update (_ : nat) (_ : unit) (_ : A) (_ : O) := tt.
Definition initial_update (_ : unit) (_ : O) := tt.
Definition noise := NoisyChannelBridge.scalar_channel R bound count.

Theorem sampled_masks_decode :
  fdistmap (fun r => B.decode_coins n.+1 n.+1 (encode_masks r)) (uniform R (FieldMasks n.+1)) =
  uniform R (FieldMasks n.+1).
Proof.
have H r : B.decode_coins n.+1 n.+1 (encode_masks r) = r.
  exact: Bridge.decode_coins_encode.
have -> : (fun r => B.decode_coins n.+1 n.+1 (encode_masks r)) = id.
  exact/boolp.funeqP.
exact: fdistmap_id.
Qed.

Definition trace (load : type.interp C.Load) :=
  @E.initial_execution R n H A O reset start (fun _ => noise) noise
    (port load) policy update initial_update C.scheduled_edges (fdist1 tt).

Theorem tick_is_actual time load raw masks coins :
  @E.next_raw n A reset start (port load) time raw masks coins = tick time load raw masks coins.
Proof. reflexivity. Qed.

Theorem trace_initial_sample load :
  trace load = noise (Storage.state_HW n (C.initial_state n)) >>= (fun o =>
    fdistmap (fun tr => (o,tr))
      (@E.actual_run R n H A O reset start (fun _ => noise) (port load) policy update
        C.scheduled_edges 0%nat (C.initial_state n) tt)).
Proof.
rewrite /trace /E.initial_execution.
congr (fdistbind _ _); apply/boolp.funeqP => o.
congr (fdistmap _ _). by rewrite fdist1bind.
Qed.

Theorem actual_run_fresh fuel time load raw :
  @E.actual_run R n H A O reset start (fun _ => noise) (port load) policy update
    fuel.+1 time raw tt =
  uniform R (FieldMasks n.+1) >>= (fun masks =>
  uniform R (Bridge.FieldCoins n C.groups) >>= (fun coins =>
  let out := tick time load raw masks coins in
  noise (Storage.state_HW n out) >>= (fun o =>
  fdistmap (fun tr => (o,tr))
    (@E.actual_run R n H A O reset start (fun _ => noise) (port load) policy update
      fuel time.+1 out tt)))).
Proof. reflexivity. Qed.
End Sampling.

Section Security.
Variable R : realType.
Variables bound count : nat.
Hypothesis capacity : leq (16 + C.groups * (256 * 255) + count)%nat bound.

Theorem ladder_trace_256 xp scalar1 scalar2 :
  NoisyLeakage.TV (@trace R 255 bound count (xp,scalar1)) (@trace R 255 bound count (xp,scalar2)) <=
    (2:R)^-66.
Proof.
exact (@QuartzMaskedBudget.execution_256 R bound count [the finType of (unit : Type)] (FieldMasks 256)
  reset start (@port 255 (xp,scalar1)) (@port 255 (xp,scalar2))
  (@policy R 255) (@policy R 255) (@update 255 bound) (@update 255 bound)
  (@initial_update bound) (@initial_update bound) capacity (fdist1 tt) (fdist1 tt)).
Qed.

Theorem ladder_trace_repeated_256 q xp scalar1 scalar2 : leq q (2 ^ 32) ->
  NoisyLeakage.TV
    (NoisyLeakage.iid (@trace R 255 bound count (xp,scalar1)) q)
    (NoisyLeakage.iid (@trace R 255 bound count (xp,scalar2)) q) <= (2:R)^-34.
Proof.
exact (@QuartzMaskedBudget.repeated_execution_256 R bound count [the finType of (unit : Type)] (FieldMasks 256)
  reset start (@port 255 (xp,scalar1)) (@port 255 (xp,scalar2))
  (@policy R 255) (@policy R 255) (@update 255 bound) (@update 255 bound)
  (@initial_update bound) (@initial_update bound) capacity q (fdist1 tt) (fdist1 tt)).
Qed.

Theorem ladder_trace_contract_256 q xp scalar1 scalar2 : leq q (2 ^ 32) ->
  NoisyLeakage.TV (@trace R 255 bound count (xp,scalar1)) (@trace R 255 bound count (xp,scalar2)) <=
    (2:R)^-66 /\
  NoisyLeakage.TV
    (NoisyLeakage.iid (@trace R 255 bound count (xp,scalar1)) q)
    (NoisyLeakage.iid (@trace R 255 bound count (xp,scalar2)) q) <= (2:R)^-34 /\
  forall (state : type.interp (C.State 255))
      (coins : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count),
    val (inord (Storage.state_HW 255 state + NoisyShares.noise_sum coins) : 'I_bound.+1) =
      (Storage.state_HW 255 state + NoisyShares.noise_sum coins)%nat.
Proof.
exact (@QuartzMaskedBudget.binomial_execution_256 R bound count [the finType of (unit : Type)] (FieldMasks 256)
  reset start (@port 255 (xp,scalar1)) (@port 255 (xp,scalar2))
  (@policy R 255) (@policy R 255) (@update 255 bound) (@update 255 bound)
  (@initial_update bound) (@initial_update bound) capacity q (fdist1 tt) (fdist1 tt)).
Qed.
End Security.

Definition curve_run n point scalar masks coins :=
  @run_ticks n C.scheduled_edges 0%nat (Curve.load point scalar) masks coins (C.initial_state n).

Lemma curve_run_matches_program n point scalar masks coins :
  @curve_run n point scalar masks coins =
  Curve.program n point scalar (randomness_at masks coins 0%nat)
    (fun k => randomness_at masks coins (Schedule.work_edges - k)%nat).
Proof. exact: run_ticks_schedule. Qed.

Theorem curve_run_canonical n point scalar masks coins :
  B.canonical n C.groups (@curve_run n point scalar masks coins).2.
Proof. exact: initialized_run_canonical. Qed.

Theorem curve_run_ready n point scalar masks coins :
  fn.interp (C.ready n) (@curve_run n point scalar masks coins) = bits.of_Z 1 1.
Proof. exact: run_ticks_ready. Qed.

Theorem curve_run_correct n point (scalar : Z) masks coins :
  Z.le 0 scalar /\ Z.lt scalar (Z.pow 2 255) ->
  C.reconstruct_group n (fn.interp (C.output n) (@curve_run n point scalar masks coins)) =
    Curve25519.M.X0 (Curve25519.M.scalarmult scalar point).
Proof.
move=> Hscalar. rewrite curve_run_matches_program.
exact (@Curve.program_correct n point scalar (randomness_at masks coins 0%nat)
  (fun k => randomness_at masks coins (Schedule.work_edges - k)%nat) Hscalar).
Qed.

Definition curve_trace (R : realType) n bound count point scalar :=
  @trace R n bound count (Curve.load point scalar).

Section CurveSecurity.
Variable R : realType.
Variables bound count : nat.
Hypothesis capacity : leq (16 + C.groups * (256 * 255) + count)%nat bound.

(* Correctness concerns the internal output. The security observation remains only the noisy HW trace. *)
Theorem ladder_correct_and_noisy_secure_256 q (point : Curve25519.M.point) (scalar1 scalar2 : Z) :
  (Z.le 0 scalar1 /\ Z.lt scalar1 (Z.pow 2 255)) ->
  (Z.le 0 scalar2 /\ Z.lt scalar2 (Z.pow 2 255)) -> leq q (2 ^ 32) ->
  (forall masks coins,
    B.canonical 255 C.groups (@curve_run 255 point scalar1 masks coins).2 /\
    C.reconstruct_group 255 (fn.interp (C.output 255) (@curve_run 255 point scalar1 masks coins)) =
      Curve25519.M.X0 (Curve25519.M.scalarmult scalar1 point) /\
    fn.interp (C.ready 255) (@curve_run 255 point scalar1 masks coins) = bits.of_Z 1 1) /\
  (forall masks coins,
    B.canonical 255 C.groups (@curve_run 255 point scalar2 masks coins).2 /\
    C.reconstruct_group 255 (fn.interp (C.output 255) (@curve_run 255 point scalar2 masks coins)) =
      Curve25519.M.X0 (Curve25519.M.scalarmult scalar2 point) /\
    fn.interp (C.ready 255) (@curve_run 255 point scalar2 masks coins) = bits.of_Z 1 1) /\
  NoisyLeakage.TV (@curve_trace R 255 bound count point scalar1)
    (@curve_trace R 255 bound count point scalar2) <= (2:R)^-66 /\
  NoisyLeakage.TV (NoisyLeakage.iid (@curve_trace R 255 bound count point scalar1) q)
    (NoisyLeakage.iid (@curve_trace R 255 bound count point scalar2) q) <= (2:R)^-34 /\
  forall (state : type.interp (C.State 255))
      (coins : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count),
    val (inord (Storage.state_HW 255 state + NoisyShares.noise_sum coins) : 'I_bound.+1) =
      (Storage.state_HW 255 state + NoisyShares.noise_sum coins)%nat.
Proof.
move=> Hscalar1 Hscalar2 Hq. split.
- move=> masks coins. split; first exact: curve_run_canonical.
  split; [exact (@curve_run_correct 255 point scalar1 masks coins Hscalar1) | exact: curve_run_ready].
split.
- move=> masks coins. split; first exact: curve_run_canonical.
  split; [exact (@curve_run_correct 255 point scalar2 masks coins Hscalar2) | exact: curve_run_ready].
exact (@ladder_trace_contract_256 R bound count capacity q
  (Curve.load point scalar1).1 (Curve.load point scalar1).2 (Curve.load point scalar2).2 Hq).
Qed.
End CurveSecurity.
End QuartzMaskedLadderSecurity.

Print Assumptions QuartzMaskedLadderSecurity.decode_encode_masks.
Print Assumptions QuartzMaskedLadderSecurity.initialized_run_canonical.
Print Assumptions QuartzMaskedLadderSecurity.run_ticks_ready.
Print Assumptions QuartzMaskedLadderSecurity.no_command_load.
Print Assumptions QuartzMaskedLadderSecurity.run_ticks_schedule.
Print Assumptions QuartzMaskedLadderSecurity.actual_run_fresh.
Print Assumptions QuartzMaskedLadderSecurity.ladder_trace_contract_256.
Print Assumptions QuartzMaskedLadderSecurity.curve_run_correct.
Print Assumptions QuartzMaskedLadderSecurity.ladder_correct_and_noisy_secure_256.
