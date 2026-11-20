From Stdlib Require Import ZArith Bits Lia Vector List.
From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import masked_arithmetic masked_bank masked_controller masked_controller_storage.
From Masking Require Import finite_masking shared_ladder fiat_field arithmetic_bank_refresh
  quartz_masked_hw quartz_masked_bank_security curve_snapshot curve_bank_bound curve_bank_history
  trace_masking history_semantics noisy_leakage noisy_trace noisy_shares noisy_channel_bridge.
From Crypto Require Import Spec.ModularArithmetic Arithmetic.ModularArithmeticTheorems.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module QuartzMaskedExecution.
Module M := MaskedArithmetic.
Module B := MaskedBank.
Module C := MaskedController.
Module Storage := MaskedControllerStorage.
Module Bridge := QuartzMaskedBankSecurity.
Local Notation K := FiatField.curve25519.

Lemma vector_ext t k (a b : Vector.t (type.interp t) k) :
  (forall i : 'I_k, @M.read t k a (val i) = @M.read t k b (val i)) -> a = b.
Proof.
  revert b. induction a as [|x k a IH]; intros b H.
  - symmetry. exact: Vector.nil_spec.
  - rewrite (Vector.eta b) in H |- *.
    have Hhead := H ord0.
    change (x = Vector.hd b) in Hhead. rewrite Hhead. f_equal. apply IH => i.
    exact: (H (lift ord0 i)).
Qed.
Print Assumptions vector_ext.

Lemma encode_decode_word w : QuartzMaskedHW.canonical w -> Bridge.encode_word (M.decode_word w) = w.
Proof.
  move=> Hw. apply Zmod.unsigned_inj.
  rewrite Bridge.encode_word_unsigned.
  exact: QuartzMaskedHW.decode_canonical Hw.
Qed.

Definition Bank n := [the finType of {ffun 'I_C.groups -> {ffun 'I_n.+1 -> K}}].

Definition encode_bank n (a : Bank n) : type.interp (C.Bank n) :=
  Bridge.tabulate (M.Shares (S n)) C.groups (fun i =>
    Bridge.tabulate M.Word (S n) (fun j => Bridge.encode_word (a i j))).

Theorem decode_encode n (a : Bank n) : B.decode n C.groups (encode_bank a) = a.
Proof.
  apply/ffunP => i; apply/ffunP => j.
  by rewrite /B.decode /M.decode /encode_bank !ffunE !Bridge.read_tabulate Bridge.encode_word_decode.
Qed.

Theorem encode_canonical n (a : Bank n) : B.canonical n C.groups (encode_bank a).
Proof.
  move=> i j. rewrite /encode_bank !Bridge.read_tabulate.
  exact: Bridge.encode_word_canonical.
Qed.

Theorem encode_decode n (a : type.interp (C.Bank n)) : B.canonical n C.groups a ->
  encode_bank (B.decode n C.groups a) = a.
Proof.
  move=> Ha. apply: (@vector_ext (M.Shares n.+1) C.groups) => i.
  apply: (@vector_ext M.Word n.+1) => j.
  rewrite /encode_bank !Bridge.read_tabulate /B.decode /M.decode !ffunE.
  exact: encode_decode_word (Ha i j).
Qed.

Section Execution.
Variable R : realType.
Variable n : nat.
Variables H A O : finType.
(* H is external policy memory, not observed Quartz storage. Only the O trace is released. *)
Local Notation S := [the finType of (Bank n * H)%type].
Variable reset start : nat -> bits 1.
Variable initial_control : type.interp C.Control.
Variable channel : nat -> nat -> R.-fdist O.

Fixpoint control_at time : type.interp C.Control :=
  if time is k.+1 then fn.interp C.next_control (control_at k,(reset k,start k)) else initial_control.

Definition raw_state time (s : S) : type.interp (C.State n) :=
  (control_at time, encode_bank s.1).

Variable port : A -> (type.interp C.Load * type.interp (M.Masks n.+1))%type.
Variable policy : nat -> S -> R.-fdist A.
Variable update : nat -> H -> A -> O -> H.

Definition command time a : type.interp C.Commands :=
  (reset time,(start time,(port a).1)).

Definition input time (raw : type.interp (C.State n)) a (r : Bridge.FieldCoins n C.groups) :
    type.interp (C.Input n) :=
  (raw,(command time a,((port a).2,Bridge.encode_coins r))).

Definition next_raw time raw a r := fn.interp (C.tick n) (input time raw a r).

Definition prepared_bank time (s : S) a : type.interp (C.Bank n) :=
  fn.interp (C.prepare_bank n) (raw_state time s,(command time a,(port a).2)).

Lemma prepared_canonical time s a : B.canonical n C.groups (prepared_bank time s a).
Proof. apply: C.prepare_bank_canonical. exact: encode_canonical. Qed.

Lemma next_control_exact time raw a r : raw.1 = control_at time ->
  (next_raw time raw a r).1 = control_at time.+1.
Proof.
  move=> Hcontrol. rewrite /next_raw C.tick_public_control /input /command /= Hcontrol. reflexivity.
Qed.

Lemma next_canonical time raw a r : B.canonical n C.groups raw.2 ->
  B.canonical n C.groups (next_raw time raw a r).2.
Proof. exact (C.tick_preserves_canonical n (input time raw a r)). Qed.

Lemma next_factorization time s a r :
  next_raw time (raw_state time s) a r =
  (control_at time.+1, fn.interp (B.refresh n C.groups) (prepared_bank time s a,Bridge.encode_coins r)).
Proof.
  rewrite /next_raw C.tick_factorization /C.prepared /input /raw_state /command /prepared_bank.
  reflexivity.
Qed.

(* The finite memory can retain past observations. Final refresh coins are drawn after the policy. *)
Definition step time (s : S) : R.-fdist (S * O) :=
  policy time s >>= (fun a => uniform R (Bridge.FieldCoins n C.groups) >>= (fun r =>
    let out := next_raw time (raw_state time s) a r in
    channel time (Storage.state_HW n out) >>= (fun o =>
      fdist1 ((B.decode n C.groups out.2,update time s.2 a o),o)))).

Definition prepare_law time (s : S) : R.-fdist (Bank n) :=
  fdistmap (fun a => B.decode n C.groups (prepared_bank time s a)) (policy time s).

Definition bank_channel time h := channel time (Storage.control_HW (control_at time.+1) + h)%nat.

Lemma observe_pair (d : R.-fdist O) (f : O -> S) :
  fdistmap snd (d >>= (fun o => fdist1 (f o,o))) = d.
Proof.
  change (fdistmap snd (fdistmap (fun o => (f o,o)) d) = d).
  rewrite fdistmap_comp. exact: fdistmap_id.
Qed.

Lemma step_emission time s : fdistmap snd (step time s) =
  prepare_law time s >>= CurveBankBound.refreshed_law (bank_channel time).
Proof.
  rewrite /step /prepare_law map_bind bind_map.
  congr (fdistbind (policy time s) _); apply/boolp.funeqP => a.
  rewrite map_bind.
  transitivity (Bridge.refreshed_law (bank_channel time) (prepared_bank time s a)).
  - congr (fdistbind _ _); apply/boolp.funeqP => r.
    rewrite next_factorization /= observe_pair. reflexivity.
  - apply: Bridge.refreshed_lawE. exact: prepared_canonical.
Qed.

Local Opaque next_raw.

Fixpoint finite_run fuel time (s : S) : R.-fdist (MaskingTrace.trace_type O fuel) :=
  match fuel with
  | Datatypes.O => fdist1 tt
  | Datatypes.S k => step time s >>= (fun so =>
      fdistmap (fun tr => (so.2,tr)) (finite_run k time.+1 so.1))
  end.

(* The raw interpreter retains the actual Quartz state between clocks. *)
Fixpoint actual_run fuel time (raw : type.interp (C.State n)) (memory : H) :
    R.-fdist (MaskingTrace.trace_type O fuel) :=
  match fuel with
  | Datatypes.O => fdist1 tt
  | Datatypes.S k => policy time (B.decode n C.groups raw.2,memory) >>= (fun a =>
      uniform R (Bridge.FieldCoins n C.groups) >>= (fun r =>
      let out := next_raw time raw a r in
      channel time (Storage.state_HW n out) >>= (fun o =>
      fdistmap (fun tr => (o,tr)) (actual_run k time.+1 out (update time memory a o)))))
  end.

Lemma raw_state_roundtrip time raw memory : raw.1 = control_at time -> B.canonical n C.groups raw.2 ->
  raw_state time (B.decode n C.groups raw.2,memory) = raw.
Proof.
  case: raw => c a /= Hc Ha. rewrite /raw_state /= (encode_decode Ha) Hc. reflexivity.
Qed.

Theorem actual_run_correspondence fuel time raw memory :
  raw.1 = control_at time -> B.canonical n C.groups raw.2 ->
  actual_run fuel time raw memory = finite_run fuel time (B.decode n C.groups raw.2,memory).
Proof.
  elim: fuel time raw memory => [|fuel IH] time raw memory Hc Ha; first reflexivity.
  cbn [actual_run finite_run]. rewrite /step (raw_state_roundtrip memory Hc Ha) !fdistbindA.
  congr (fdistbind _ _); apply/boolp.funeqP => a.
  rewrite fdistbindA.
  congr (fdistbind _ _); apply/boolp.funeqP => r.
  rewrite fdistbindA.
  congr (fdistbind _ _); apply/boolp.funeqP => o.
  rewrite fdist1bind /=. congr (fdistmap _ _).
  apply: IH; [exact: next_control_exact Hc | exact: next_canonical Ha].
Qed.

Definition timed_step horizon k := step (horizon - k.+1)%nat.

Lemma finite_run_countdown fuel horizon (s : S) : Nat.le fuel horizon ->
  finite_run fuel (horizon - fuel)%nat s = MaskingTrace.run (timed_step horizon) fuel s.
Proof.
  elim: fuel horizon s => [|fuel IH] horizon s Hle; first reflexivity.
  cbn [finite_run MaskingTrace.run timed_step].
  congr (fdistbind _ _); apply/boolp.funeqP => so.
  congr (fdistmap _ _).
  have E : (horizon - fuel.+1).+1 = (horizon - fuel)%nat.
    apply: subnSK. apply/ltP. exact Hle.
  rewrite E. apply IH. lia.
Qed.

Definition execution T (prior : R.-fdist S) :=
  prior >>= (fun s => actual_run T 0%nat (raw_state 0%nat s) s.2).

Lemma executionE T prior : execution T prior = prior >>= finite_run T 0%nat.
Proof.
  rewrite /execution. congr (fdistbind prior _); apply/boolp.funeqP => -[a memory].
  have E := @actual_run_correspondence T 0%nat (raw_state 0%nat (a,memory)) memory
    erefl (encode_canonical a).
  by rewrite E /raw_state /= decode_encode.
Qed.

End Execution.

Section Security.
Variable R : realType.
Variable n : nat.
Variables H A O : finType.
Local Notation S := [the finType of (Bank n * H)%type].
Variables reset start : nat -> bits 1.
Variable initial_control : type.interp C.Control.
Variable channel : nat -> nat -> R.-fdist O.
Variables port1 port2 : A -> (type.interp C.Load * type.interp (M.Masks n.+1))%type.
Variables policy1 policy2 : nat -> S -> R.-fdist A.
Variables update1 update2 : nat -> H -> A -> O -> H.
Variable epsilon : R.
Hypothesis shares : leq 1 n.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
Hypothesis budget : @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2.

Local Notation run1 := (@finite_run R n H A O reset start initial_control channel port1 policy1 update1).
Local Notation run2 := (@finite_run R n H A O reset start initial_control channel port2 policy2 update2).
Local Notation step1 := (@timed_step R n H A O reset start initial_control channel port1 policy1 update1).
Local Notation step2 := (@timed_step R n H A O reset start initial_control channel port2 policy2 update2).
Local Notation prepare1 := (@prepare_law R n H A reset start initial_control port1 policy1).
Local Notation prepare2 := (@prepare_law R n H A reset start initial_control port2 policy2).
Local Notation noise_at := (@bank_channel R O reset start initial_control channel).
Local Notation cost := (C.groups%:R * epsilon).

Theorem finite_execution_bound T (d e : R.-fdist S) :
  NoisyLeakage.TV (d >>= run1 T 0%nat) (e >>= run2 T 0%nat) <= T%:R * cost.
Proof.
  have E1 : run1 T 0%nat = MaskingTrace.run (step1 T) T.
    apply/boolp.funeqP => s.
    have E := @finite_run_countdown R n H A O reset start initial_control channel port1 policy1 update1
      T T s (Nat.le_refl T).
    by rewrite subnn in E.
  have E2 : run2 T 0%nat = MaskingTrace.run (step2 T) T.
    apply/boolp.funeqP => s.
    have E := @finite_run_countdown R n H A O reset start initial_control channel port2 policy2 update2
      T T s (Nat.le_refl T).
    by rewrite subnn in E.
  rewrite E1 E2.
  have match1 k : CurveBankHistory.emission_matches (noise_at (T-k.+1)%nat)
      (step1 T k) (prepare1 (T-k.+1)%nat).
    exact: step_emission.
  have match2 k : CurveBankHistory.emission_matches (noise_at (T-k.+1)%nat)
      (step2 T k) (prepare2 (T-k.+1)%nat).
    exact: step_emission.
  have Hb := @CurveBankTimedHistory.execution_bound R [the finType of 'I_C.groups] n shares epsilon
    epsilon_nonnegative budget S O (fun k => noise_at (T-k.+1)%nat)
    (step1 T) (step2 T) (fun k => prepare1 (T-k.+1)%nat) (fun k => prepare2 (T-k.+1)%nat)
    match1 match2 T d e.
  by rewrite card_ord in Hb.
Qed.

Theorem execution_bound T (d e : R.-fdist S) :
  NoisyLeakage.TV
    (@execution R n H A O reset start initial_control channel port1 policy1 update1 T d)
    (@execution R n H A O reset start initial_control channel port2 policy2 update2 T e) <= T%:R * cost.
Proof. rewrite !executionE. exact: finite_execution_bound. Qed.

End Security.

Section Initial.
Variable R : realType.
Variable n : nat.
Variables H A O : finType.
Local Notation S := [the finType of (Bank n * H)%type].
Variables reset start : nat -> bits 1.
Variable channel : nat -> nat -> R.-fdist O.
Variable initial_channel : nat -> R.-fdist O.
Variable port : A -> (type.interp C.Load * type.interp (M.Masks n.+1))%type.
Variable policy : nat -> S -> R.-fdist A.
Variable update : nat -> H -> A -> O -> H.
Variable initial_update : H -> O -> H.

(* The public power-on state is observed too, and its observation reaches the policy memory. *)
Definition initial_execution T (prior : R.-fdist H) :=
  initial_channel (Storage.state_HW n (C.initial_state n)) >>= (fun o =>
    fdistmap (fun tr => (o,tr)) (prior >>= (fun h =>
      @actual_run R n H A O reset start channel port policy update T 0%nat
        (C.initial_state n) (initial_update h o)))).

Lemma initial_tailE T prior o :
  (prior >>= (fun h => @actual_run R n H A O reset start channel port policy update T 0%nat
    (C.initial_state n) (initial_update h o))) =
  fdistmap (fun h => (B.decode n C.groups (C.initial_state n).2,initial_update h o)) prior >>=
    @finite_run R n H A O reset start (C.initial_state n).1 channel port policy update T 0%nat.
Proof.
  rewrite bind_map. congr (fdistbind prior _); apply/boolp.funeqP => h.
  exact: (@actual_run_correspondence R n H A O reset start (C.initial_state n).1 channel port policy update
    T 0%nat (C.initial_state n) (initial_update h o) erefl (C.initial_canonical n)).
Qed.
End Initial.

Section InitialSecurity.
Variable R : realType.
Variable n : nat.
Variables H A O : finType.
Local Notation S := [the finType of (Bank n * H)%type].
Variables reset start : nat -> bits 1.
Variable channel : nat -> nat -> R.-fdist O.
Variable initial_channel : nat -> R.-fdist O.
Variables port1 port2 : A -> (type.interp C.Load * type.interp (M.Masks n.+1))%type.
Variables policy1 policy2 : nat -> S -> R.-fdist A.
Variables update1 update2 : nat -> H -> A -> O -> H.
Variables initial_update1 initial_update2 : H -> O -> H.
Variable epsilon : R.
Hypothesis shares : leq 1 n.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
Hypothesis budget : @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2.
Local Notation cost := (C.groups%:R * epsilon).
Local Notation run1 := (@initial_execution R n H A O reset start channel initial_channel
  port1 policy1 update1 initial_update1).
Local Notation run2 := (@initial_execution R n H A O reset start channel initial_channel
  port2 policy2 update2 initial_update2).

Theorem initial_execution_bound T (d e : R.-fdist H) :
  NoisyLeakage.TV (run1 T d) (run2 T e) <= T%:R * cost.
Proof.
  rewrite /initial_execution. apply: NoisyTrace.bind_TV_bound => o.
  apply: le_trans (NoisyTrace.map_TV_contraction _ _ _) _.
  rewrite !initial_tailE. apply: finite_execution_bound; assumption.
Qed.

(* Repetitions are independent complete runs, not samples from one persistent execution. *)
Corollary repeated_initial_execution_bound q T (d e : R.-fdist H) :
  NoisyLeakage.TV (NoisyLeakage.iid (run1 T d) q) (NoisyLeakage.iid (run2 T e) q) <=
    q%:R * (T%:R * cost).
Proof.
  apply: le_trans (NoisyLeakage.iid_TV_bound _ _ q) _.
  apply: ler_wpM2l; first exact: ler0n.
  exact: initial_execution_bound.
Qed.
End InitialSecurity.

Theorem tick_no_clip n (p : type.interp (C.Input n)) bound count
    (noise : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count) :
  leq (16 + C.groups * (n.+1 * 255) + count)%nat bound ->
  val (inord (Storage.state_HW n (fn.interp (C.tick n) p) + NoisyShares.noise_sum noise) : 'I_bound.+1) =
    (Storage.state_HW n (fn.interp (C.tick n) p) + NoisyShares.noise_sum noise)%nat.
Proof. exact: Bridge.state_HW_no_clip. Qed.

Theorem initial_no_clip n bound count
    (noise : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count) :
  leq (16 + C.groups * (n.+1 * 255) + count)%nat bound ->
  val (inord (Storage.state_HW n (C.initial_state n) + NoisyShares.noise_sum noise) : 'I_bound.+1) =
    (Storage.state_HW n (C.initial_state n) + NoisyShares.noise_sum noise)%nat.
Proof. exact: Bridge.state_HW_no_clip. Qed.

Section Binomial.
Variable R : realType.
Variables n bound count : nat.
Variables H A : finType.
Local Notation O := [the finType of 'I_bound.+1].
Local Notation S := [the finType of (Bank n * H)%type].
Variables reset start : nat -> bits 1.
Variables port1 port2 : A -> (type.interp C.Load * type.interp (M.Masks n.+1))%type.
Variables policy1 policy2 : nat -> S -> R.-fdist A.
Variables update1 update2 : nat -> H -> A -> O -> H.
Variables initial_update1 initial_update2 : H -> O -> H.
Variable epsilon : R.
Hypothesis shares : leq 1 n.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
Hypothesis budget : @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2.
Local Notation noise := (NoisyChannelBridge.scalar_channel R bound count).
Local Notation run1 := (@initial_execution R n H A O reset start (fun _ => noise) noise
  port1 policy1 update1 initial_update1).
Local Notation run2 := (@initial_execution R n H A O reset start (fun _ => noise) noise
  port2 policy2 update2 initial_update2).
Local Notation cost := (C.groups%:R * epsilon).

(* T clocks produce T+1 samples. Each sample uses the same nonwrapping additive-noise channel. *)
Theorem binomial_execution_contract q T (d e : R.-fdist H) :
  leq (16 + C.groups * (n.+1 * 255) + count)%nat bound ->
  NoisyLeakage.TV (run1 T d) (run2 T e) <= T%:R * cost /\
  NoisyLeakage.TV (NoisyLeakage.iid (run1 T d) q) (NoisyLeakage.iid (run2 T e) q) <=
    q%:R * (T%:R * cost) /\
  forall (state : type.interp (C.State n))
      (coins : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count),
    val (inord (Storage.state_HW n state + NoisyShares.noise_sum coins) : 'I_bound.+1) =
      (Storage.state_HW n state + NoisyShares.noise_sum coins)%nat.
Proof.
  move=> Hcapacity. split; first by apply: initial_execution_bound.
  split; first by apply: repeated_initial_execution_bound.
  move=> state coins. exact: Bridge.state_HW_no_clip Hcapacity.
Qed.
End Binomial.

End QuartzMaskedExecution.

Print Assumptions QuartzMaskedExecution.encode_decode.
Print Assumptions QuartzMaskedExecution.step_emission.
Print Assumptions QuartzMaskedExecution.actual_run_correspondence.
Print Assumptions QuartzMaskedExecution.initial_execution_bound.
Print Assumptions QuartzMaskedExecution.repeated_initial_execution_bound.
Print Assumptions QuartzMaskedExecution.tick_no_clip.
Print Assumptions QuartzMaskedExecution.binomial_execution_contract.
