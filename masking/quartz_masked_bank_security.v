From Stdlib Require Import ZArith Bits Lia Vector List.
From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import hamming_weight masked_arithmetic masked_bank masked_controller masked_controller_storage.
From Masking Require Import finite_masking shared_ladder fiat_field arithmetic_bank_refresh
  field_aggregate_spectral curve_snapshot curve_bank_bound quartz_masked_hw noisy_leakage field_history
  noisy_shares noisy_channel_bridge.
From Crypto Require Import Spec.ModularArithmetic Arithmetic.ModularArithmeticTheorems.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module QuartzMaskedBankSecurity.
Module M := MaskedArithmetic.
Module B := MaskedBank.
Module C := MaskedController.
Module Storage := MaskedControllerStorage.
Local Notation K := FiatField.curve25519.

Fixpoint tabulate (t : type) k : ('I_k -> type.interp t) -> Vector.t (type.interp t) k :=
  match k as count return ('I_count -> type.interp t) -> Vector.t (type.interp t) count with
  | O => fun _ => Vector.nil _
  | S n => fun f => Vector.cons _ (f ord0) n (@tabulate t n (fun i => f (lift ord0 i)))
  end.
Arguments tabulate t k _ : clear implicits.

Lemma read_tabulate t k f (i : 'I_k) : @M.read t k (tabulate t k f) (val i) = f i.
Proof.
  elim: k f i => [f i|k IH f i].
  - case: i => i Hi. exfalso. by move: Hi; rewrite ltn0.
  - case: (unliftP ord0 i) => [j ->|->]; last reflexivity.
    change (@M.read t k (tabulate t k (fun j => f (lift ord0 j))) (val j) = f (lift ord0 j)).
    exact: IH.
Qed.

Definition vector_sum t k (f : type.interp t -> nat) (a : Vector.t (type.interp t) k) :=
  List.fold_right (fun x acc => (f x + acc)%nat) 0%nat (Vector.to_list a).

Lemma vector_sumE t k f (a : Vector.t (type.interp t) k) :
  vector_sum f a = \sum_(i : 'I_k) f (@M.read t k a (val i)).
Proof.
  induction a as [|h k rest IH]; first by rewrite big_ord0.
  rewrite big_ord_recl.
  change ((f h + vector_sum f rest)%nat = (f h + \sum_(i : 'I_k) f (@M.read t k rest (val i)))%nat).
  by rewrite IH.
Qed.

Lemma word_bank_sum k (a : Vector.t (bits 255) k) :
  RegisterHW.bank_HW a = \sum_(i : 'I_k) RegisterHW.word_HW (@M.read M.Word k a (val i)).
Proof.
  transitivity (@vector_sum M.Word k RegisterHW.word_HW a); last exact: vector_sumE.
  by induction a; simpl; rewrite ?IHa.
Qed.

Definition raw_HW n groups (a : type.interp (B.Bank n groups)) :=
  @vector_sum (M.Shares (S n)) groups RegisterHW.bank_HW a.

Theorem raw_HW_decode n groups a : B.canonical n groups a ->
  raw_HW a = CurveBankBound.bank_HW (B.decode n groups a).
Proof.
  move=> Ha. rewrite /raw_HW vector_sumE /CurveBankBound.bank_HW /CurveBankBound.observation_sum.
  apply: eq_bigr => i _.
  rewrite /CurveBankBound.group_observations ffunE FieldAggregateSpectral.observe_value.
  rewrite word_bank_sum /FieldAggregateSpectral.total_HW.
  apply: eq_bigr => j _.
  rewrite /FieldAggregateSpectral.hw /B.decode /M.decode !ffunE.
  apply: QuartzMaskedHW.word_HW_decode. exact: Ha i j.
Qed.

Definition encode_word (x : K) : bits 255 :=
  bits.of_Z 255 (F.to_Z x).

Lemma encode_word_unsigned x : Zmod.unsigned (encode_word x) = F.to_Z x.
Proof.
  apply bits.unsigned_of_Z_small.
  have Hx := F.to_Z_range x (Pos2Z.is_pos FiatField.curve25519_modulus).
  have Hp : (Z.pos FiatField.curve25519_modulus < 2 ^ 255)%Z by vm_compute.
  lia.
Qed.

Lemma encode_word_decode x : M.decode_word (encode_word x) = x.
Proof. rewrite /M.decode_word encode_word_unsigned. exact: FiatField.encode_to_Z. Qed.

Lemma encode_word_canonical x : QuartzMaskedHW.canonical (encode_word x).
Proof.
  rewrite /QuartzMaskedHW.canonical encode_word_unsigned.
  exact: F.to_Z_range (Pos2Z.is_pos FiatField.curve25519_modulus).
Qed.

Definition FieldCoins n groups := [the finZmodType of {ffun 'I_groups -> {ffun 'I_n -> K}}].

Definition encode_coins n groups (r : FieldCoins n groups) : type.interp (B.Coins n groups) :=
  tabulate (M.Shares n) groups (fun i => tabulate M.Word n (fun j => encode_word (r i j))).

Theorem decode_coins_encode n groups (r : FieldCoins n groups) :
  B.decode_coins n groups (encode_coins r) = r.
Proof.
  apply/ffunP => i; apply/ffunP => j.
  by rewrite /B.decode_coins /M.decode /encode_coins !ffunE !read_tabulate encode_word_decode.
Qed.

Theorem encode_coins_canonical n groups (r : FieldCoins n groups) (i : 'I_groups) (j : 'I_n) :
  QuartzMaskedHW.canonical
    (@M.read M.Word n (@M.read (M.Shares n) groups (encode_coins r) (val i)) (val j)).
Proof. rewrite /encode_coins !read_tabulate. exact: encode_word_canonical. Qed.

Theorem refresh_HW n groups a (r : FieldCoins n groups) : B.canonical n groups a ->
  raw_HW (fn.interp (B.refresh n groups) (a,encode_coins r)) =
  CurveBankBound.bank_HW (ArithmeticBankRefresh.refresh (B.decode n groups a) r).
Proof.
  move=> Ha.
  have Hcanonical := B.refresh_canonical n groups a (encode_coins r) Ha.
  by rewrite (raw_HW_decode Hcanonical) B.refresh_refines decode_coins_encode.
Qed.

Lemma raw_HW_bound n groups a : B.canonical n groups a ->
  leq (raw_HW a) (groups * (255*n.+1))%nat.
Proof.
  move=> Ha. rewrite (raw_HW_decode Ha).
  have H := CurveBankBound.bank_HW_bound (B.decode n groups a).
  by rewrite card_ord in H.
Qed.

Theorem binomial_refresh_no_clip n groups a (r : FieldCoins n groups) offset bound count
    (noise : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count) :
  B.canonical n groups a ->
  leq (offset + groups * (255*n.+1) + count)%nat bound ->
  let h := raw_HW (fn.interp (B.refresh n groups) (a,encode_coins r)) in
  val (inord (offset + h + NoisyShares.noise_sum noise) : 'I_bound.+1) =
    (offset + h + NoisyShares.noise_sum noise)%nat.
Proof.
  move=> Ha Hcapacity. apply: NoisyChannelBridge.scalar_channel_no_clip.
  apply: leq_trans _ Hcapacity. apply: leq_add; last exact: leqnn.
  apply: leq_add; first exact: leqnn.
  apply: raw_HW_bound. by apply: B.refresh_canonical.
Qed.

Section Laws.
Variable R : realType.
Variables n groups : nat.
Variable O : finType.
Variable channel : nat -> R.-fdist O.

(* Coins are uniform field elements, canonically encoded before the actual DSL call. *)
Definition refreshed_law (a : type.interp (B.Bank n groups)) : R.-fdist O :=
  uniform R (FieldCoins n groups) >>= (fun r =>
    channel (raw_HW (fn.interp (B.refresh n groups) (a,encode_coins r)))).

Theorem refreshed_lawE a : B.canonical n groups a ->
  refreshed_law a = CurveBankBound.refreshed_law channel (B.decode n groups a).
Proof.
  move=> Ha. rewrite /refreshed_law /CurveBankBound.refreshed_law.
  congr (fdistbind _ _); apply/boolp.funeqP => r.
  by rewrite refresh_HW.
Qed.

Variable epsilon : R.
Hypothesis shares : leq 1 n.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
Hypothesis budget : @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2.

Theorem refreshed_TV_bound a b : B.canonical n groups a -> B.canonical n groups b ->
  NoisyLeakage.TV (refreshed_law a) (refreshed_law b) <= groups%:R * epsilon.
Proof.
  move=> Ha Hb. rewrite (refreshed_lawE Ha) (refreshed_lawE Hb).
  have H := @CurveBankBound.refreshed_pair_bound R [the finType of 'I_groups] n shares epsilon
    epsilon_nonnegative budget O channel (B.decode n groups a) (B.decode n groups b).
  by rewrite card_ord in H.
Qed.

(* Priors may be correlated; fresh coins are sampled after selecting the bank. *)
Theorem arbitrary_prior_bound (X : finType) (state : X -> type.interp (B.Bank n groups))
    (d e : R.-fdist X) :
  (forall x, B.canonical n groups (state x)) ->
  NoisyLeakage.TV (d >>= (fun x => refreshed_law (state x)))
    (e >>= (fun x => refreshed_law (state x))) <= groups%:R * epsilon.
Proof.
  move=> Hcanonical. apply: FieldHistory.mixture_TV_bound => x y.
  exact: refreshed_TV_bound (Hcanonical x) (Hcanonical y).
Qed.

End Laws.

Lemma raw_HW_storage n (a : type.interp (C.Bank n)) : raw_HW a = Storage.bank_HW n a.
Proof. reflexivity. Qed.

Section StateLaws.
Variable R : realType.
Variable n : nat.
Variable O : finType.
Variable channel : nat -> R.-fdist O.

(* This is the complete stored-state observer after refresh, with fixed public control. *)
Definition state_refreshed_law (control : type.interp C.Control) (a : type.interp (C.Bank n)) : R.-fdist O :=
  uniform R (FieldCoins n 282) >>= (fun r =>
    channel (Storage.state_HW n (control, fn.interp (B.refresh n 282) (a,encode_coins r)))).

Lemma state_refreshed_lawE control a :
  state_refreshed_law control a =
    refreshed_law (fun h => channel (Storage.control_HW control + h)%nat) a.
Proof. reflexivity. Qed.

Variable epsilon : R.
Hypothesis shares : leq 1 n.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
Hypothesis budget : @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2.

Theorem state_refreshed_TV_bound control a b : B.canonical n 282 a -> B.canonical n 282 b ->
  NoisyLeakage.TV (state_refreshed_law control a) (state_refreshed_law control b) <= 282%:R * epsilon.
Proof.
  move=> Ha Hb. rewrite !state_refreshed_lawE.
  apply: refreshed_TV_bound; assumption.
Qed.

Theorem state_arbitrary_prior_bound control (X : finType) (state : X -> type.interp (C.Bank n))
    (d e : R.-fdist X) :
  (forall x, B.canonical n 282 (state x)) ->
  NoisyLeakage.TV (d >>= (fun x => state_refreshed_law control (state x)))
    (e >>= (fun x => state_refreshed_law control (state x))) <= 282%:R * epsilon.
Proof.
  move=> Hcanonical. apply: FieldHistory.mixture_TV_bound => x y.
  exact: state_refreshed_TV_bound (Hcanonical x) (Hcanonical y).
Qed.
End StateLaws.

Theorem state_HW_no_clip n (s : type.interp (C.State n)) bound count
    (noise : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count) :
  leq (16 + C.groups * (n.+1 * 255) + count)%nat bound ->
  val (inord (Storage.state_HW n s + NoisyShares.noise_sum noise) : 'I_bound.+1) =
    (Storage.state_HW n s + NoisyShares.noise_sum noise)%nat.
Proof.
  move=> Hcapacity. apply: NoisyChannelBridge.scalar_channel_no_clip.
  apply: leq_trans _ Hcapacity. apply: leq_add; last exact: leqnn.
  apply/leP. exact: Storage.state_HW_bound.
Qed.

Corollary state_refresh_no_clip n control a (r : FieldCoins n 282) bound count
    (noise : NoisyLeakage.repetitions_type [the finType of (bool : Type)] count) :
  leq (16 + C.groups * (n.+1 * 255) + count)%nat bound ->
  let h := Storage.state_HW n (control, fn.interp (B.refresh n 282) (a,encode_coins r)) in
  val (inord (h + NoisyShares.noise_sum noise) : 'I_bound.+1) = (h + NoisyShares.noise_sum noise)%nat.
Proof. exact: state_HW_no_clip. Qed.

End QuartzMaskedBankSecurity.

Print Assumptions QuartzMaskedBankSecurity.raw_HW_decode.
Print Assumptions QuartzMaskedBankSecurity.decode_coins_encode.
Print Assumptions QuartzMaskedBankSecurity.refreshed_lawE.
Print Assumptions QuartzMaskedBankSecurity.arbitrary_prior_bound.
Print Assumptions QuartzMaskedBankSecurity.state_arbitrary_prior_bound.
Print Assumptions QuartzMaskedBankSecurity.state_refresh_no_clip.
