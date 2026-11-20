From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import bigop_ext fdist.
From Masking Require Import finite_masking shared_ladder arithmetic_shares arithmetic_privacy
  noisy_leakage noisy_bit_example noisy_channel_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking NoisyLeakage SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module ArithmeticNoisySnapshot.
Section Snapshot.
Variable R : realType.
Variable K : finComNzRingType.
Variable n : nat.
Variable observe_bit : K -> bool.
Local Notation V := [the finZmodType of {ffun 'I_n.+1 -> K}].
Local Notation Noise := [the finType of 'rV[bool]_n.+1].
Local Notation View := [the finType of {ffun 'I_n.+1 -> option K}].
Local Notation Output := [the finType of {ffun 'I_n.+1 -> 'I_3}].

Definition noise_law : R.-fdist Noise :=
  (NoisyBitExample.fair R) `^ n.+1.

Definition noisy_vector (a : V) (noise : Noise) : Output :=
  [ffun i => inord (nat_of_bool (observe_bit (a i)) + nat_of_bool (noise ord0 i))].

Lemma noisy_vector_no_wrap a noise i :
  val (noisy_vector a noise i) =
    (nat_of_bool (observe_bit (a i)) + nat_of_bool (noise ord0 i))%N.
Proof.
rewrite /noisy_vector ffunE /= inordK //.
by case: (observe_bit (a i)); case: (noise ord0 i).
Qed.

Definition decode_probe (v : View) : Output :=
  [ffun i => match v i with
    | None => inord 1
    | Some x => inord (if observe_bit x then 2 else 0)
    end].

Definition flip_noise (a : V) (row : Noise) : Noise :=
  \row_i if observe_bit (a i) then row ord0 i else negb (row ord0 i).

Lemma flip_noiseK a : involutive (flip_noise a).
Proof.
move=> row. apply/rowP => i. rewrite /flip_noise !mxE.
by case: (observe_bit (a i)); rewrite ?negbK.
Qed.

Lemma noise_mass row : noise_law row = (2^-1)^+n.+1.
Proof.
rewrite /noise_law fdist_rVE.
under eq_bigr do rewrite NoisyBitExample.fair_mass.
by rewrite prodr_const card_ord.
Qed.

Lemma flip_noise_uniform a : fdistmap (flip_noise a) noise_law = noise_law.
Proof.
apply/fdist_ext => row.
rewrite fdistmapE -[row](flip_noiseK a) (big_pred1_inj (can_inj (flip_noiseK a))).
by rewrite !noise_mass.
Qed.

Lemma vector_simulation a row :
  noisy_vector a (flip_noise a row) =
  decode_probe (ArithmeticPrivacy.probe (ArithmeticPrivacy.row_flags row) a).
Proof.
apply/ffunP => i.
rewrite /noisy_vector /flip_noise /decode_probe /ArithmeticPrivacy.probe
  /ArithmeticPrivacy.row_flags !ffunE mxE.
by case E: (observe_bit (a i)); case: (row ord0 i) => /=; rewrite ?E.
Qed.

Theorem fixed_shares_simulation a :
  fdistmap (noisy_vector a) noise_law =
  fdistmap (fun flags => decode_probe (ArithmeticPrivacy.probe flags a))
    (ArithmeticPrivacy.independent_flags n (NoisyBitExample.fair R)).
Proof.
rewrite -(flip_noise_uniform a) fdistmap_comp.
rewrite /ArithmeticPrivacy.independent_flags fdistmap_comp.
congr (fdistmap _ _). apply/boolp.funeqP => row. exact: vector_simulation.
Qed.

(* Arithmetic shares and the measurement noise are independently sampled. *)
Definition actual_law (s : K) : R.-fdist Output :=
  ArithmeticPrivacy.sharing_law R n s >>= (fun a => fdistmap (noisy_vector a) noise_law).

Theorem actual_channel_simulation s :
  actual_law s = fdistmap decode_probe
    (ArithmeticPrivacy.probe_law (ArithmeticPrivacy.independent_flags n (NoisyBitExample.fair R)) s).
Proof.
rewrite /actual_law /ArithmeticPrivacy.probe_law map_bind.
have H : (fun a : V => fdistmap (noisy_vector a) noise_law) =
    (fun a => fdistmap (fun flags => decode_probe (ArithmeticPrivacy.probe flags a))
      (ArithmeticPrivacy.independent_flags n (NoisyBitExample.fair R))).
  apply/boolp.funeqP => a. exact: fixed_shares_simulation.
rewrite H /fdistmap NoisyChannelBridge.bind_swap.
congr (fdistbind _ _). apply/boolp.funeqP => flags.
rewrite fdistbindA. congr (fdistbind _ _).
apply/boolp.funeqP => a. by rewrite fdist1bind.
Qed.

Theorem snapshot_TV_bound s t : TV (actual_law s) (actual_law t) <= (2^-1)^+n.+1.
Proof.
rewrite !actual_channel_simulation.
have H := ArithmeticPrivacy.simulated_channel_bound (NoisyBitExample.fair R)
  (fun v : View => fdist1 (decode_probe v)) s t.
by rewrite NoisyBitExample.fair_mass in H.
Qed.

Definition sum_observation (v : Output) : 'I_(2 * n.+1).+1 :=
  inord (\sum_i (val (v i)))%N.

Lemma sum_observation_no_wrap v :
  val (sum_observation v) = (\sum_i val (v i))%N.
Proof.
rewrite /sum_observation /= inordK // ltnS.
have H : (\sum_i val (v i) <= \sum_(i : 'I_n.+1) 2)%N.
  apply: leq_sum => i _. by rewrite -ltnS; exact: ltn_ord.
by rewrite sum_nat_const card_ord mulnC in H.
Qed.

Lemma aggregate_value a noise :
  val (sum_observation (noisy_vector a noise)) =
    ((\sum_i nat_of_bool (observe_bit (a i))) + (\sum_i nat_of_bool (noise ord0 i)))%N.
Proof.
rewrite sum_observation_no_wrap.
under eq_bigr do rewrite noisy_vector_no_wrap.
by rewrite big_split.
Qed.

Definition aggregate_law s :=
  fdistmap sum_observation (actual_law s).

Theorem aggregate_channel_equality s :
  aggregate_law s = ArithmeticPrivacy.sharing_law R n s >>= (fun a =>
    fdistmap (fun noise : Noise =>
      (inord ((\sum_i nat_of_bool (observe_bit (a i))) +
        (\sum_i nat_of_bool (noise ord0 i)))) : 'I_(2 * n.+1).+1) noise_law).
Proof.
rewrite /aggregate_law /actual_law map_bind.
congr (fdistbind _ _). apply/boolp.funeqP => a.
rewrite fdistmap_comp. congr (fdistmap _ _). apply/boolp.funeqP => noise.
rewrite /comp /sum_observation.
under eq_bigr do rewrite noisy_vector_no_wrap.
by rewrite big_split.
Qed.

Theorem aggregate_TV_bound s t :
  TV (aggregate_law s) (aggregate_law t) <= (2^-1)^+n.+1.
Proof.
apply: le_trans (channel_TV_contraction (actual_law s) (actual_law t)
  (fun v => fdist1 (sum_observation v))) _.
exact: snapshot_TV_bound.
Qed.

End Snapshot.

(* Canonical F3 encodings are 00, 01, and 10. This Boolean HW property is field-specific. *)
Definition F3 := [the finComNzRingType of 'Z_3].
Definition F3_observer (x : F3) : bool := x != 0.
Definition F3_binary_HW (x : F3) : nat :=
  (nat_of_bool (odd (val x)) + nat_of_bool (odd (val x %/ 2)))%N.

Lemma F3_HW_correct x : F3_binary_HW x = nat_of_bool (F3_observer x).
Proof. case: x => -[|[|[|i]]] // H; by vm_compute. Qed.

Corollary F3_snapshot_bound (R : realType) n (s t : F3) :
  TV (actual_law R n F3_observer s) (actual_law R n F3_observer t) <= (2^-1)^+n.+1.
Proof. exact: snapshot_TV_bound. Qed.

Corollary F3_aggregate_bound (R : realType) n (s t : F3) :
  TV (aggregate_law R n F3_observer s) (aggregate_law R n F3_observer t) <= (2^-1)^+n.+1.
Proof. exact: aggregate_TV_bound. Qed.

End ArithmeticNoisySnapshot.

Print Assumptions ArithmeticNoisySnapshot.actual_channel_simulation.
Print Assumptions ArithmeticNoisySnapshot.snapshot_TV_bound.
Print Assumptions ArithmeticNoisySnapshot.aggregate_channel_equality.
Print Assumptions ArithmeticNoisySnapshot.F3_HW_correct.
Print Assumptions ArithmeticNoisySnapshot.F3_aggregate_bound.
