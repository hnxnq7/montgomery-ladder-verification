From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist variation_dist.
From Masking Require Import noisy_leakage noisy_bit_example noisy_shares.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module NoisyWords.

Definition word_type (w : nat) : finType :=
  repetitions_type [the finType of (bool : Type)] w.

Section IndependentBits.
Variable R : realType.
Variable O : finType.
Variable bit_law : bool -> R.-fdist O.

(* Independence is across bits in this snapshot, not across time. *)
Fixpoint word_law (w : nat) : word_type w -> R.-fdist (repetitions_type O w) :=
  match w as n return word_type n -> R.-fdist (repetitions_type O n) with
  | 0 => fun _ => fdist1 tt
  | n.+1 => fun bits => (bit_law bits.1) `x (@word_law n bits.2)
  end.
Arguments word_law w _ : clear implicits.

Lemma product_TV_bound (A B : finType) (d e : R.-fdist A) (p q : R.-fdist B) :
  TV (d `x p) (e `x q) <= TV d e + TV p q.
Proof.
rewrite /TV -mulrDl.
apply: ler_pM; try exact: pos_var_dist; try exact: product_L1_bound.
- by rewrite invr_ge0 ler0n.
- exact: lexx.
Qed.

Theorem word_TV_bound epsilon :
  (forall b1 b2, TV (bit_law b1) (bit_law b2) <= epsilon) ->
  forall w (x y : word_type w),
    TV (word_law w x) (word_law w y) <= w%:R * epsilon.
Proof.
move=> H. elim=> [|w IH] x y.
- by rewrite /= TV_self mul0r.
- case: x => x xs. case: y => y ys.
  apply: le_trans (product_TV_bound _ _ _ _) _.
  rewrite -nat1r mulrDl mul1r.
  exact: lerD (H x y) (IH xs ys).
Qed.

Theorem word_channel_bound epsilon :
  (forall b1 b2, TV (bit_law b1) (bit_law b2) <= epsilon) ->
  forall w (x y : word_type w) (B : finType)
    (channel : repetitions_type O w -> R.-fdist B),
    TV (apply_channel (word_law w x) channel) (apply_channel (word_law w y) channel) <=
      w%:R * epsilon.
Proof.
move=> H w x y B channel.
apply: le_trans (channel_TV_contraction _ _ channel) _.
exact: (@word_TV_bound epsilon H w x y).
Qed.

Lemma word_zero_TV (x y : word_type 0) :
  TV (word_law 0 x) (word_law 0 y) = 0.
Proof. by rewrite /= TV_self. Qed.

End IndependentBits.

Section SharedBits.
Variable R : realType.

Definition fine_word_law (d w : nat) (bits : word_type w) :=
  @word_law R (NoisyShares.fine_type d) (NoisyShares.fine_law R d) w bits.

Theorem fine_word_TV_bound d w (x y : word_type w) :
  TV (fine_word_law d x) (fine_word_law d y) <= w%:R * (2^-1)^+d.+1.
Proof.
exact: (@word_TV_bound R _ _ _ (NoisyShares.fine_bound R d) w x y).
Qed.

(* A width specialization, not a claim about a Curve25519 execution. *)
Corollary fine_word_255_TV_bound d (x y : word_type 255) :
  TV (fine_word_law d x) (fine_word_law d y) <= 255%:R * (2^-1)^+d.+1.
Proof. exact: fine_word_TV_bound. Qed.

Theorem fine_word_channel_bound d w (x y : word_type w) (B : finType)
    (channel : repetitions_type (NoisyShares.fine_type d) w -> R.-fdist B) :
  TV (apply_channel (fine_word_law d x) channel) (apply_channel (fine_word_law d y) channel) <=
    w%:R * (2^-1)^+d.+1.
Proof.
apply: le_trans (channel_TV_contraction _ _ channel) _.
exact: fine_word_TV_bound.
Qed.

Fixpoint fine_word_sum (d w : nat) : repetitions_type (NoisyShares.fine_type d) w -> nat :=
  match w as n return repetitions_type (NoisyShares.fine_type d) n -> nat with
  | O => fun _ => 0%N
  | S n => fun p => (NoisyShares.fine_sum p.1 + @fine_word_sum d n p.2)%N
  end.
Arguments fine_word_sum d w _ : clear implicits.

Lemma fine_word_sum_bound d w (x : repetitions_type (NoisyShares.fine_type d) w) :
  (fine_word_sum d w x <= 2 * d.+1 * w)%N.
Proof.
elim: w x => [|w IH] x; first by rewrite /= muln0.
case: x => h tail.
change (NoisyShares.fine_sum h + fine_word_sum d w tail <= 2 * d.+1 * w.+1)%N.
rewrite mulnS.
exact: leq_add (NoisyShares.fine_sum_bound h) (IH tail).
Qed.

Definition aggregate_word_value d w e (x : repetitions_type (NoisyShares.fine_type d) w)
    (noise : repetitions_type [the finType of (bool : Type)] e) :
    'I_(2 * d.+1 * w + e).+1 :=
  inord (fine_word_sum d w x + NoisyShares.noise_sum noise).

Lemma aggregate_word_no_wrap d w e (x : repetitions_type (NoisyShares.fine_type d) w) noise :
  val (@aggregate_word_value d w e x noise) =
    (fine_word_sum d w x + NoisyShares.noise_sum noise)%N.
Proof.
rewrite /aggregate_word_value /= inordK // ltnS.
exact: leq_add (fine_word_sum_bound x) (NoisyShares.noise_sum_bound noise).
Qed.

Definition aggregate_word_channel d w e (x : repetitions_type (NoisyShares.fine_type d) w) :=
  fdistmap (@aggregate_word_value d w e x) (iid (NoisyBitExample.fair R) e).

(* w*(d+1) shared bits and w*(d+1)+e independent fair noise bits in one snapshot. *)
Definition aggregate_word_law d w e (bits : word_type w) :=
  apply_channel (fine_word_law d bits) (@aggregate_word_channel d w e).

Theorem aggregate_word_TV_bound d w e (x y : word_type w) :
  TV (aggregate_word_law d e x) (aggregate_word_law d e y) <=
    w%:R * (2^-1)^+d.+1.
Proof. exact: fine_word_channel_bound. Qed.

End SharedBits.
End NoisyWords.

Print Assumptions NoisyWords.word_TV_bound.
Print Assumptions NoisyWords.word_channel_bound.
Print Assumptions NoisyWords.word_zero_TV.
Print Assumptions NoisyWords.fine_word_255_TV_bound.
Print Assumptions NoisyWords.aggregate_word_no_wrap.
Print Assumptions NoisyWords.aggregate_word_TV_bound.
