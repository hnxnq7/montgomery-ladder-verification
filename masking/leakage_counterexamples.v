From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking word_masking shared_ladder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.

Module LeakageCounterexamples.

Local Notation bit := (WordMasking.word 0).
Local Notation K := [the finZmodType of bit].

(* Exhaustive masks: each entry has probability 1/2; each mask pair has 1/4. *)
Definition masks : seq bit :=
  enum bit.
Definition pairs : seq (bit * bit) :=
  allpairs pair masks masks.

Lemma masks_size : size masks = 2%N.
Proof. rewrite /masks !enum_ordSl enum_ord0. by vm_compute. Qed.

Lemma pairs_size : size pairs = 4%N.
Proof. rewrite /pairs /masks !enum_ordSl enum_ord0. by vm_compute. Qed.

(* For one-bit words, the unsigned value is exactly the Hamming weight. *)
Definition combined_hw (s r : bit) : nat :=
  (val (split s r).1 + val (split s r).2)%N.

Lemma combined_hw_copies :
  map (combined_hw 0) masks = [:: 0; 2]%N /\
  map (combined_hw 1) masks = [:: 1; 1]%N.
Proof. rewrite /masks !enum_ordSl enum_ord0. by vm_compute. Qed.

Lemma combined_hw_distinguishes :
  count (fun r => combined_hw 0 r == 1%N) masks = 0%N /\
  count (fun r => combined_hw 1 r == 1%N) masks = 2%N.
Proof. rewrite /masks !enum_ordSl enum_ord0. by vm_compute. Qed.

(* This sum occurs in raw_mul before the third product and output refresh. *)
Definition cross_sum (a b : shares K) : bit :=
  a.1 * b.2 + a.2 * b.1.

Lemma raw_mul_second a b :
  (SharedLadder.raw_mul a b).2 = cross_sum a b + a.2 * b.2.
Proof. reflexivity. Qed.

Definition independent_cross (s t : bit) (rs : bit * bit) : bit :=
  cross_sum (split s rs.1) (split t rs.2).

Lemma independent_cross_counts :
  count (fun rs => independent_cross 0 0 rs == 1) pairs = 0%N /\
  count (fun rs => independent_cross 1 1 rs == 1) pairs = 2%N.
Proof. rewrite /pairs /masks !enum_ordSl enum_ord0. by vm_compute. Qed.

Lemma raw_mul_second_counts :
  count (fun rs => (SharedLadder.raw_mul (split (0 : bit) rs.1) (split 0 rs.2)).2 == 1)
    pairs = 1%N /\
  count (fun rs => (SharedLadder.raw_mul (split (1 : bit) rs.1) (split 1 rs.2)).2 == 1)
    pairs = 3%N.
Proof. rewrite /pairs /masks !enum_ordSl enum_ord0. by vm_compute. Qed.

(* Squaring reuses the same sharing, so its two inputs are correlated. *)
Definition square_cross (s r : bit) : bit :=
  (split s r).1 * (split s r).2.

Lemma square_cross_counts :
  count (fun r => square_cross 0 r == 1) masks = 1%N /\
  count (fun r => square_cross 1 r == 1) masks = 0%N.
Proof. rewrite /masks !enum_ordSl enum_ord0. by vm_compute. Qed.

Section Temporal.
Variable R : realType.

(* The pair records observations at two times, not two simultaneous probes. *)
Definition temporal_trace (s : bit) :=
  share_distribution R s.

Lemma temporal_marginals_uniform s :
  fdistmap fst (temporal_trace s) = uniform R K /\
  fdistmap snd (temporal_trace s) = uniform R K.
Proof. split; [exact: first_share_uniform | exact: second_share_uniform]. Qed.

Lemma temporal_joint_distinguishes : temporal_trace 0 <> temporal_trace 1.
Proof.
move/both_shares_reveal => /eqP.
by rewrite eq_sym oner_eq0.
Qed.

(* A fresh output mask still hides Y, despite the preceding counterexamples. *)
Lemma final_y_uniform a b :
  fdistmap (fun r : bit => (SharedLadder.shared_mul a b r).2) (uniform R K) = uniform R K.
Proof. exact: SharedLadder.shared_mul_output_uniform. Qed.

End Temporal.
End LeakageCounterexamples.

Print Assumptions LeakageCounterexamples.combined_hw_distinguishes.
Print Assumptions LeakageCounterexamples.independent_cross_counts.
Print Assumptions LeakageCounterexamples.square_cross_counts.
Print Assumptions LeakageCounterexamples.temporal_joint_distinguishes.
