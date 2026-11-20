From mathcomp Require Import boot order algebra reals field_tactic.
From infotheo Require Import fdist variation_dist.
From Masking Require Import trace_masking noisy_leakage noisy_bit_example xor_shares
  noisy_shares noisy_channel_bridge noisy_words noisy_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory NoisyLeakage NoisyBitExample.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section Checks.
Variable R : realType.

Example zero_observations (A : finType) (d e : R.-fdist A) :
  TV (iid d 0) (iid e 0) = 0.
Proof. exact: TV_self. Qed.

Example one_observation_comparison :
  TV (plain_law R false) (plain_law R true) = 1 / 2 /\
  TV (masked_law R false) (masked_law R true) = 1 / 4 /\
  TV (dual_law R false) (dual_law R true) = 0.
Proof. split; [exact: plain_TV | split; [exact: masked_TV | exact: dual_TV]]. Qed.

Example masked_repetition_budget q :
  TV (iid (masked_law R false) q) (iid (masked_law R true) q) <= q%:R / 4.
Proof.
have H := iid_TV_bound (masked_law R false) (masked_law R true) q.
by rewrite masked_TV mulrA mulr1 in H.
Qed.

Example dual_repetition_budget q s t :
  TV (iid (dual_law R s) q) (iid (dual_law R t) q) = 0.
Proof. by rewrite (dual_laws_equal R s t) TV_self. Qed.

Example masked_all_secrets_budget q s t :
  TV (iid (masked_law R s) q) (iid (masked_law R t) q) <= q%:R / 4.
Proof.
have Hnonneg : (0 : R) <= q%:R / 4.
  apply: divr_ge0; by rewrite ler0n.
case: s; case: t; try by rewrite TV_self.
- rewrite /TV symmetric_var_dist. exact: masked_repetition_budget.
- exact: masked_repetition_budget.
Qed.

Example arbitrary_share_reconstruction d s :
  fdistmap (fun p => XorShares.reconstruct d p.1) (NoisyShares.sample R d s) = fdist1 s.
Proof. exact: NoisyShares.sample_correct. Qed.

(* Both parameter choices have eight fair noise bits in total. *)
Example fixed_noise_share_comparison s t :
  TV (NoisyShares.aggregate_law R 1 6 s) (NoisyShares.aggregate_law R 1 6 t) <= 1 / 4 /\
  TV (NoisyShares.aggregate_law R 3 4 s) (NoisyShares.aggregate_law R 3 4 t) <= 1 / 16.
Proof.
have E2 : (2^-1 : R)^+2 = 1 / 4 by rewrite expr2; field by rewrite ?pnatr_eq0.
have E4 : (2^-1 : R)^+4 = 1 / 16 by rewrite !exprS expr0; field by rewrite ?pnatr_eq0.
split.
- have H := NoisyShares.aggregate_TV_bound R 1 6 s t. by rewrite E2 in H.
- have H := NoisyShares.aggregate_TV_bound R 3 4 s t. by rewrite E4 in H.
Qed.

Example parameterized_common_bound d e s t :
  TV (NoisyShares.aggregate_law R d e s) (NoisyShares.aggregate_law R d e t) <= (2^-1)^+d.+1 /\
  TV (NoisyChannelBridge.dual_law R d e s) (NoisyChannelBridge.dual_law R d e t) <= (2^-1)^+d.+1.
Proof.
split; first exact: NoisyShares.aggregate_TV_bound.
rewrite (NoisyChannelBridge.dual_laws_equal R d e s t) TV_self.
apply: exprn_ge0. by rewrite invr_ge0 ler0n.
Qed.

Example word_255_snapshot_budget d (x y : NoisyWords.word_type 255) :
  TV (NoisyWords.fine_word_law R d x) (NoisyWords.fine_word_law R d y) <=
    255%:R * (2^-1)^+d.+1.
Proof. exact: NoisyWords.fine_word_255_TV_bound. Qed.

Example repeated_word_snapshot_budget d w q (x y : NoisyWords.word_type w) :
  TV (iid (NoisyWords.fine_word_law R d x) q) (iid (NoisyWords.fine_word_law R d y) q) <=
    q%:R * (w%:R * (2^-1)^+d.+1).
Proof.
apply: le_trans (iid_TV_bound _ _ q) _.
apply: ler_wpM2l; first by rewrite ler0n.
exact: NoisyWords.fine_word_TV_bound.
Qed.

Section PublicSchedule.
Variable S : finType.
Variable advance : nat -> S -> S.
Variable public_bit : nat -> bool.

Let step k (s : S) : R.-fdist [the finType of (S * bool)%type] :=
  fdist1 (advance k s, public_bit k).

Example changing_public_schedule n s t :
  TV (MaskingTrace.run step n s) (MaskingTrace.run step n t) <= 0.
Proof.
have Hstep k state : TV (fdistmap snd (step k state)) (fdist1 (public_bit k)) <= (0 : R).
  by rewrite /step fdistmap1 TV_self.
have H := @NoisyTrace.trace_pair_bound R S [the finType of (bool : Type)] step
  (fun k => fdist1 (public_bit k)) 0 Hstep n s t.
by rewrite mulr0 in H.
Qed.

End PublicSchedule.

Section HistorySampling.
Variable public_choice : nat -> seq 'I_5 -> bool.

(* Each step samples fresh shares, but its public choice may depend on the history. *)
Let history_kernel (s : bool) k (h : seq 'I_5) :=
  masked_law R (xorb s (public_choice k h)).

Example history_sensitive_budget n h :
  TV (NoisyTrace.history_run (history_kernel false) n h)
     (NoisyTrace.history_run (history_kernel true) n h) <= n%:R / 4.
Proof.
have Hstep k history : TV (history_kernel false k history) (history_kernel true k history) <= (1 / 4 : R).
  rewrite /history_kernel. case: (public_choice k history) => /=.
  - rewrite /TV symmetric_var_dist -/(TV (masked_law R false) (masked_law R true)).
    by rewrite masked_TV.
  - by rewrite masked_TV.
have H := @NoisyTrace.history_trace_bound R [the finType of 'I_5]
  (history_kernel false) (history_kernel true) (1 / 4) Hstep n h.
by rewrite mulrA mulr1 in H.
Qed.

End HistorySampling.

End Checks.

Print Assumptions one_observation_comparison.
Print Assumptions masked_repetition_budget.
Print Assumptions dual_repetition_budget.
Print Assumptions masked_all_secrets_budget.
Print Assumptions arbitrary_share_reconstruction.
Print Assumptions fixed_noise_share_comparison.
Print Assumptions parameterized_common_bound.
Print Assumptions word_255_snapshot_budget.
Print Assumptions repeated_word_snapshot_budget.
Print Assumptions changing_public_schedule.
Print Assumptions history_sensitive_budget.
