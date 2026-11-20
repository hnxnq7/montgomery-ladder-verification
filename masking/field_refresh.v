From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.

Module FieldRefresh.

Section Refresh.
Variable R : realType.
Variable K : finZmodType.

(* Equality of complete output-pair laws; observing both shares still reveals their sum. *)
Theorem refresh_pair_law (a : shares K) :
  fdistmap (refresh a) (uniform R K) = share_distribution R (reconstruct a).
Proof.
have E : refresh a = split (reconstruct a) \o (fun r => a.1 + r).
  apply/boolp.funeqP => r.
  by rewrite /refresh /split /reconstruct /= opprD addrACA subrr add0r.
rewrite E -fdistmap_comp uniform_add.
reflexivity.
Qed.

End Refresh.

Section Operations.
Variable R : realType.
Variable K : finComNzRingType.
Local Notation reconstruct := (@FiniteMasking.reconstruct K).

Theorem shared_add_pair_law (a b : shares K) :
  fdistmap (SharedLadder.shared_add a b) (uniform R K) =
  share_distribution R (reconstruct a + reconstruct b).
Proof.
rewrite /SharedLadder.shared_add refresh_pair_law.
have H := SharedLadder.shared_add_correct a b (0 : K).
rewrite /SharedLadder.shared_add refresh_correct in H.
by rewrite H.
Qed.

Theorem shared_sub_pair_law (a b : shares K) :
  fdistmap (SharedLadder.shared_sub a b) (uniform R K) =
  share_distribution R (reconstruct a - reconstruct b).
Proof.
rewrite /SharedLadder.shared_sub refresh_pair_law.
have H := SharedLadder.shared_sub_correct a b (0 : K).
rewrite /SharedLadder.shared_sub refresh_correct in H.
by rewrite H.
Qed.

Theorem shared_mul_pair_law (a b : shares K) :
  fdistmap (SharedLadder.shared_mul a b) (uniform R K) =
  share_distribution R (reconstruct a * reconstruct b).
Proof.
rewrite /SharedLadder.shared_mul refresh_pair_law.
have H := SharedLadder.shared_mul_correct a b (0 : K).
rewrite /SharedLadder.shared_mul refresh_correct in H.
by rewrite H.
Qed.

Corollary shared_square_pair_law (a : shares K) :
  fdistmap (SharedLadder.shared_mul a a) (uniform R K) =
  share_distribution R ((reconstruct a)^+2).
Proof. by rewrite shared_mul_pair_law expr2. Qed.

Corollary shared_sub_self_pair_law (a : shares K) :
  fdistmap (SharedLadder.shared_sub a a) (uniform R K) = share_distribution R (0 : K).
Proof. by rewrite shared_sub_pair_law subrr. Qed.

Corollary sampled_add_correct (a b : shares K) :
  fdistmap reconstruct (fdistmap (SharedLadder.shared_add a b) (uniform R K)) =
  fdist1 (reconstruct a + reconstruct b).
Proof. by rewrite shared_add_pair_law reconstruction_distribution. Qed.

Corollary sampled_sub_correct (a b : shares K) :
  fdistmap reconstruct (fdistmap (SharedLadder.shared_sub a b) (uniform R K)) =
  fdist1 (reconstruct a - reconstruct b).
Proof. by rewrite shared_sub_pair_law reconstruction_distribution. Qed.

Corollary sampled_mul_correct (a b : shares K) :
  fdistmap reconstruct (fdistmap (SharedLadder.shared_mul a b) (uniform R K)) =
  fdist1 (reconstruct a * reconstruct b).
Proof. by rewrite shared_mul_pair_law reconstruction_distribution. Qed.

End Operations.
End FieldRefresh.

Print Assumptions FieldRefresh.refresh_pair_law.
Print Assumptions FieldRefresh.shared_add_pair_law.
Print Assumptions FieldRefresh.shared_sub_pair_law.
Print Assumptions FieldRefresh.shared_mul_pair_law.
Print Assumptions FieldRefresh.shared_square_pair_law.
Print Assumptions FieldRefresh.sampled_mul_correct.
