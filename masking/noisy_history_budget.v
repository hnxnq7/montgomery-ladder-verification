From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import noisy_leakage noisy_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory NoisyLeakage NoisyTrace.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module NoisyHistoryBudget.
Section Budget.
Variable R : realType.
Variable O : finType.
Variables k1 k2 : nat -> seq O -> R.-fdist O.

(* Weight future conditional distances by the first execution's history probabilities. *)
Fixpoint budget (n : nat) (h : seq O) : R :=
  match n with
  | 0%N => 0
  | k.+1 => TV (k1 k h) (k2 k h) + \sum_(o : O) k1 k h o * budget k (o :: h)
  end.

Theorem history_trace_bound n h :
  TV (history_run k1 n h) (history_run k2 n h) <= budget n h.
Proof.
elim: n h => [|n IH] h; first by rewrite /= TV_self.
rewrite /=.
set hybrid := k1 n h >>= (fun o =>
  fdistmap (fun t => (o, t)) (history_run k2 n (o :: h))).
apply: le_trans (TV_triangle _ hybrid _) _.
rewrite [TV (k1 n h) _ + _]addrC.
apply: lerD; last exact: channel_TV_contraction.
apply: le_trans (bind_TV_kernel _ _ _) _.
apply: ler_sum => o _.
apply: ler_wpM2l; first exact: FDist.ge0.
exact: le_trans (map_TV_contraction _ _ (fun t => (o, t))) (IH (o :: h)).
Qed.

Corollary repeated_history_bound q n h :
  TV (iid (history_run k1 n h) q) (iid (history_run k2 n h) q) <= q%:R * budget n h.
Proof.
apply: le_trans (iid_TV_bound _ _ q) _.
apply: ler_wpM2l; first by rewrite ler0n.
exact: history_trace_bound.
Qed.

(* A familiar uniform bound is one way, but not the only way, to bound this budget. *)
Lemma uniform_budget epsilon :
  (forall n h, TV (k1 n h) (k2 n h) <= epsilon) ->
  forall n h, budget n h <= n%:R * epsilon.
Proof.
move=> H; elim=> [|n IH] h; first by rewrite /= mul0r.
rewrite /= -natr1 mulrDl mul1r [n%:R * epsilon + epsilon]addrC.
apply: lerD; first exact: H.
rewrite -[n%:R * epsilon]mul1r -(FDist.f1 (k1 n h)) big_distrl /=.
apply: ler_sum => o _.
apply: ler_wpM2l; first exact: FDist.ge0.
by rewrite FDist.f1; exact: (IH (o :: h)).
Qed.

End Budget.
End NoisyHistoryBudget.

Print Assumptions NoisyHistoryBudget.history_trace_bound.
Print Assumptions NoisyHistoryBudget.repeated_history_bound.
