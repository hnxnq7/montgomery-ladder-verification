From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist variation_dist.
From Masking Require Import finite_masking trace_masking noisy_leakage noisy_trace
  noisy_history_budget history_semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory FiniteMasking NoisyLeakage HistorySemantics.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module HistorySemanticsTests.
Section Tests.
Variable R : realType.

Definition prior : R.-fdist bool := fdist1 false.

Lemma posterior_point (step : bool -> R.-fdist (bool * bool)) s t o :
  step s = fdist1 (t, o) -> posterior (fdist1 s) step o = fdist1 t.
Proof.
move=> H.
have Ho : observation (fdist1 s) step = fdist1 o.
  by rewrite /observation /joint fdist1bind H /fdist_snd fdistmap1.
apply/fdist_ext => u.
rewrite posterior_nonzero; first by rewrite Ho fdist1xx oner_neq0.
by rewrite /joint fdist1bind H Ho fdist1xx divr1 !fdist1E xpair_eqE eqxx andbT.
Qed.

Definition timed_step (n : nat) (s : bool) : R.-fdist (bool * bool) :=
  if n is 0%N then fdist1 (negb s, s) else fdist1 (true, false).

(* run emits transition observations only, not an initial-state snapshot.
   An initial observation requires a separate channel in the execution model. *)
Example no_initial_snapshot s : MaskingTrace.run timed_step 0 s = fdist1 tt.
Proof. by []. Qed.

Example countdown_execution :
  prior >>= (MaskingTrace.run timed_step 2) = fdist1 (false, (true, tt)).
Proof.
by rewrite /prior fdist1bind /= /timed_step !fdist1bind !fdistmap1.
Qed.

Example first_posterior : history_belief timed_step prior 1 [:: false] = fdist1 true.
Proof. apply: posterior_point. by []. Qed.

Example newest_first_posterior :
  history_belief timed_step prior 0 [:: true; false] = fdist1 false.
Proof.
change (posterior (history_belief timed_step prior 1 [:: false]) (timed_step 0) true = fdist1 false).
rewrite first_posterior; apply: posterior_point. by [].
Qed.

Example first_kernel : history_kernel timed_step prior 1 [::] = fdist1 false.
Proof.
by rewrite /history_kernel /= /observation /joint /prior fdist1bind
  /timed_step /fdist_snd fdistmap1.
Qed.

Example second_kernel : history_kernel timed_step prior 0 [:: false] = fdist1 true.
Proof.
by rewrite /history_kernel first_posterior /observation /joint fdist1bind
  /timed_step /fdist_snd fdistmap1.
Qed.

Example countdown_history_law :
  NoisyTrace.history_run (history_kernel timed_step prior) 2 [::] = fdist1 (false, (true, tt)).
Proof. by rewrite -execution_history_law countdown_execution. Qed.

Definition emit (b : bool) (_ : nat) (s : bool) : R.-fdist (bool * bool) :=
  fdist1 (s, b).

Lemma emit_kernel b n h : history_kernel (emit b) prior n h = fdist1 b.
Proof.
rewrite /history_kernel /observation /joint /fdist_snd map_bind.
have -> : (fun s => fdistmap snd (emit b n s)) = (fun _ : bool => fdist1 b).
  by apply/boolp.funeqP => s; rewrite /emit fdistmap1.
exact: bind_constant.
Qed.

Example asymmetric_history_support :
  history_kernel (emit true) prior 1 [::] true = 1 /\
  history_kernel (emit false) prior 1 [::] true = 0.
Proof. by rewrite !emit_kernel !fdist1E. Qed.

Example impossible_history_default :
  history_belief (emit false) prior 1 [:: true] = fdist_uniform (fdist_card_prednK prior).
Proof.
apply: history_belief_zero.
by rewrite emit_kernel fdist1E.
Qed.

Example impossible_history_default_mass :
  history_belief (emit false) prior 1 [:: true] true = (2 : R)^-1.
Proof. by rewrite impossible_history_default fdist_uniformE card_bool. Qed.

Example possible_history_posterior : history_belief (emit true) prior 1 [:: true] = prior.
Proof. apply: posterior_point. by []. Qed.

Lemma bool_diracs_TV : TV (@fdist1 R _ true) (fdist1 false) = 1.
Proof.
rewrite /TV /var_dist big_bool !fdist1E /= subr0 sub0r normrN !normr1.
change ((2 : R) / 2 = 1).
by rewrite divff // pnatr_eq0.
Qed.

Lemma asymmetric_budget n h :
  NoisyHistoryBudget.budget (history_kernel (emit true) prior)
    (history_kernel (emit false) prior) n h = n%:R.
Proof.
elim: n h => [|n IH] h; first by [].
rewrite /= !emit_kernel bool_diracs_TV.
under eq_bigr do rewrite IH.
by rewrite -big_distrl FDist.f1 /= mul1r addrC natr1.
Qed.

Example asymmetric_execution_budget :
  TV (prior >>= (MaskingTrace.run (emit true) 2))
     (prior >>= (MaskingTrace.run (emit false) 2)) <= 2.
Proof.
have H := execution_history_bound (emit true) (emit false) prior prior 2.
by rewrite asymmetric_budget in H.
Qed.

End Tests.
End HistorySemanticsTests.

Print Assumptions HistorySemanticsTests.countdown_execution.
Print Assumptions HistorySemanticsTests.newest_first_posterior.
Print Assumptions HistorySemanticsTests.countdown_history_law.
Print Assumptions HistorySemanticsTests.impossible_history_default_mass.
Print Assumptions HistorySemanticsTests.asymmetric_execution_budget.
