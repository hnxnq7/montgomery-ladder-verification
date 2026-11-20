From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking fiat_field curve_snapshot curve_bank_bound
  trace_masking history_semantics noisy_leakage noisy_trace noisy_history_budget.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module CurveBankHistory.
Section Execution.
Variable R : realType.
Variable I : finType.
Variable n : nat.
Hypothesis shares : (1 <= n)%N.
Variable epsilon : R.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
Hypothesis budget : @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2.
Variables S O : finType.
Variable channel : nat -> R.-fdist O.
Local Notation K := FiatField.curve25519.
Local Notation Bank := [the finType of {ffun I -> {ffun 'I_n.+1 -> K}}].
Local Notation refreshed := (@CurveBankBound.refreshed_law R I n O channel).
Local Notation cost := (#|I|%:R * epsilon).

(* This is an obligation on every hidden state, not merely on initial marginals. *)
Definition emission_matches (transition : S -> R.-fdist (S * O))
    (prepare : S -> R.-fdist Bank) : Prop :=
  forall s, fdistmap snd (transition s) = prepare s >>= refreshed.

Lemma observation_factorization transition prepare :
  emission_matches transition prepare -> forall prior,
  HistorySemantics.observation prior transition = (prior >>= prepare) >>= refreshed.
Proof.
  move=> H prior.
  rewrite /HistorySemantics.observation /HistorySemantics.joint /fdist_snd map_bind fdistbindA.
  congr (fdistbind prior _); apply/boolp.funeqP => s; exact: H.
Qed.

Lemma observation_bound transition1 transition2 prepare1 prepare2 :
  emission_matches transition1 prepare1 -> emission_matches transition2 prepare2 ->
  forall d e, NoisyLeakage.TV (HistorySemantics.observation d transition1)
    (HistorySemantics.observation e transition2) <= cost.
Proof.
  move=> H1 H2 d e; rewrite (observation_factorization H1) (observation_factorization H2).
  exact: (@CurveBankBound.arbitrary_prior_bound R I n shares epsilon epsilon_nonnegative budget
    O channel (d >>= prepare1) (e >>= prepare2)).
Qed.

Variables step1 step2 : nat -> S -> R.-fdist (S * O).
Variables prepare1 prepare2 : nat -> S -> R.-fdist Bank.
Hypothesis matches1 : forall k, emission_matches (step1 k) (prepare1 k).
Hypothesis matches2 : forall k, emission_matches (step2 k) (prepare2 k).

(* Countdown indices and newest-first histories are inherited from HistorySemantics. *)
Lemma history_kernel_bound d e k h :
  NoisyLeakage.TV (HistorySemantics.history_kernel step1 d k h)
    (HistorySemantics.history_kernel step2 e k h) <= cost.
Proof.
  rewrite /HistorySemantics.history_kernel.
  exact: (@observation_bound (step1 k) (step2 k) (prepare1 k) (prepare2 k)
    (matches1 k) (matches2 k)).
Qed.

Lemma history_budget_bound d e T h :
  NoisyHistoryBudget.budget (HistorySemantics.history_kernel step1 d)
    (HistorySemantics.history_kernel step2 e) T h <= T%:R * cost.
Proof.
  apply: NoisyHistoryBudget.uniform_budget => k hist.
  exact: history_kernel_bound.
Qed.

Theorem execution_bound T d e :
  NoisyLeakage.TV (d >>= MaskingTrace.run step1 T) (e >>= MaskingTrace.run step2 T) <=
    T%:R * cost.
Proof.
  apply: le_trans (HistorySemantics.execution_history_bound step1 step2 d e T) _.
  exact: history_budget_bound.
Qed.

Corollary repeated_execution_bound runs T d e :
  NoisyLeakage.TV (NoisyLeakage.iid (d >>= MaskingTrace.run step1 T) runs)
    (NoisyLeakage.iid (e >>= MaskingTrace.run step2 T) runs) <= runs%:R * (T%:R * cost).
Proof.
  apply: le_trans (HistorySemantics.repeated_execution_history_bound step1 step2 d e runs T) _.
  apply: ler_wpM2l; first exact: ler0n.
  exact: history_budget_bound.
Qed.

(* Initial, intermediate, idle, and done emissions are not filtered from this trace. *)
Definition execution_with_initial (initial : S -> R.-fdist (S * O))
    (step : nat -> S -> R.-fdist (S * O)) T (prior : R.-fdist S) :=
  prior >>= (fun s => initial s >>= (fun so =>
    fdistmap (fun tr => (so.2, tr)) (MaskingTrace.run step T so.1))).

Lemma initial_disintegration initial step T prior :
  execution_with_initial initial step T prior =
    HistorySemantics.observation prior initial >>= (fun o =>
      fdistmap (fun tr => (o, tr))
        (HistorySemantics.posterior prior initial o >>= MaskingTrace.run step T)).
Proof.
  rewrite /execution_with_initial -fdistbindA -/(HistorySemantics.joint prior initial).
  rewrite HistorySemantics.one_step_disintegration fdistbindA.
  congr (fdistbind (HistorySemantics.observation prior initial) _).
  by apply/boolp.funeqP => o; rewrite bind_map /= map_bind.
Qed.

Theorem execution_with_initial_bound initial1 initial2 prepare_initial1 prepare_initial2 :
  emission_matches initial1 prepare_initial1 -> emission_matches initial2 prepare_initial2 ->
  forall T d e,
  NoisyLeakage.TV (execution_with_initial initial1 step1 T d)
    (execution_with_initial initial2 step2 T e) <= T.+1%:R * cost.
Proof.
  move=> H1 H2 T d e; rewrite !initial_disintegration.
  set hybrid := HistorySemantics.observation d initial1 >>= (fun o =>
    fdistmap (fun tr => (o, tr))
      (HistorySemantics.posterior e initial2 o >>= MaskingTrace.run step2 T)).
  apply: le_trans (NoisyTrace.TV_triangle _ hybrid _) _.
  rewrite -natr1 mulrDl mul1r.
  apply: lerD.
  - apply: NoisyTrace.bind_TV_bound => o.
    apply: le_trans (NoisyTrace.map_TV_contraction _ _ _) _.
    exact: execution_bound.
  - apply: le_trans (NoisyLeakage.channel_TV_contraction _ _ _) _.
    exact: (@observation_bound initial1 initial2 prepare_initial1 prepare_initial2 H1 H2).
Qed.

End Execution.
End CurveBankHistory.

Print Assumptions CurveBankHistory.execution_bound.
Print Assumptions CurveBankHistory.execution_with_initial_bound.

(* Public control may change the common observation channel at each step. *)
Module CurveBankTimedHistory.
Section Execution.
Variable R : realType.
Variable I : finType.
Variable n : nat.
Hypothesis shares : (1 <= n)%N.
Variable epsilon : R.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
Hypothesis budget : @ratr R (CurveSnapshot.squared_budget n) <= epsilon^+2.
Variables S O : finType.
Variable channel : nat -> nat -> R.-fdist O.
Local Notation K := FiatField.curve25519.
Local Notation Bank := [the finType of {ffun I -> {ffun 'I_n.+1 -> K}}].
Local Notation cost := (#|I|%:R * epsilon).
Variables step1 step2 : nat -> S -> R.-fdist (S * O).
Variables prepare1 prepare2 : nat -> S -> R.-fdist Bank.
Hypothesis matches1 : forall k,
  CurveBankHistory.emission_matches (channel k) (step1 k) (prepare1 k).
Hypothesis matches2 : forall k,
  CurveBankHistory.emission_matches (channel k) (step2 k) (prepare2 k).

Lemma history_kernel_bound d e k h :
  NoisyLeakage.TV (HistorySemantics.history_kernel step1 d k h)
    (HistorySemantics.history_kernel step2 e k h) <= cost.
Proof.
  rewrite /HistorySemantics.history_kernel.
  exact: (@CurveBankHistory.observation_bound R I n shares epsilon epsilon_nonnegative budget
    S O (channel k) (step1 k) (step2 k) (prepare1 k) (prepare2 k) (matches1 k) (matches2 k)).
Qed.

Lemma history_budget_bound d e T h :
  NoisyHistoryBudget.budget (HistorySemantics.history_kernel step1 d)
    (HistorySemantics.history_kernel step2 e) T h <= T%:R * cost.
Proof.
  apply: NoisyHistoryBudget.uniform_budget => k hist.
  exact: history_kernel_bound.
Qed.

Theorem execution_bound T d e :
  NoisyLeakage.TV (d >>= MaskingTrace.run step1 T) (e >>= MaskingTrace.run step2 T) <= T%:R * cost.
Proof.
  apply: le_trans (HistorySemantics.execution_history_bound step1 step2 d e T) _.
  exact: history_budget_bound.
Qed.

Theorem repeated_execution_bound runs T d e :
  NoisyLeakage.TV (NoisyLeakage.iid (d >>= MaskingTrace.run step1 T) runs)
    (NoisyLeakage.iid (e >>= MaskingTrace.run step2 T) runs) <= runs%:R * (T%:R * cost).
Proof.
  apply: le_trans (HistorySemantics.repeated_execution_history_bound step1 step2 d e runs T) _.
  apply: ler_wpM2l; first exact: ler0n.
  exact: history_budget_bound.
Qed.

Theorem execution_with_initial_bound initial_channel initial1 initial2
    (prepare_initial1 prepare_initial2 : S -> R.-fdist Bank) :
  CurveBankHistory.emission_matches initial_channel initial1 prepare_initial1 ->
  CurveBankHistory.emission_matches initial_channel initial2 prepare_initial2 ->
  forall T d e,
  NoisyLeakage.TV (CurveBankHistory.execution_with_initial initial1 step1 T d)
    (CurveBankHistory.execution_with_initial initial2 step2 T e) <= T.+1%:R * cost.
Proof.
  move=> H1 H2 T d e; rewrite !CurveBankHistory.initial_disintegration.
  set hybrid := HistorySemantics.observation d initial1 >>= (fun o =>
    fdistmap (fun tr => (o, tr))
      (HistorySemantics.posterior e initial2 o >>= MaskingTrace.run step2 T)).
  apply: le_trans (NoisyTrace.TV_triangle _ hybrid _) _.
  rewrite -natr1 mulrDl mul1r.
  apply: lerD.
  - apply: NoisyTrace.bind_TV_bound => o.
    apply: le_trans (NoisyTrace.map_TV_contraction _ _ _) _.
    exact: execution_bound.
  - apply: le_trans (NoisyLeakage.channel_TV_contraction _ _ _) _.
    exact: (@CurveBankHistory.observation_bound R I n shares epsilon epsilon_nonnegative budget
      S O initial_channel initial1 initial2 prepare_initial1 prepare_initial2 H1 H2).
Qed.
End Execution.
End CurveBankTimedHistory.
Print Assumptions CurveBankTimedHistory.execution_bound.
Print Assumptions CurveBankTimedHistory.execution_with_initial_bound.
