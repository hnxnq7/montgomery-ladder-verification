From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import ssr_ext fdist proba jfdist_cond.
From Masking Require Import finite_masking trace_masking noisy_leakage noisy_trace noisy_history_budget.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module HistorySemantics.
Section Semantics.
Variable R : realType.

Lemma dependent_product_bind (A B : finType) (d : R.-fdist A) (f : A -> R.-fdist B) :
  d `X f = d >>= (fun a => fdistmap (fun b => (a, b)) (f a)).
Proof.
apply/fdist_ext => -[a b]. rewrite fdist_prodE /= fdistbindE.
have H x : fdistmap (fun y => (x, y)) (f x) (a, b) = if x == a then f x b else 0.
  rewrite fdistmapE /=.
  under eq_bigl do rewrite !inE xpair_eqE.
  case E: (x == a); first by rewrite /= big_pred1_eq.
  by rewrite /= big_pred0.
rewrite (eq_bigr _ (fun x _ => congr1 (fun z => d x * z) (H x))).
rewrite (bigD1 a) // eqxx /=.
rewrite big1 ?addr0 // => x /negbTE Hxa.
by rewrite Hxa mulr0.
Qed.

Variables S O : finType.

Definition joint (prior : R.-fdist S) (step : S -> R.-fdist (S * O)) :=
  prior >>= step.

Definition observation (prior : R.-fdist S) (step : S -> R.-fdist (S * O)) :=
  fdist_snd (joint prior step).

Definition posterior (prior : R.-fdist S) (step : S -> R.-fdist (S * O)) (o : O) :=
  jfdist_cond (fdistX (joint prior step)) o.

Lemma posterior_zero prior step o : observation prior step o = 0 ->
  posterior prior step o = fdist_uniform (fdist_card_prednK prior).
Proof.
move=> H; rewrite /posterior jfdist_cond_dflt; last first.
  by apply/fdist_ext => s; rewrite !fdist_uniformE.
by rewrite negbK fdistX1; apply/eqP.
Qed.

Lemma posterior_nonzero prior step o s : observation prior step o != 0 ->
  posterior prior step o s = joint prior step (s, o) / observation prior step o.
Proof.
move=> H; rewrite /posterior jfdist_condE; first by rewrite fdistX1.
by rewrite /jcPr setX1 !Pr_set1 fdistXE fdistX2 fdistXE fdistX1.
Qed.

Theorem one_step_disintegration prior step :
  joint prior step = observation prior step >>= (fun o =>
    fdistmap (fun s => (s, o)) (posterior prior step o)).
Proof.
have H := fdist_prodK (fdistX (joint prior step)).
change (fdist_prod (fdist_fst (fdistX (joint prior step)))
  (fun o => posterior prior step o) = fdistX (joint prior step)) in H.
rewrite fdistX1 -/(observation prior step) dependent_product_bind in H.
have := congr1 (@fdistX R O S) H.
rewrite fdistXI /fdistX map_bind => <-.
congr (fdistbind (observation prior step) _).
by apply/boolp.funeqP => o; rewrite fdistmap_comp.
Qed.

Section History.
Variable step : nat -> S -> R.-fdist (S * O).
Variable prior : R.-fdist S.

(* Histories are newest first; n is the number of remaining steps. *)
Fixpoint history_belief (n : nat) (h : seq O) : R.-fdist S :=
  match h with
  | [::] => prior
  | o :: rest => posterior (history_belief n.+1 rest) (step n) o
  end.

Definition history_kernel n h :=
  observation (history_belief n.+1 h) (step n).

Lemma history_belief_zero n h o : history_kernel n h o = 0 ->
  history_belief n (o :: h) = fdist_uniform (fdist_card_prednK (history_belief n.+1 h)).
Proof. exact: posterior_zero. Qed.

Theorem run_from_history n h :
  history_belief n h >>= (MaskingTrace.run step n) =
  NoisyTrace.history_run history_kernel n h.
Proof.
elim: n h => [|n IH] h; first by rewrite /= bind_constant.
rewrite /= -fdistbindA.
rewrite -/(joint _ _) one_step_disintegration fdistbindA.
congr (fdistbind (observation (history_belief n.+1 h) (step n)) _).
apply/boolp.funeqP => o.
rewrite bind_map /= -map_bind.
by rewrite -(IH (o :: h)).
Qed.

Corollary execution_history_law n :
  prior >>= (MaskingTrace.run step n) = NoisyTrace.history_run history_kernel n [::].
Proof. exact: (run_from_history n [::]). Qed.

End History.

Section Budget.
Variables step1 step2 : nat -> S -> R.-fdist (S * O).
Variables prior1 prior2 : R.-fdist S.

Theorem execution_history_bound n :
  TV (prior1 >>= (MaskingTrace.run step1 n)) (prior2 >>= (MaskingTrace.run step2 n)) <=
  NoisyHistoryBudget.budget (history_kernel step1 prior1) (history_kernel step2 prior2) n [::].
Proof.
rewrite !execution_history_law.
exact: NoisyHistoryBudget.history_trace_bound.
Qed.

Corollary repeated_execution_history_bound q n :
  TV (iid (prior1 >>= (MaskingTrace.run step1 n)) q)
     (iid (prior2 >>= (MaskingTrace.run step2 n)) q) <=
  q%:R * NoisyHistoryBudget.budget (history_kernel step1 prior1) (history_kernel step2 prior2) n [::].
Proof.
rewrite !execution_history_law.
exact: NoisyHistoryBudget.repeated_history_bound.
Qed.

End Budget.

End Semantics.
End HistorySemantics.

Print Assumptions HistorySemantics.posterior_zero.
Print Assumptions HistorySemantics.one_step_disintegration.
Print Assumptions HistorySemantics.posterior_nonzero.
Print Assumptions HistorySemantics.execution_history_law.
Print Assumptions HistorySemantics.execution_history_bound.
Print Assumptions HistorySemantics.repeated_execution_history_bound.
