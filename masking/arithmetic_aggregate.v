From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import ssr_ext bigop_ext fdist proba jfdist_cond.
From Masking Require Import finite_masking shared_ladder arithmetic_shares arithmetic_privacy
  noisy_channel_bridge history_semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory FiniteMasking SharedLadder ArithmeticPrivacy.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module ArithmeticAggregate.
Section Aggregate.
Variable R : realType.
Variable K : finComNzRingType.
Variable n : nat.
Local Notation V := [the finZmodType of {ffun 'I_n.+1 -> K}].

Lemma uniform_vector_product (r : V) :
  uniform R V r = \prod_i uniform R K (r i).
Proof.
rewrite /uniform fdist_uniformE card_ffun card_ord natrX.
under eq_bigr do rewrite fdist_uniformE.
by rewrite prodr_const card_ord exprVn.
Qed.

Lemma share_as_add s (r : V) :
  ArithmeticShares.share s r = r + single ord0 (s - ArithmeticShares.reconstruct r).
Proof. by apply/ffunP => i; rewrite /ArithmeticShares.share /single !ffunE. Qed.

Lemma uniform_secret_for_masks (r : V) :
  fdistmap (fun s => ArithmeticShares.share s r) (uniform R K) =
  fdistmap (fun d => r + single ord0 d) (uniform R K).
Proof.
rewrite -{1}(uniform_add R (ArithmeticShares.reconstruct r)) fdistmap_comp.
congr (fdistmap _ _); apply/boolp.funeqP => d.
by rewrite /= share_as_add addrAC subrr add0r.
Qed.

(* Randomizing the secret restores uniformity; fixed-secret shares remain correlated. *)
Theorem uniform_secret_mixture :
  uniform R K >>= sharing_law R n = uniform R V.
Proof.
rewrite /sharing_law /fdistmap NoisyChannelBridge.bind_swap.
change (uniform R V >>= (fun r =>
  fdistmap (fun s => ArithmeticShares.share s r) (uniform R K)) = uniform R V).
have -> : (fun r : V => fdistmap (fun s => ArithmeticShares.share s r) (uniform R K)) =
    (fun r => fdistmap (fun d => r + single ord0 d) (uniform R K)).
  by apply/boolp.funeqP => r; exact: uniform_secret_for_masks.
rewrite /fdistmap NoisyChannelBridge.bind_swap.
change (uniform R K >>= (fun d =>
  fdistmap (fun r : V => r + single ord0 d) (uniform R V)) = uniform R V).
have -> : (fun d : K => fdistmap (fun r : V => r + single ord0 d) (uniform R V)) =
    (fun _ => uniform R V).
  apply/boolp.funeqP => d.
  have -> : (fun r : V => r + single ord0 d) = (fun r => single ord0 d + r).
    by apply/boolp.funeqP => r; rewrite addrC.
  exact: uniform_add.
exact: bind_constant.
Qed.

Definition reconstruction_joint :=
  fdistmap (fun r : V => (ArithmeticShares.reconstruct r, r)) (uniform R V).

Theorem uniform_secret_joint :
  (uniform R K) `X (sharing_law R n) = reconstruction_joint.
Proof.
rewrite /reconstruction_joint -uniform_secret_mixture map_bind HistorySemantics.dependent_product_bind.
congr (fdistbind (uniform R K) _); apply/boolp.funeqP => s.
rewrite /sharing_law !fdistmap_comp.
congr (fdistmap _ _); apply/boolp.funeqP => r.
by rewrite /= ArithmeticShares.share_correct.
Qed.

Lemma reconstruction_marginal : fdist_fst reconstruction_joint = uniform R K.
Proof. by rewrite -uniform_secret_joint fdist_prod1. Qed.

Lemma secret_mass_nonzero s : uniform R K s != 0.
Proof.
rewrite /uniform fdist_uniformE invr_eq0 pnatr_eq0 -lt0n.
exact: cardinal_positive.
Qed.

Theorem sharing_law_conditional s :
  sharing_law R n s = jfdist_cond reconstruction_joint s.
Proof.
rewrite -uniform_secret_joint; apply: jfdist_cond_prod.
by rewrite fdist_prod1; exact: secret_mass_nonzero.
Qed.

Variable O : finType.
Variable observe : V -> O.

Definition aggregate_joint :=
  fdistmap (fun r : V => (ArithmeticShares.reconstruct r, observe r)) (uniform R V).

Theorem aggregate_joint_law :
  (uniform R K) `X (fun s => fdistmap observe (sharing_law R n s)) = aggregate_joint.
Proof.
rewrite /aggregate_joint -uniform_secret_mixture map_bind HistorySemantics.dependent_product_bind.
congr (fdistbind (uniform R K) _); apply/boolp.funeqP => s.
rewrite /sharing_law !fdistmap_comp.
congr (fdistmap _ _); apply/boolp.funeqP => r.
by rewrite /= ArithmeticShares.share_correct.
Qed.

Lemma aggregate_marginal : fdist_fst aggregate_joint = uniform R K.
Proof. by rewrite -aggregate_joint_law fdist_prod1. Qed.

Theorem aggregate_conditional_law s :
  fdistmap observe (sharing_law R n s) = jfdist_cond aggregate_joint s.
Proof.
rewrite -aggregate_joint_law; apply: jfdist_cond_prod.
by rewrite fdist_prod1; exact: secret_mass_nonzero.
Qed.

Theorem aggregate_conditional_mass s o :
  fdistmap observe (sharing_law R n s) o = aggregate_joint (s, o) / uniform R K s.
Proof.
rewrite aggregate_conditional_law jfdist_condE; first by rewrite aggregate_marginal secret_mass_nonzero.
by rewrite /jcPr setX1 !Pr_set1 fdistXE fdistX2 aggregate_marginal.
Qed.

Definition joint_count s o :=
  #|[pred r : V | (ArithmeticShares.reconstruct r == s) && (observe r == o)]|.

Lemma aggregate_joint_count s o :
  aggregate_joint (s, o) = (joint_count s o)%:R / #|V|%:R.
Proof.
rewrite /aggregate_joint fdistmapE /uniform.
under eq_bigl do rewrite !inE xpair_eqE.
under eq_bigr do rewrite fdist_uniformE.
by rewrite sumr_const -[LHS]mulr_natl.
Qed.

(* Exact whole-vector counting, including n = 0; no conditional independence. *)
Theorem aggregate_count_formula s o :
  fdistmap observe (sharing_law R n s) o = (joint_count s o)%:R / (#|K|%:R : R)^+n.
Proof.
have q0 : (#|K|%:R : R) != 0.
  rewrite pnatr_eq0 -lt0n; exact: cardinal_positive.
rewrite aggregate_conditional_mass aggregate_joint_count /uniform fdist_uniformE
  card_ffun card_ord natrX exprS invfM invrK.
by rewrite -!mulrA [(#|K|%:R : R)^-1 * _]mulrCA mulVf // mulr1.
Qed.

End Aggregate.
End ArithmeticAggregate.

Print Assumptions ArithmeticAggregate.uniform_secret_joint.
Print Assumptions ArithmeticAggregate.uniform_vector_product.
Print Assumptions ArithmeticAggregate.sharing_law_conditional.
Print Assumptions ArithmeticAggregate.aggregate_conditional_law.
Print Assumptions ArithmeticAggregate.aggregate_conditional_mass.
Print Assumptions ArithmeticAggregate.aggregate_count_formula.
