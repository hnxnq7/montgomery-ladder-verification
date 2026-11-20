From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist variation_dist.
From Masking Require Import finite_masking.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module NoisyLeakage.
Section Channel.
Variable R : realType.

(* Infotheo's var_dist is L1, so total variation includes the factor 1/2. *)
Definition TV (A : finType) (d e : R.-fdist A) : R :=
  var_dist d e / 2.

Definition apply_channel (A B : finType) (d : R.-fdist A) (channel : A -> R.-fdist B) :=
  d >>= channel.

Definition bounded_indistinguishable (A : finType) (epsilon : R) (d e : R.-fdist A) : Prop :=
  TV d e <= epsilon.

Lemma TV_self (A : finType) (d : R.-fdist A) : TV d d = 0.
Proof.
rewrite /TV /var_dist.
under eq_bigr do rewrite subrr normr0.
by rewrite big1 // mul0r.
Qed.

Lemma equal_law_TV_zero (A : finType) (d e : R.-fdist A) :
  d = e -> TV d e = 0.
Proof. by move=> ->; exact: TV_self. Qed.

Lemma TV_nonnegative (A : finType) (d e : R.-fdist A) : 0 <= TV d e.
Proof. apply: mulr_ge0; [exact: pos_var_dist | by rewrite invr_ge0 ler0n]. Qed.

Lemma TV_zero_iff (A : finType) (d e : R.-fdist A) : TV d e = 0 <-> d = e.
Proof.
split; last exact: equal_law_TV_zero.
move/eqP. rewrite /TV mulf_eq0 invr_eq0 pnatr_eq0 /= orbF.
by move/eqP/def_var_dist.
Qed.

Lemma L1_at_most_two (A : finType) (d e : R.-fdist A) : var_dist d e <= 2.
Proof.
change (var_dist d e <= 1 + 1).
rewrite /var_dist -{1}(FDist.f1 d) -(FDist.f1 e) -big_split /=.
apply: ler_sum => a _.
apply: le_trans (ler_normB (d a) (e a)) _.
by rewrite (ger0_norm (FDist.ge0 d a)) (ger0_norm (FDist.ge0 e a)).
Qed.

Lemma TV_at_most_one (A : finType) (d e : R.-fdist A) : TV d e <= 1.
Proof.
rewrite /TV ler_pdivrMr ?ltr0n // mul1r.
exact: L1_at_most_two.
Qed.

(* A may encode a whole correlated trace; the channel is shared by both runs. *)
Theorem channel_L1_contraction (A B : finType) (d e : R.-fdist A)
    (channel : A -> R.-fdist B) :
  var_dist (apply_channel d channel) (apply_channel e channel) <= var_dist d e.
Proof.
rewrite /var_dist /apply_channel.
apply: (@le_trans _ _ (\sum_(b : B) \sum_(a : A) `|d a - e a| * channel a b)).
- apply: ler_sum => b _.
  rewrite !fdistbindE -sumrB.
  under eq_bigr do rewrite -mulrBl.
  apply: (@le_trans _ _ (\sum_(a : A) `|(d a - e a) * channel a b|)).
  + exact: ler_norm_sum.
  + apply: ler_sum => a _. by rewrite normrM (ger0_norm (FDist.ge0 (channel a) b)).
- rewrite exchange_big. apply: ler_sum => a _.
  by rewrite -big_distrr /= FDist.f1 mulr1.
Qed.

Theorem channel_TV_contraction (A B : finType) (d e : R.-fdist A)
    (channel : A -> R.-fdist B) :
  TV (apply_channel d channel) (apply_channel e channel) <= TV d e.
Proof.
apply: ler_pM; try exact: pos_var_dist; try exact: channel_L1_contraction.
- by rewrite invr_ge0 ler0n.
- exact: lexx.
Qed.

Lemma channel_preserves_bound (A B : finType) epsilon (d e : R.-fdist A)
    (channel : A -> R.-fdist B) :
  bounded_indistinguishable epsilon d e ->
  bounded_indistinguishable epsilon (apply_channel d channel) (apply_channel e channel).
Proof. move=> H; exact: le_trans (channel_TV_contraction d e channel) H. Qed.

Theorem constant_observation_noisy_equal (A B C : finType) (d e : R.-fdist A)
    (observe : A -> B) (value : B) (channel : B -> R.-fdist C) :
  (forall a, observe a = value) ->
  apply_channel (fdistmap observe d) channel = apply_channel (fdistmap observe e) channel.
Proof.
move=> H.
have -> : observe = (fun _ : A => value) by apply/boolp.funeqP.
by rewrite !map_constant.
Qed.

Lemma product_L1_bound (A B : finType) (d e : R.-fdist A) (p q : R.-fdist B) :
  var_dist (d `x p) (e `x q) <= var_dist d e + var_dist p q.
Proof.
rewrite /var_dist.
under eq_bigr do rewrite !fdist_prodE.
rewrite -(pair_bigA _ (fun a b => `|d a * p b - e a * q b|)) /=.
apply: (@le_trans _ _ (\sum_(a : A) \sum_(b : B)
  (`|d a - e a| * p b + e a * `|p b - q b|))).
- apply: ler_sum => a _. apply: ler_sum => b _.
  have -> : d a * p b - e a * q b = (d a - e a) * p b + e a * (p b - q b).
    by rewrite mulrBl mulrBr addrA subrK.
  apply: le_trans (ler_normD _ _) _.
  by rewrite !normrM (ger0_norm (FDist.ge0 p b)) (ger0_norm (FDist.ge0 e a)).
- have Hsum a : (\sum_(b : B) (`|d a - e a| * p b + e a * `|p b - q b|)) =
      `|d a - e a| + e a * (\sum_(b : B) `|p b - q b|).
    by rewrite big_split /= -!big_distrr /= FDist.f1 mulr1.
  rewrite (eq_bigr _ (fun a _ => Hsum a)).
  by rewrite big_split /= -big_distrl /= FDist.f1 mul1r.
Qed.

(* Each element is one whole execution trace, with fresh randomness between executions. *)
Fixpoint repetitions_type (A : finType) (q : nat) : finType :=
  match q with
  | O => [the finType of (unit : Type)]
  | S n => [the finType of (A * repetitions_type A n)%type]
  end.

Fixpoint iid (A : finType) (d : R.-fdist A) (q : nat) : R.-fdist (repetitions_type A q) :=
  match q as n return R.-fdist (repetitions_type A n) with
  | O => fdist1 tt
  | S n => d `x (iid d n)
  end.

Lemma iid_L1_bound (A : finType) (d e : R.-fdist A) q :
  var_dist (iid d q) (iid e q) <= q%:R * var_dist d e.
Proof.
elim: q => [|q IH].
- rewrite /= mul0r /var_dist.
  under eq_bigr do rewrite subrr normr0.
  by rewrite big1.
- apply: le_trans (product_L1_bound d e (iid d q) (iid e q)) _.
  rewrite -nat1r mulrDl mul1r.
  exact: lerD (lexx _) IH.
Qed.

Theorem iid_TV_bound (A : finType) (d e : R.-fdist A) q :
  TV (iid d q) (iid e q) <= q%:R * TV d e.
Proof.
rewrite /TV mulrA.
apply: ler_pM; try exact: pos_var_dist; try exact: iid_L1_bound.
- by rewrite invr_ge0 ler0n.
- exact: lexx.
Qed.

End Channel.
End NoisyLeakage.

Print Assumptions NoisyLeakage.channel_TV_contraction.
Print Assumptions NoisyLeakage.constant_observation_noisy_equal.
