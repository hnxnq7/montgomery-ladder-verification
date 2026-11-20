From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist variation_dist.
From Masking Require Import finite_masking trace_masking noisy_leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module NoisyTrace.
Section Bounds.
Variable R : realType.

Lemma L1_triangle (A : finType) (d e f : R.-fdist A) :
  var_dist d f <= var_dist d e + var_dist e f.
Proof.
rewrite /var_dist -big_split /=. apply: ler_sum => a _.
have -> : d a - f a = (d a - e a) + (e a - f a).
  by rewrite addrA subrK.
exact: ler_normD.
Qed.

Lemma TV_triangle (A : finType) (d e f : R.-fdist A) :
  TV d f <= TV d e + TV e f.
Proof.
rewrite /TV -mulrDl.
apply: ler_pM; try exact: pos_var_dist; try exact: L1_triangle.
- by rewrite invr_ge0 ler0n.
- exact: lexx.
Qed.

Lemma bind_L1_kernel (A B : finType) (d : R.-fdist A) (f g : A -> R.-fdist B) :
  var_dist (d >>= f) (d >>= g) <= \sum_(a : A) d a * var_dist (f a) (g a).
Proof.
rewrite /var_dist.
apply: (@le_trans _ _ (\sum_(b : B) \sum_(a : A) d a * `|f a b - g a b|)).
- apply: ler_sum => b _.
  rewrite !fdistbindE -sumrB.
  under eq_bigr do rewrite -mulrBr.
  apply: le_trans (ler_norm_sum _ _ _) _.
  apply: ler_sum => a _. by rewrite normrM (ger0_norm (FDist.ge0 d a)).
- rewrite exchange_big. apply: ler_sum => a _.
  by rewrite -big_distrr.
Qed.

Lemma bind_TV_kernel (A B : finType) (d : R.-fdist A) (f g : A -> R.-fdist B) :
  TV (d >>= f) (d >>= g) <= \sum_(a : A) d a * TV (f a) (g a).
Proof.
rewrite /TV.
under eq_bigr do rewrite mulrA.
rewrite -big_distrl.
apply: ler_pM; try exact: pos_var_dist; try exact: bind_L1_kernel.
- by rewrite invr_ge0 ler0n.
- exact: lexx.
Qed.

Lemma bind_TV_bound (A B : finType) (d : R.-fdist A) (f g : A -> R.-fdist B) epsilon :
  (forall a, TV (f a) (g a) <= epsilon) -> TV (d >>= f) (d >>= g) <= epsilon.
Proof.
move=> H. apply: le_trans (bind_TV_kernel d f g) _.
rewrite -[epsilon]mul1r -(FDist.f1 d) big_distrl /=.
apply: ler_sum => a _. apply: ler_wpM2l; [exact: FDist.ge0 | exact: H].
Qed.

Lemma map_TV_contraction (A B : finType) (d e : R.-fdist A) (f : A -> B) :
  TV (fdistmap f d) (fdistmap f e) <= TV d e.
Proof. exact: (channel_TV_contraction d e (fun a => fdist1 (f a))). Qed.

Section Trace.
Variables S O : finType.
Variable step : nat -> S -> R.-fdist [the finType of (S * O)%type].
Variable observation : nat -> R.-fdist O.
Variable epsilon : R.

(* Public control may change the reference leakage law at each step. *)
Fixpoint reference_trace (n : nat) : R.-fdist (MaskingTrace.trace_type O n) :=
  match n as k return R.-fdist (MaskingTrace.trace_type O k) with
  | 0 => fdist1 tt
  | k.+1 => observation k >>= (fun y => fdistmap (fun t => (y, t)) (reference_trace k))
  end.

(* The premise holds for every hidden state, not just an initial-state marginal. *)
Hypothesis step_observation_bound : forall n s,
  TV (fdistmap snd (step n s)) (observation n) <= epsilon.

Theorem trace_reference_bound n s :
  TV (MaskingTrace.run step n s) (reference_trace n) <= n%:R * epsilon.
Proof.
elim: n s => [|n IH] s.
- by rewrite /= TV_self mul0r.
- rewrite /=.
  set hybrid := step n s >>= (fun p =>
    fdistmap (fun t => (p.2, t)) (reference_trace n)).
  apply: le_trans (TV_triangle _ hybrid _) _.
  rewrite -natr1 mulrDl mul1r.
  apply: lerD.
  + apply: bind_TV_bound => p.
    exact: le_trans (map_TV_contraction _ _ (fun t => (p.2, t))) (IH p.1).
  + rewrite /hybrid -(@bind_map R _ _ _ (step n s) snd
      (fun y => fdistmap (fun t => (y, t)) (reference_trace n))).
    exact: le_trans (channel_TV_contraction _ _ _) (step_observation_bound n s).
Qed.

Theorem trace_pair_bound n s t :
  TV (MaskingTrace.run step n s) (MaskingTrace.run step n t) <= 2 * n%:R * epsilon.
Proof.
apply: le_trans (TV_triangle _ (reference_trace n) _) _.
rewrite -mulrA mulr_natl mulr2n.
apply: lerD; first exact: trace_reference_bound.
rewrite /TV symmetric_var_dist. exact: trace_reference_bound.
Qed.

(* Repetitions are independent whole runs; observations inside each run may correlate. *)
Corollary iid_trace_pair_bound q n s t :
  TV (iid (MaskingTrace.run step n s) q) (iid (MaskingTrace.run step n t) q) <=
    q%:R * (2 * n%:R * epsilon).
Proof.
apply: le_trans (iid_TV_bound _ _ q) _.
apply: ler_wpM2l; first by rewrite ler0n.
exact: trace_pair_bound.
Qed.

End Trace.

Section History.
Variable O : finType.

(* Prior observations are newest first; the returned trace is in execution order. *)
Fixpoint history_run (kernel : nat -> seq O -> R.-fdist O) (n : nat) (h : seq O) :
    R.-fdist (MaskingTrace.trace_type O n) :=
  match n as k return R.-fdist (MaskingTrace.trace_type O k) with
  | 0 => fdist1 tt
  | k.+1 => kernel k h >>= (fun o =>
      fdistmap (fun t => (o, t)) (history_run kernel k (o :: h)))
  end.

Variables k1 k2 : nat -> seq O -> R.-fdist O.
Variable epsilon : R.

(* This conditional-law premise needs its own proof and interpreter connection. *)
Hypothesis history_observation_bound : forall n h,
  TV (k1 n h) (k2 n h) <= epsilon.

Theorem history_trace_bound n h :
  TV (history_run k1 n h) (history_run k2 n h) <= n%:R * epsilon.
Proof.
elim: n h => [|n IH] h.
- by rewrite /= TV_self mul0r.
- rewrite /=.
  set hybrid := k1 n h >>= (fun o =>
    fdistmap (fun t => (o, t)) (history_run k2 n (o :: h))).
  apply: le_trans (TV_triangle _ hybrid _) _.
  rewrite -natr1 mulrDl mul1r.
  apply: lerD.
  + apply: bind_TV_bound => o.
    exact: le_trans (map_TV_contraction _ _ (fun t => (o, t))) (IH (o :: h)).
  + exact: le_trans (channel_TV_contraction _ _ _) (history_observation_bound n h).
Qed.

Corollary iid_history_trace_bound q n h :
  TV (iid (history_run k1 n h) q) (iid (history_run k2 n h) q) <=
    q%:R * (n%:R * epsilon).
Proof.
apply: le_trans (iid_TV_bound _ _ q) _.
apply: ler_wpM2l; first by rewrite ler0n.
exact: history_trace_bound.
Qed.

End History.
End Bounds.
End NoisyTrace.

Print Assumptions NoisyTrace.trace_reference_bound.
Print Assumptions NoisyTrace.trace_pair_bound.
Print Assumptions NoisyTrace.iid_trace_pair_bound.
Print Assumptions NoisyTrace.history_trace_bound.
Print Assumptions NoisyTrace.iid_history_trace_bound.
