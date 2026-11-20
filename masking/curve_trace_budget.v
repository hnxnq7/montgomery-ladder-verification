From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import curve_snapshot curve_snapshot_budget noisy_leakage noisy_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module CurveTraceBudget.

(* n counts extra shares; c includes every composition factor, including repetitions. *)
Lemma scaled_certificate n c e :
  (c^2 * (255*n.+1).+1 * 49^(2*(n.+1-2)) * 2^(e*2) <= 64^(2*(n.+1-2)))%N ->
  (c%:R:rat)^+2 * CurveSnapshot.squared_budget n <= 2^-(e*2).
Proof.
move=> H. rewrite CurveSnapshotBudget.squared_budgetE mulrA -natrX -natrM.
exact: CurveSnapshotBudget.rational_certificate H.
Qed.

Lemma real_scaled_certificate (R : realType) n c e :
  (c^2 * (255*n.+1).+1 * 49^(2*(n.+1-2)) * 2^(e*2) <= 64^(2*(n.+1-2)))%N ->
  (c%:R:R)^+2 * @ratr R (CurveSnapshot.squared_budget n) <= ((2:R)^-e)^+2.
Proof.
move=> H.
have B := @CurveSnapshotBudget.real_certificate R _ e (scaled_certificate H).
by rewrite rmorphM rmorphXn rmorph_nat in B.
Qed.

(* This is an arithmetic discharge rule, not a trace-composition theorem. *)
Theorem discharge (R : realType) n c e (distance : R) :
  0 <= distance ->
  distance^+2 <= (c%:R:R)^+2 * @ratr R (CurveSnapshot.squared_budget n) ->
  (c^2 * (255*n.+1).+1 * 49^(2*(n.+1-2)) * 2^(e*2) <= 64^(2*(n.+1-2)))%N ->
  distance <= (2:R)^-e.
Proof.
move=> Hd Hb Hc.
have He : 0 <= (2:R)^-e by rewrite invr_ge0 exprn_ge0 ?ler0n.
rewrite -ler_sqr ?nnegrE //.
exact: le_trans Hb (real_scaled_certificate R Hc).
Qed.

Section History.
Variable R : realType.
Variable O : finType.
Variables k1 k2 : nat -> seq O -> R.-fdist O.
Variables n L : nat.
Variable epsilon : R.
Hypothesis epsilon_nonnegative : 0 <= epsilon.
(* Use the exact square-root budget here, not a larger rounded certificate. *)
Hypothesis snapshot_budget : epsilon^+2 <= @ratr R (CurveSnapshot.squared_budget n).
(* Must hold after every observation history, not merely for unconditional snapshots. *)
Hypothesis conditional_bank_bound : forall t h,
  NoisyLeakage.TV (k1 t h) (k2 t h) <= L%:R * epsilon.

Theorem history_budget_squared repetitions clocks h :
  NoisyLeakage.TV
    (NoisyLeakage.iid (NoisyTrace.history_run k1 clocks h) repetitions)
    (NoisyLeakage.iid (NoisyTrace.history_run k2 clocks h) repetitions)^+2 <=
    ((repetitions*clocks*L)%:R:R)^+2 * @ratr R (CurveSnapshot.squared_budget n).
Proof.
have H := @NoisyTrace.iid_history_trace_bound R O k1 k2 (L%:R * epsilon)
  conditional_bank_bound repetitions clocks h.
rewrite !mulrA -!natrM in H.
have Hsq : NoisyLeakage.TV
    (NoisyLeakage.iid (NoisyTrace.history_run k1 clocks h) repetitions)
    (NoisyLeakage.iid (NoisyTrace.history_run k2 clocks h) repetitions)^+2 <=
    (((repetitions*clocks*L)%:R:R) * epsilon)^+2.
  apply: lerXn2r H.
  - exact: NoisyLeakage.TV_nonnegative.
  - apply: mulr_ge0 epsilon_nonnegative. exact: ler0n.
apply: le_trans Hsq _.
rewrite exprMn.
apply: ler_wpM2l snapshot_budget.
by rewrite sqr_ge0.
Qed.

Theorem history_budget repetitions clocks h e :
  ((repetitions*clocks*L)^2 * (255*n.+1).+1 * 49^(2*(n.+1-2)) *
    2^(e*2) <= 64^(2*(n.+1-2)))%N ->
  NoisyLeakage.TV
    (NoisyLeakage.iid (NoisyTrace.history_run k1 clocks h) repetitions)
    (NoisyLeakage.iid (NoisyTrace.history_run k2 clocks h) repetitions) <= (2:R)^-e.
Proof.
move=> Hc.
apply: discharge (history_budget_squared repetitions clocks h) Hc.
exact: NoisyLeakage.TV_nonnegative.
Qed.
End History.

Lemma dyadic_headroom (R : realType) c b e (distance : R) :
  distance <= c%:R * (2:R)^-(b+e) -> (c <= 2^b)%N -> distance <= (2:R)^-e.
Proof.
move=> Hd Hc.
have HcR : (c%:R:R) <= 2^+b by rewrite -natrX ler_nat.
apply: le_trans Hd _.
apply: le_trans (ler_wpM2r _ HcR) _.
- by rewrite invr_ge0 exprn_ge0 ?ler0n.
- have Hnz : (2:R)^+b != 0 by rewrite expf_eq0 pnatr_eq0 andbF.
  by rewrite exprD invfM mulrA mulfV // mul1r.
Qed.

(* The factor allowance is conditional; it is not a controller inventory. *)
Theorem headroom_256 (R : realType) c b e (distance : R) :
  0 <= distance ->
  distance^+2 <= (c%:R:R)^+2 * @ratr R (CurveSnapshot.squared_budget 255) ->
  (c <= 2^b)%N -> (b+e=88)%N -> distance <= (2:R)^-e.
Proof.
move=> Hd Hsq Hc Hbe.
have Hb := CurveSnapshotBudget.real_budget_256 R.
have Hmul : (c%:R:R)^+2 * @ratr R (CurveSnapshot.squared_budget 255) <=
    (c%:R * (2:R)^-88)^+2.
  rewrite exprMn. apply: ler_wpM2l Hb. exact: sqr_ge0.
have Hpos : 0 <= c%:R * (2:R)^-88.
  apply: mulr_ge0; first exact: ler0n.
  by rewrite invr_ge0 exprn_ge0 ?ler0n.
have Hlinear : distance <= c%:R * (2:R)^-88.
  rewrite -ler_sqr.
  - exact: Hd.
  - exact: Hpos.
  - exact: le_trans Hsq Hmul.
rewrite -Hbe in Hlinear.
exact: dyadic_headroom Hlinear Hc.
Qed.

(* Direct use of the certified 256-share epsilon avoids a square-root conversion. *)
Theorem history_256 (R : realType) (O : finType)
    (k1 k2 : nat -> seq O -> R.-fdist O) L repetitions clocks h b e :
  (forall t history, NoisyLeakage.TV (k1 t history) (k2 t history) <= L%:R * (2:R)^-88) ->
  (repetitions*clocks*L <= 2^b)%N -> (b+e=88)%N ->
  NoisyLeakage.TV
    (NoisyLeakage.iid (NoisyTrace.history_run k1 clocks h) repetitions)
    (NoisyLeakage.iid (NoisyTrace.history_run k2 clocks h) repetitions) <= (2:R)^-e.
Proof.
move=> Hhist Hc Hbe.
have H := @NoisyTrace.iid_history_trace_bound R O k1 k2 (L%:R * (2:R)^-88)
  Hhist repetitions clocks h.
rewrite !mulrA -!natrM -Hbe in H.
exact: dyadic_headroom H Hc.
Qed.
End CurveTraceBudget.

Print Assumptions CurveTraceBudget.scaled_certificate.
Print Assumptions CurveTraceBudget.history_budget.
Print Assumptions CurveTraceBudget.headroom_256.
Print Assumptions CurveTraceBudget.history_256.
