From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking field_mul_gadget field_mul_leakage field_linear_gadget
  field_history noisy_leakage noisy_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking
  FieldMulGadget FieldMulLeakage NoisyLeakage NoisyTrace.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FieldTraceBound.

Section Trace.
Variable R : realType.
Variable K : finComNzRingType.
Variable O : finType.
Variable observe : seq K -> R.-fdist O.
Variable epsilon : R.

(* A noise-only diameter assumption, not a benefit derived from masking. *)
Hypothesis channel_bound : forall bank1 bank2,
  size bank1 = 12%N -> size bank2 = 12%N ->
  TV (observe bank1) (observe bank2) <= epsilon.

Theorem observe_trace_bound n banks1 banks2 :
  size banks1 = n -> size banks2 = n ->
  all (fun bank => size bank == 12%N) banks1 ->
  all (fun bank => size bank == 12%N) banks2 ->
  TV (observe_trace observe n banks1) (observe_trace observe n banks2) <= n%:R * epsilon.
Proof.
elim: n banks1 banks2 => [|n IH] banks1 banks2 Hlen1 Hlen2 Hbanks1 Hbanks2.
- by rewrite /= TV_self mul0r.
- case: banks1 Hlen1 Hbanks1 => [|b1 bs1] //= /succn_inj Hlen1 /andP [/eqP Hb1 Hbs1].
  case: banks2 Hlen2 Hbanks2 => [|b2 bs2] //= /succn_inj Hlen2 /andP [/eqP Hb2 Hbs2].
  rewrite /=.
  set hybrid := observe b1 >>= (fun o =>
    fdistmap (fun rest => (o, rest)) (observe_trace observe n bs2)).
  apply: le_trans (TV_triangle _ hybrid _) _.
  rewrite -natr1 mulrDl mul1r.
  apply: lerD.
  + apply: bind_TV_bound => o.
    apply: le_trans (map_TV_contraction _ _ (fun rest => (o, rest))) _.
    exact: IH Hlen1 Hlen2 Hbs1 Hbs2.
  + exact: le_trans (channel_TV_contraction _ _ _) (channel_bound Hb1 Hb2).
Qed.

Theorem fixed_masks_trace_bound a b c d ra rb rc sa sb sc :
  TV (observe_trace observe 17 (trace a b ra rb rc))
     (observe_trace observe 17 (trace c d sa sb sc)) <= 17%:R * epsilon.
Proof.
apply: observe_trace_bound; try exact: trace_length; exact: trace_footprint.
Qed.

(* The three masks remain fixed throughout each actual execution. *)
Theorem trace_law_bound a b c d :
  TV (trace_law observe a b) (trace_law observe c d) <= 17%:R * epsilon.
Proof.
rewrite /trace_law.
apply: bind_TV_bound => ra.
apply: bind_TV_bound => rb.
apply: bind_TV_bound => rc.
exact: fixed_masks_trace_bound.
Qed.

Theorem linear_trace_law_bound subtract a b c d :
  TV (FieldLinearGadget.trace_law observe subtract a b)
     (FieldLinearGadget.trace_law observe subtract c d) <= 6%:R * epsilon.
Proof.
rewrite /FieldLinearGadget.trace_law.
apply: bind_TV_bound => r.
apply: observe_trace_bound;
  try exact: FieldLinearGadget.trace_length; exact: FieldLinearGadget.trace_footprint.
Qed.

Theorem arbitrarybelief_linear_trace_bound subtract (d e : R.-fdist (shares K * shares K)) :
  TV (FieldLinearGadget.belief_trace_law observe subtract d)
     (FieldLinearGadget.belief_trace_law observe subtract e) <= 6%:R * epsilon.
Proof.
rewrite /FieldLinearGadget.belief_trace_law.
apply: FieldHistory.mixture_TV_bound => ab cd.
exact: linear_trace_law_bound.
Qed.

End Trace.

Section Aggregate.
Variable R : realType.
Variable K : finComNzRingType.
Variables width noise_count : nat.
Variable hw : K -> nat.
Variable epsilon : R.

Hypothesis aggregate_channel_bound : forall bank1 bank2 : seq K,
  size bank1 = 12%N -> size bank2 = 12%N ->
  TV (@aggregate_channel R K width noise_count hw bank1)
     (@aggregate_channel R K width noise_count hw bank2) <= epsilon.

(* Includes all 17 snapshots and arbitrary correlated operand beliefs. *)
Theorem belief_trace_bound (d e : R.-fdist (shares K * shares K)) :
  TV (@belief_trace_law R K width noise_count hw d)
     (@belief_trace_law R K width noise_count hw e) <= 17%:R * epsilon.
Proof.
rewrite /belief_trace_law.
apply: FieldHistory.mixture_TV_bound => ab cd.
exact: (@trace_law_bound R K _ _ epsilon aggregate_channel_bound ab.1 ab.2 cd.1 cd.2).
Qed.

End Aggregate.
End FieldTraceBound.

Print Assumptions FieldTraceBound.observe_trace_bound.
Print Assumptions FieldTraceBound.trace_law_bound.
Print Assumptions FieldTraceBound.belief_trace_bound.
Print Assumptions FieldTraceBound.linear_trace_law_bound.
Print Assumptions FieldTraceBound.arbitrarybelief_linear_trace_bound.
