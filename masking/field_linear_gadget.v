From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder field_refresh
  field_mul_gadget field_mul_leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FieldLinearGadget.

Section Operations.
Variable K : finComNzRingType.

Definition raw (subtract : bool) (a b : shares K) :=
  if subtract then SharedLadder.raw_sub a b else SharedLadder.raw_add a b.

Definition result subtract a b r :=
  refresh (raw subtract a b) r.

Definition value (subtract : bool) (x y : K) :=
  if subtract then x - y else x + y.

Theorem result_correct subtract a b r :
  reconstruct (result subtract a b r) = value subtract (reconstruct a) (reconstruct b).
Proof.
case: subtract; [exact: SharedLadder.shared_sub_correct | exact: SharedLadder.shared_add_correct].
Qed.

(* Reuse the multiplication bank; unused scratch slots remain zero. *)
Definition writes subtract a b (r : K) : seq (nat * K) :=
  let c := raw subtract a b in
  [:: (4%N, r); (10%N, c.1); (11%N, c.2); (10%N, c.1 + r); (11%N, c.2 - r)].

Definition trace subtract a b r :=
  FieldMulGadget.store_trace (FieldMulGadget.initial_bank a b) (writes subtract a b r).

Lemma trace_length subtract a b r : size (trace subtract a b r) = 6%N.
Proof. by []. Qed.

Lemma trace_footprint subtract a b r :
  all (fun bank => size bank == 12%N) (trace subtract a b r).
Proof. by []. Qed.

Lemma trace_output subtract a b r :
  FieldMulGadget.output (last [::] (trace subtract a b r)) = result subtract a b r.
Proof. by []. Qed.

Theorem trace_correct subtract a b r :
  reconstruct (FieldMulGadget.output (last [::] (trace subtract a b r))) =
  value subtract (reconstruct a) (reconstruct b).
Proof. by rewrite trace_output result_correct. Qed.

End Operations.

Section Distribution.
Variable R : realType.
Variable K : finComNzRingType.

Theorem output_pair_law subtract (a b : shares K) :
  fdistmap (result subtract a b) (uniform R K) =
  share_distribution R (value subtract (reconstruct a) (reconstruct b)).
Proof.
case: subtract; [exact: FieldRefresh.shared_sub_pair_law | exact: FieldRefresh.shared_add_pair_law].
Qed.

Variable O : finType.
Variable observe : seq K -> R.-fdist O.

Definition trace_law subtract (a b : shares K) :=
  uniform R K >>= (fun r => FieldMulLeakage.observe_trace observe 6 (trace subtract a b r)).

Definition belief_trace_law subtract (belief : R.-fdist (shares K * shares K)) :=
  belief >>= (fun ab => trace_law subtract ab.1 ab.2).

End Distribution.
End FieldLinearGadget.

Print Assumptions FieldLinearGadget.trace_correct.
Print Assumptions FieldLinearGadget.output_pair_law.
