From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking field_mul_gadget noisy_leakage
  noisy_bit_example noisy_shares noisy_channel_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking NoisyLeakage FieldMulGadget.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FieldMulLeakage.

Section Trace.
Variable R : realType.
Variable K : finComNzRingType.
Variable O : finType.
Variable observe : seq K -> R.-fdist O.

Fixpoint observe_trace (n : nat) (banks : seq (seq K)) : R.-fdist (repetitions_type O n) :=
  match n with
  | 0%N => fdist1 tt
  | k.+1 => observe (head [::] banks) >>= (fun o =>
      fdistmap (fun rest => (o, rest)) (observe_trace k (behead banks)))
  end.

(* Masks are sampled once per execution, not independently at each observation. *)
Definition trace_law (a b : shares K) : R.-fdist (repetitions_type O 17) :=
  uniform R K >>= (fun ra => uniform R K >>= (fun rb => uniform R K >>= (fun rc =>
    observe_trace 17 (trace a b ra rb rc)))).

End Trace.

Section Aggregate.
Variable R : realType.
Variable K : finComNzRingType.
Variables width noise_count : nat.
Variable hw : K -> nat.
Hypothesis hw_bound : forall x, (hw x <= width)%N.

Definition bank_hw (bank : seq K) :=
  foldr addn 0%N (map hw bank).

Lemma bank_hw_bound bank : (bank_hw bank <= size bank * width)%N.
Proof.
elim: bank => [|x bank IH]; first by [].
rewrite /bank_hw /= mulSn.
exact: leq_add (hw_bound x) IH.
Qed.

Definition aggregate_channel (bank : seq K) : R.-fdist 'I_(12 * width + noise_count).+1 :=
  NoisyChannelBridge.scalar_channel R (12 * width + noise_count) noise_count (bank_hw bank).

Lemma trace_channel_no_clip a b ra rb rc bank
    (noise : repetitions_type [the finType of (bool : Type)] noise_count) :
  bank \in trace a b ra rb rc ->
  val (inord (bank_hw bank + NoisyShares.noise_sum noise) :
    'I_(12 * width + noise_count).+1) = (bank_hw bank + NoisyShares.noise_sum noise)%N.
Proof.
move=> Hbank.
have Hsize : size bank = 12%N.
  move/allP: (trace_footprint a b ra rb rc) => H.
  apply/eqP; exact: (H bank Hbank).
apply: NoisyChannelBridge.scalar_channel_no_clip.
apply: leq_add; last exact: leqnn.
by move: (bank_hw_bound bank); rewrite Hsize.
Qed.

(* Aggregate stored HW plus independent binomial noise at every snapshot. *)
Definition aggregate_trace_law (a b : shares K) :=
  trace_law aggregate_channel a b.

(* A caller may supply its posterior operand distribution after earlier observations. *)
Definition belief_trace_law (belief : R.-fdist (shares K * shares K)) :=
  belief >>= (fun ab => aggregate_trace_law ab.1 ab.2).

Definition fresh_inputs_trace_law (s t : K) :=
  share_distribution R s >>= (fun a => share_distribution R t >>= (fun b =>
    aggregate_trace_law a b)).

(* Squaring starts from one shared operand, not two independent initial sharings. *)
Definition square_trace_law (s : K) :=
  share_distribution R s >>= (fun a => aggregate_trace_law a a).

End Aggregate.
End FieldMulLeakage.

Print Assumptions FieldMulLeakage.trace_channel_no_clip.
