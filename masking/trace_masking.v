From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module MaskingTrace.
Section Trace.
Variable R : realType.
Variables S O : finType.
Variable step : nat -> S -> R.-fdist [the finType of (S * O)%type].
Variable observation : R.-fdist O.

Fixpoint trace_type (n : nat) : finType :=
  match n with
  | 0 => [the finType of (unit : Type)]
  | n.+1 => [the finType of (O * trace_type n)%type]
  end.

(* One public step emits one observation; internal states remain hidden. *)
Fixpoint run (n : nat) (s : S) : R.-fdist (trace_type n) :=
  match n with
  | 0 => fdist1 tt
  | n.+1 => step n s >>= (fun p => fdistmap (fun t => (p.2, t)) (run n p.1))
  end.

Fixpoint independent_trace (n : nat) : R.-fdist (trace_type n) :=
  match n with
  | 0 => fdist1 tt
  | n.+1 => observation >>= (fun y => fdistmap (fun t => (y, t)) (independent_trace n))
  end.

Fixpoint run_with_state (n : nat) (s : S) :
    R.-fdist [the finType of (S * trace_type n)%type] :=
  match n with
  | 0 => fdist1 (s, tt)
  | n.+1 => step n s >>= (fun p =>
      fdistmap (fun q => (q.1, (p.2, q.2))) (run_with_state n p.1))
  end.

Fixpoint state_run (n : nat) (s : S) : R.-fdist S :=
  match n with
  | 0 => fdist1 s
  | n.+1 => step n s >>= (fun p => state_run n p.1)
  end.

Lemma erase_state n s : fdistmap fst (run_with_state n s) = state_run n s.
Proof.
elim: n s => [|n IH] s; first by rewrite /= fdistmap1.
rewrite /= map_bind; congr (fdistbind (step n s) _).
apply/boolp.funeqP => p; rewrite fdistmap_comp.
exact: IH.
Qed.

Lemma erase_trace n s : fdistmap snd (run_with_state n s) = run n s.
Proof.
elim: n s => [|n IH] s; first by rewrite /= fdistmap1.
rewrite /= map_bind; congr (fdistbind (step n s) _).
apply/boolp.funeqP => p; rewrite fdistmap_comp.
change (fdistmap ((fun t => (p.2, t)) \o snd) (run_with_state n p.1) =
  fdistmap (fun t => (p.2, t)) (run n p.1)).
by rewrite -(fdistmap_comp (fun t => (p.2, t)) snd) IH.
Qed.

(* Equality must hold for every hidden state, not merely for one input marginal. *)
Hypothesis step_observation : forall n s, fdistmap snd (step n s) = observation.

Theorem joint_trace_distribution n s : run n s = independent_trace n.
Proof.
elim: n s => [|n IH] s; first by [].
rewrite /=.
have -> : (fun p : S * O => fdistmap (fun t => (p.2, t)) (run n p.1)) =
    (fun p => fdistmap (fun t => (p.2, t)) (independent_trace n)).
  by apply/boolp.funeqP => p; rewrite IH.
rewrite -(@bind_map R _ _ _ (step n s) snd
  (fun y => fdistmap (fun t => (y, t)) (independent_trace n))).
by rewrite step_observation.
Qed.

Theorem joint_trace_independent n s1 s2 : run n s1 = run n s2.
Proof. by rewrite !joint_trace_distribution. Qed.

End Trace.

Section Refreshed.
Variable R : realType.
Variable S : finType.
Variable K : finComNzRingType.
Variable compute : nat -> S -> shares K.
Variable update : nat -> S -> shares K -> S.

Definition refreshed_step n (s : S) : R.-fdist [the finType of (S * K)%type] :=
  fdistmap (fun r => let a := refresh (compute n s) r in (update n s a, a.2)) (uniform R K).

Lemma refreshed_step_observation n s :
  fdistmap snd (refreshed_step n s) = uniform R K.
Proof. by rewrite /refreshed_step fdistmap_comp; exact: refreshed_output_uniform. Qed.

Theorem refreshed_trace_independent n s1 s2 :
  run refreshed_step n s1 = run refreshed_step n s2.
Proof.
apply: (@joint_trace_independent R S K refreshed_step (uniform R K)).
exact: refreshed_step_observation.
Qed.

End Refreshed.
End MaskingTrace.
