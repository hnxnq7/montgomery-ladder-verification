From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder ladder_distribution shared_power shared_loop trace_masking.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module LadderTrace.
Section Ladder.
Variable R : realType.
Variable K : finComNzRingType.
Local Notation C := [the finZmodType of SharedLadder.coordinates K].
Local Notation S := [the finType of SharedLoop.state K].
Variables a24 xp : K.

Definition kernel (bits : nat -> bool) n (s : S) :=
  fdistmap (fun next : S => (next, next.1.2)) (SharedLoop.iteration R a24 xp (bits n) s).

Lemma kernel_observation bits n s :
  fdistmap snd (kernel bits n s) = uniform R C.
Proof.
rewrite /kernel /SharedLoop.iteration !fdistmap_comp.
exact: MaskedLadder.output_uniform.
Qed.

(* Checkpoints expose the refreshed Y vector after each complete LadderStep. *)
Definition loop m bits s := MaskingTrace.run_with_state (kernel bits) m s.

Lemma loop_state m bits s :
  fdistmap fst (loop m bits s) = SharedLoop.run R m a24 xp bits s.
Proof.
rewrite /loop MaskingTrace.erase_state.
elim: m s => [|m IH] s; first by [].
rewrite /= /kernel bind_map.
congr (fdistbind (SharedLoop.iteration R a24 xp (bits m) s) _).
by apply/boolp.funeqP => next; exact: IH.
Qed.

Theorem loop_checkpoints m bits s :
  fdistmap snd (loop m bits s) = MaskingTrace.independent_trace (uniform R C) m.
Proof.
rewrite /loop MaskingTrace.erase_trace.
apply: MaskingTrace.joint_trace_distribution.
exact: kernel_observation.
Qed.

Variable exponent : BinNums.positive.

Definition complete (s : S) :=
  let p := SharedLoop.finish s in
  SharedPower.affine R exponent p.1 p.2 >>=
    (fun a => fdistmap (refresh a) (uniform R K)).

Lemma complete_observation s : fdistmap snd (complete s) = uniform R K.
Proof.
rewrite /complete map_bind.
have -> : (fun a : shares K => fdistmap snd (fdistmap (refresh a) (uniform R K))) =
    (fun _ => uniform R K).
  by apply/boolp.funeqP => a; rewrite fdistmap_comp refreshed_output_uniform.
exact: bind_constant.
Qed.

Definition program m bits :=
  loop m bits (split ((1, 0), (xp, 1)) 0, false) >>=
    (fun p => fdistmap (fun a => (a, p.2)) (complete p.1)).

Theorem program_erasure m bits :
  fdistmap fst (program m bits) = SharedLoop.program R exponent m a24 xp bits.
Proof.
rewrite /program map_bind.
have -> : (fun p : S * MaskingTrace.trace_type C m =>
    fdistmap fst (fdistmap (fun a => (a, p.2)) (complete p.1))) =
    (fun p => complete p.1).
  by apply/boolp.funeqP => p; rewrite fdistmap_comp fdistmap_id.
rewrite -(@bind_map R _ _ _ (loop m bits (split ((1, 0), (xp, 1)) 0, false)) fst complete).
rewrite loop_state /SharedLoop.program /SharedLoop.affine_computation
  /SharedLoop.projective bind_map fdistbindA.
reflexivity.
Qed.

Definition observe m (p : shares K * MaskingTrace.trace_type C m) :=
  (p.2, p.1.2).

Theorem program_checkpoints m bits :
  fdistmap (@observe m) (program m bits) =
  MaskingTrace.independent_trace (uniform R C) m >>=
    (fun t => fdistmap (fun y => (t, y)) (uniform R K)).
Proof.
rewrite /program map_bind.
have -> : (fun p : S * MaskingTrace.trace_type C m =>
    fdistmap (@observe m) (fdistmap (fun a => (a, p.2)) (complete p.1))) =
    (fun p => fdistmap (fun y => (p.2, y)) (uniform R K)).
  apply/boolp.funeqP => p; rewrite fdistmap_comp.
  change (fdistmap ((fun y => (p.2, y)) \o snd) (complete p.1) =
    fdistmap (fun y => (p.2, y)) (uniform R K)).
  by rewrite -(fdistmap_comp (fun y => (p.2, y)) snd) complete_observation.
rewrite -(@bind_map R _ _ _ (loop m bits (split ((1, 0), (xp, 1)) 0, false)) snd
  (fun t => fdistmap (fun y => (t, y)) (uniform R K))).
by rewrite loop_checkpoints.
Qed.

Theorem program_checkpoint_independent m bits1 bits2 :
  fdistmap (@observe m) (program m bits1) = fdistmap (@observe m) (program m bits2).
Proof. by rewrite !program_checkpoints. Qed.

End Ladder.
End LadderTrace.
