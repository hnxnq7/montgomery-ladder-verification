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

Module MaskedLadder.
Section Ladder.
Variable R : realType.
Variable K : finComNzRingType.
Local Notation C := [the finZmodType of coordinates K].
Local Notation T := [the finZmodType of mask_tape K].
Local Notation decode := (@reconstruct C).

Record inputs := {
  a24 : shares K;
  xP : shares K;
  X2 : shares K;
  Z2 : shares K;
  X3 : shares K;
  Z3 : shares K
}.

Definition expected (i : inputs) :=
  clear_step (reconstruct i.(a24)) (reconstruct i.(xP))
    (reconstruct i.(X2)) (reconstruct i.(Z2)) (reconstruct i.(X3)) (reconstruct i.(Z3)).

Definition step (i : inputs) (t : mask_tape K) : shares C :=
  pack (shared_step i.(a24) i.(xP) i.(X2) i.(Z2) i.(X3) i.(Z3) t).

Definition execute (i : inputs) (t : mask_tape K) (r : C) : shares C :=
  refresh (step i t) r.

Lemma execute_correct i t r : reconstruct (execute i t r) = expected i.
Proof.
rewrite /execute refresh_correct /step -reconstruct_packedE.
exact: packed_step_correct.
Qed.

(* Uniform finite functions sample independent operation masks; the output refresh is separate. *)
Definition program (i : inputs) : R.-fdist [the finType of shares C] :=
  uniform R T >>= (fun t => fdistmap (execute i t) (uniform R C)).

Theorem program_correct i :
  fdistmap decode (program i) = fdist1 (expected i).
Proof.
rewrite /program map_bind.
have H t : fdistmap decode (fdistmap (execute i t) (uniform R C)) = fdist1 (expected i).
  rewrite fdistmap_comp.
  have -> : decode \o execute i t = (fun _ => expected i).
    by apply/boolp.funeqP => r; exact: execute_correct.
  exact: map_constant.
have -> : (fun t => fdistmap decode (fdistmap (execute i t) (uniform R C))) =
    (fun _ => fdist1 (expected i)).
  by apply/boolp.funeqP => t; exact: H.
exact: bind_constant.
Qed.

(* Y is the complete four-coordinate vector of second shares, observed only at completion. *)
Theorem output_uniform i : fdistmap snd (program i) = uniform R C.
Proof.
rewrite /program map_bind.
have H t : fdistmap snd (fdistmap (execute i t) (uniform R C)) = uniform R C.
  rewrite fdistmap_comp /execute /=.
  exact: refreshed_output_uniform.
have -> : (fun t => fdistmap snd (fdistmap (execute i t) (uniform R C))) =
    (fun _ => uniform R C).
  by apply/boolp.funeqP => t; exact: H.
exact: bind_constant.
Qed.

Theorem output_independent (i j : inputs) :
  fdistmap snd (program i) = fdistmap snd (program j).
Proof. by rewrite !output_uniform. Qed.

Theorem observed_output_independent (B : finType) (observe : C -> B) (i j : inputs) :
  fdistmap (fun p => observe p.2) (program i) =
  fdistmap (fun p => observe p.2) (program j).
Proof.
have H := congr1 (fdistmap observe) (output_independent i j).
by rewrite !fdistmap_comp in H.
Qed.

Theorem correct_and_output_independent (i j : inputs) :
  fdistmap decode (program i) = fdist1 (expected i) /\
  fdistmap decode (program j) = fdist1 (expected j) /\
  fdistmap snd (program i) = fdistmap snd (program j).
Proof.
split; first exact: program_correct.
split; [exact: program_correct | exact: output_independent].
Qed.

End Ladder.
End MaskedLadder.
