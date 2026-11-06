From Stdlib Require Import BinNums.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module SharedPower.

Section Power.
Variable K : finComNzRingType.
Variable R : realType.

Local Notation reconstruct := (@FiniteMasking.reconstruct K).

Definition multiply (a b : shares K) : R.-fdist (shares K) :=
  fdistmap (shared_mul a b) (uniform R K).

Lemma multiply_correct a b :
  fdistmap reconstruct (multiply a b) = fdist1 (reconstruct a * reconstruct b).
Proof.
rewrite /multiply fdistmap_comp.
have -> : reconstruct \o shared_mul a b = (fun _ => reconstruct a * reconstruct b).
  by apply/boolp.funeqP => r; exact: shared_mul_correct.
exact: map_constant.
Qed.

Fixpoint clear_power (e : positive) (a : K) : K :=
  match e with
  | xH => a
  | xO e' => let b := clear_power e' a in b * b
  | xI e' => let b := clear_power e' a in a * (b * b)
  end.

Lemma clear_power_zero e : clear_power e 0 = 0.
Proof. by elim: e => [e IH | e IH |] /=; rewrite ?IH ?mul0r. Qed.

(* Each multiply draws a fresh mask; squaring uses the same sampled operand twice. *)
Fixpoint power (e : positive) (a : shares K) : R.-fdist (shares K) :=
  match e with
  | xH => fdist1 a
  | xO e' => power e' a >>= (fun b => multiply b b)
  | xI e' => power e' a >>= (fun b => multiply b b >>= (fun c => multiply a c))
  end.

Lemma power_correct e a :
  fdistmap reconstruct (power e a) = fdist1 (clear_power e (reconstruct a)).
Proof.
elim: e => [e IH | e IH |] /=.
- rewrite map_bind.
  have -> : (fun b => fdistmap reconstruct (multiply b b >>= (fun c => multiply a c))) =
      (fun b => fdist1 (reconstruct a * (reconstruct b * reconstruct b))).
    apply/boolp.funeqP => b; rewrite map_bind.
    have -> : (fun c => fdistmap reconstruct (multiply a c)) =
        (fun c => fdist1 (reconstruct a * reconstruct c)).
      by apply/boolp.funeqP => c; exact: multiply_correct.
    rewrite -(@bind_map R _ _ _ (multiply b b) reconstruct
      (fun z => fdist1 (reconstruct a * z))).
    by rewrite multiply_correct fdist1bind.
  rewrite -(@bind_map R _ _ _ (power e a) reconstruct
    (fun z => fdist1 (reconstruct a * (z * z)))).
  by rewrite IH fdist1bind.
- rewrite map_bind.
  have -> : (fun b => fdistmap reconstruct (multiply b b)) =
      (fun b => fdist1 (reconstruct b * reconstruct b)).
    by apply/boolp.funeqP => b; exact: multiply_correct.
  rewrite -(@bind_map R _ _ _ (power e a) reconstruct (fun z => fdist1 (z * z))).
  by rewrite IH fdist1bind.
- exact: fdistmap1.
Qed.

Definition affine (e : positive) (X Z : shares K) : R.-fdist (shares K) :=
  power e Z >>= (fun iz => multiply X iz).

Lemma affine_correct e X Z :
  fdistmap reconstruct (affine e X Z) =
  fdist1 (reconstruct X * clear_power e (reconstruct Z)).
Proof.
rewrite /affine map_bind.
have -> : (fun iz => fdistmap reconstruct (multiply X iz)) =
    (fun iz => fdist1 (reconstruct X * reconstruct iz)).
  by apply/boolp.funeqP => iz; exact: multiply_correct.
rewrite -(@bind_map R _ _ _ (power e Z) reconstruct (fun z => fdist1 (reconstruct X * z))).
by rewrite power_correct fdist1bind.
Qed.

End Power.
End SharedPower.
