From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder ladder_distribution shared_power.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module SharedLoop.
Section Loop.
Variable R : realType.
Variable K : finComNzRingType.
Local Notation C := [the finZmodType of coordinates K].
Definition state := (shares C * bool)%type.
Definition clear_state := (C * bool)%type.

Definition project (s : state) : clear_state :=
  (reconstruct s.1, s.2).

Definition clear_swap (b : bool) (c : C) : C :=
  if b then (c.2, c.1) else c.

(* Abstract CSwap permutes both shares; no control-trace claim is made here. *)
Definition swap_shares (b : bool) (p : shares C) : shares C :=
  (clear_swap b p.1, clear_swap b p.2).

Lemma swap_shares_correct b p :
  reconstruct (swap_shares b p) = clear_swap b (reconstruct p).
Proof. by case: b. Qed.

Definition clear_iteration (a24 xP : K) (bit : bool) (s : clear_state) : clear_state :=
  let c := clear_swap (xorb bit s.2) s.1 in
  (clear_step a24 xP c.1.1 c.1.2 c.2.1 c.2.2, bit).

Definition step_inputs (a24 xP : K) (bit : bool) (s : state) : MaskedLadder.inputs K :=
  let p := swap_shares (xorb bit s.2) s.1 in
  {| MaskedLadder.a24 := split a24 0; MaskedLadder.xP := split xP 0;
     MaskedLadder.X2 := (p.1.1.1, p.2.1.1); MaskedLadder.Z2 := (p.1.1.2, p.2.1.2);
     MaskedLadder.X3 := (p.1.2.1, p.2.2.1); MaskedLadder.Z3 := (p.1.2.2, p.2.2.2) |}.

Lemma step_inputs_correct a24 xP bit s :
  MaskedLadder.expected (step_inputs a24 xP bit s) =
  (clear_iteration a24 xP bit (project s)).1.
Proof.
case: s => p prev; case: bit; case: prev;
  by rewrite /step_inputs /MaskedLadder.expected /clear_iteration /project
    /swap_shares /clear_swap /= !split_correct.
Qed.

Definition iteration (a24 xP : K) (bit : bool) (s : state) : R.-fdist [the finType of state] :=
  fdistmap (fun p => (p, bit)) (MaskedLadder.program R (step_inputs a24 xP bit s)).

Lemma iteration_correct a24 xP bit s :
  fdistmap project (iteration a24 xP bit s) = fdist1 (clear_iteration a24 xP bit (project s)).
Proof.
rewrite /iteration fdistmap_comp.
change (fdistmap ((fun c : C => (c, bit)) \o (@reconstruct C))
  (MaskedLadder.program R (step_inputs a24 xP bit s)) =
  fdist1 (clear_iteration a24 xP bit (project s))).
rewrite -(fdistmap_comp (fun c : C => (c, bit)) (@reconstruct C)).
rewrite MaskedLadder.program_correct fdistmap1 step_inputs_correct.
by rewrite /clear_iteration.
Qed.

Fixpoint clear_run (m : nat) (a24 xP : K) (bits : nat -> bool) (s : clear_state) : clear_state :=
  match m with
  | 0 => s
  | n.+1 => clear_run n a24 xP bits (clear_iteration a24 xP (bits n) s)
  end.

Fixpoint run (m : nat) (a24 xP : K) (bits : nat -> bool) (s : state) : R.-fdist [the finType of state] :=
  match m with
  | 0 => fdist1 s
  | n.+1 => iteration a24 xP (bits n) s >>= run n a24 xP bits
  end.

Lemma run_correct m a24 xP bits s :
  fdistmap project (run m a24 xP bits s) = fdist1 (clear_run m a24 xP bits (project s)).
Proof.
elim: m s => [|m IH] s; first by rewrite /= fdistmap1.
rewrite /= (map_bind_pure _ IH).
change (fdistmap (clear_run m a24 xP bits \o project) (iteration a24 xP (bits m) s) =
  fdist1 (clear_run m a24 xP bits (clear_iteration a24 xP (bits m) (project s)))).
rewrite -(fdistmap_comp (clear_run m a24 xP bits) project).
by rewrite iteration_correct fdistmap1.
Qed.

Definition finish (s : state) : shares K * shares K :=
  let p := swap_shares s.2 s.1 in
  ((p.1.1.1, p.2.1.1), (p.1.1.2, p.2.1.2)).

Definition clear_finish (s : clear_state) : K * K :=
  (clear_swap s.2 s.1).1.

Definition project_pair (p : shares K * shares K) : K * K :=
  (reconstruct p.1, reconstruct p.2).

Lemma finish_correct s : project_pair (finish s) = clear_finish (project s).
Proof. by case: s => p []; rewrite /finish /project_pair /clear_finish /project /swap_shares /clear_swap. Qed.

Definition clear_projective m a24 xP bits :=
  clear_finish (clear_run m a24 xP bits (((1, 0), (xP, 1)), false)).

Definition projective m a24 xP bits :=
  fdistmap finish (run m a24 xP bits (split ((1, 0), (xP, 1)) 0, false)).

Theorem projective_correct m a24 xP bits :
  fdistmap project_pair (projective m a24 xP bits) = fdist1 (clear_projective m a24 xP bits).
Proof.
rewrite /projective fdistmap_comp.
have -> : project_pair \o finish = clear_finish \o project.
  by apply/boolp.funeqP => s; exact: finish_correct.
rewrite -(fdistmap_comp clear_finish project) run_correct fdistmap1.
by rewrite /clear_projective /project split_correct.
Qed.

Definition clear_affine e m a24 xP bits :=
  let p := clear_projective m a24 xP bits in p.1 * SharedPower.clear_power e p.2.

Definition affine_computation e m a24 xP bits :=
  projective m a24 xP bits >>= (fun p => SharedPower.affine R e p.1 p.2).

Theorem affine_computation_correct e m a24 xP bits :
  fdistmap (@reconstruct K) (affine_computation e m a24 xP bits) =
  fdist1 (clear_affine e m a24 xP bits).
Proof.
rewrite /affine_computation (map_bind_pure _ (fun p => SharedPower.affine_correct R e p.1 p.2)).
change (fdistmap ((fun p : K * K => p.1 * SharedPower.clear_power e p.2) \o project_pair)
  (projective m a24 xP bits) = fdist1 (clear_affine e m a24 xP bits)).
rewrite -(fdistmap_comp (fun p : K * K => p.1 * SharedPower.clear_power e p.2) project_pair).
by rewrite projective_correct fdistmap1.
Qed.

(* Refresh the returned shares; only the second share Y is observable. *)
Definition program e m a24 xP bits :=
  affine_computation e m a24 xP bits >>=
    (fun a => fdistmap (refresh a) (uniform R K)).

Theorem program_correct e m a24 xP bits :
  fdistmap (@reconstruct K) (program e m a24 xP bits) =
  fdist1 (clear_affine e m a24 xP bits).
Proof.
rewrite /program (map_bind_pure _ (fun a => refresh_distribution_correct R a)).
exact: affine_computation_correct.
Qed.

Theorem output_uniform e m a24 xP bits :
  fdistmap snd (program e m a24 xP bits) = uniform R K.
Proof.
rewrite /program map_bind.
have -> : (fun a : shares K => fdistmap snd (fdistmap (refresh a) (uniform R K))) =
    (fun _ => uniform R K).
  by apply/boolp.funeqP => a; rewrite fdistmap_comp refreshed_output_uniform.
exact: bind_constant.
Qed.

Theorem output_independent e m a24 xP bits1 bits2 :
  fdistmap snd (program e m a24 xP bits1) =
  fdistmap snd (program e m a24 xP bits2).
Proof. by rewrite !output_uniform. Qed.

End Loop.
End SharedLoop.
