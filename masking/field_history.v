From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder field_refresh field_mul_gadget noisy_leakage noisy_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking FieldRefresh NoisyLeakage NoisyTrace.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FieldHistory.
Section Mixtures.
Variable R : realType.

Lemma mixture_TV_bound (A O : finType) (law : A -> R.-fdist O) epsilon :
  (forall x y, TV (law x) (law y) <= epsilon) ->
  forall d e : R.-fdist A, TV (d >>= law) (e >>= law) <= epsilon.
Proof.
move=> H d e.
have Er : e >>= law = d >>= (fun _ => e >>= law) by rewrite bind_constant.
rewrite Er. apply: bind_TV_bound => x.
have El : law x = e >>= (fun _ => law x) by rewrite bind_constant.
rewrite El. apply: bind_TV_bound => y.
exact: H.
Qed.

End Mixtures.

Section Refresh.
Variable R : realType.
Variable K : finZmodType.
Local Notation Pair := [the finType of (shares K)].
Local Notation reconstruct := (@FiniteMasking.reconstruct K).

Definition refresh_belief (belief : R.-fdist Pair) :=
  belief >>= (fun a => fdistmap (refresh a) (uniform R K)).

Theorem refresh_belief_law (belief : R.-fdist Pair) :
  refresh_belief belief = fdistmap reconstruct belief >>= (@share_distribution R K).
Proof.
rewrite /refresh_belief bind_map.
congr (fdistbind belief _).
by apply/boolp.funeqP => a; exact: refresh_pair_law.
Qed.

Variable O : finType.
Variable channel : Pair -> R.-fdist O.

Definition canonical_noisy (s : K) :=
  share_distribution R s >>= channel.

Lemma refresh_observation_law (belief : R.-fdist Pair) :
  refresh_belief belief >>= channel = fdistmap reconstruct belief >>= canonical_noisy.
Proof. by rewrite refresh_belief_law fdistbindA. Qed.

Variable epsilon : R.
Hypothesis canonical_bound : forall s t,
  TV (canonical_noisy s) (canonical_noisy t) <= epsilon.

(* Only the refreshed output pair is passed to the common observation channel. *)
Theorem refresh_belief_TV (d e : R.-fdist Pair) :
  TV (refresh_belief d >>= channel) (refresh_belief e >>= channel) <= epsilon.
Proof.
rewrite !refresh_observation_law.
exact: (@mixture_TV_bound R _ _ _ epsilon canonical_bound _ _).
Qed.

(* These may be conditional beliefs after a common observed history. *)
Corollary refresh_history_bound (d e : nat -> seq O -> R.-fdist Pair) n h :
  TV (refresh_belief (d n h) >>= channel) (refresh_belief (e n h) >>= channel) <= epsilon.
Proof. exact: refresh_belief_TV. Qed.

End Refresh.

Section Multiplication.
Variable R : realType.
Variable K : finComNzRingType.
Local Notation Pair := [the finType of (shares K)].
Local Notation Operands := [the finType of (shares K * shares K)%type].
Local Notation reconstruct := (@FiniteMasking.reconstruct K).

Definition product_value (ab : Operands) :=
  reconstruct ab.1 * reconstruct ab.2.

(* The joint operand belief may contain aliases and arbitrary correlations. *)
Definition mul_belief (belief : R.-fdist Operands) :=
  belief >>= (fun ab => fdistmap (SharedLadder.shared_mul ab.1 ab.2) (uniform R K)).

Theorem mul_belief_law (belief : R.-fdist Operands) :
  mul_belief belief = fdistmap product_value belief >>= (@share_distribution R K).
Proof.
rewrite /mul_belief bind_map.
congr (fdistbind belief _).
by apply/boolp.funeqP => ab; exact: shared_mul_pair_law.
Qed.

Definition gadget_belief (belief : R.-fdist Operands) :=
  belief >>= (fun ab =>
    uniform R K >>= (fun ra =>
      uniform R K >>= (fun rb =>
        fdistmap (FieldMulGadget.multiply ab.1 ab.2 ra rb) (uniform R K)))).

Theorem gadget_belief_law (belief : R.-fdist Operands) :
  gadget_belief belief = fdistmap product_value belief >>= (@share_distribution R K).
Proof.
rewrite /gadget_belief bind_map.
congr (fdistbind belief _).
apply/boolp.funeqP => ab.
have E ra :
    (fun rb => fdistmap (FieldMulGadget.multiply ab.1 ab.2 ra rb) (uniform R K)) =
    (fun _ : K => share_distribution R (product_value ab)).
  by apply/boolp.funeqP => rb; exact: FieldMulGadget.output_pair_law.
have F :
    (fun ra => uniform R K >>=
      (fun rb => fdistmap (FieldMulGadget.multiply ab.1 ab.2 ra rb) (uniform R K))) =
    (fun _ : K => share_distribution R (product_value ab)).
  by apply/boolp.funeqP => ra; rewrite E bind_constant.
by rewrite F bind_constant.
Qed.

Corollary gadget_belief_eq_mul (belief : R.-fdist Operands) :
  gadget_belief belief = mul_belief belief.
Proof. by rewrite gadget_belief_law mul_belief_law. Qed.

Variable O : finType.
Variable channel : Pair -> R.-fdist O.

Lemma mul_observation_law (belief : R.-fdist Operands) :
  mul_belief belief >>= channel =
    fdistmap product_value belief >>= (@canonical_noisy R K O channel).
Proof. by rewrite mul_belief_law fdistbindA. Qed.

Variable epsilon : R.
Hypothesis product_channel_bound : forall s t,
  TV (@canonical_noisy R K O channel s) (@canonical_noisy R K O channel t) <= epsilon.

Theorem mul_belief_TV (d e : R.-fdist Operands) :
  TV (mul_belief d >>= channel) (mul_belief e >>= channel) <= epsilon.
Proof.
rewrite !mul_observation_law.
exact: (@mixture_TV_bound R _ _ _ epsilon product_channel_bound _ _).
Qed.

Corollary mul_history_bound (d e : nat -> seq O -> R.-fdist Operands) n h :
  TV (mul_belief (d n h) >>= channel) (mul_belief (e n h) >>= channel) <= epsilon.
Proof. exact: mul_belief_TV. Qed.

(* Only completed output pairs are observed, not the gadget's internal register trace. *)
Theorem gadget_history_trace_bound (d e : nat -> seq O -> R.-fdist Operands) n h :
  TV (history_run (fun k hist => gadget_belief (d k hist) >>= channel) n h)
     (history_run (fun k hist => gadget_belief (e k hist) >>= channel) n h) <=
    n%:R * epsilon.
Proof.
apply: history_trace_bound => k hist.
rewrite !gadget_belief_eq_mul.
exact: mul_belief_TV.
Qed.

End Multiplication.
End FieldHistory.

Print Assumptions FieldHistory.refresh_belief_law.
Print Assumptions FieldHistory.mul_belief_law.
Print Assumptions FieldHistory.refresh_belief_TV.
Print Assumptions FieldHistory.mul_history_bound.
Print Assumptions FieldHistory.gadget_belief_law.
Print Assumptions FieldHistory.gadget_history_trace_bound.
