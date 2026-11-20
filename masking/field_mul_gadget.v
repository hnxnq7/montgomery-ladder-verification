From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking shared_ladder field_refresh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.

Module FieldMulGadget.

Section Gadget.
Variable K : finComNzRingType.

(* Independent operand refreshes are also used for squaring. *)
Definition multiply (a b : shares K) (ra rb rc : K) : shares K :=
  let A := refresh a ra in
  let B := refresh b rb in
  let cross := (rc + A.1 * B.2) + A.2 * B.1 in
  (A.1 * B.1 - rc, A.2 * B.2 + cross).

Lemma multiply_as_refresh a b ra rb rc :
  multiply a b ra rb rc =
  SharedLadder.shared_mul (refresh a ra) (refresh b rb) (- rc).
Proof.
rewrite /multiply /SharedLadder.shared_mul /SharedLadder.raw_mul /refresh /= opprK.
congr (_, _).
rewrite [LHS]addrC -!addrA.
by rewrite [rc + _]addrC !addrA.
Qed.

Theorem multiply_correct a b ra rb rc :
  reconstruct (multiply a b ra rb rc) = reconstruct a * reconstruct b.
Proof. by rewrite multiply_as_refresh SharedLadder.shared_mul_correct !refresh_correct. Qed.

Corollary square_correct a ra rb rc :
  reconstruct (multiply a a ra rb rc) = (reconstruct a)^+2.
Proof. by rewrite multiply_correct expr2. Qed.

(* Slots: operands (0..3), mask (4), products (5..8), cross term (9), output (10..11). *)
Definition initial_bank (a b : shares K) : seq K :=
  [:: a.1; a.2; b.1; b.2; 0; 0; 0; 0; 0; 0; 0; 0].

Definition writes (a b : shares K) (ra rb rc : K) : seq (nat * K) :=
  let A := refresh a ra in
  let B := refresh b rb in
  let p00 := A.1 * B.1 in
  let p11 := A.2 * B.2 in
  let p01 := A.1 * B.2 in
  let p10 := A.2 * B.1 in
  [:: (4%N, ra); (0%N, A.1); (1%N, A.2);
      (4%N, rb); (2%N, B.1); (3%N, B.2);
      (5%N, p00); (6%N, p11); (4%N, rc); (9%N, rc);
      (7%N, p01); (9%N, rc + p01); (8%N, p10);
      (9%N, rc + p01 + p10); (10%N, p00 - rc);
      (11%N, p11 + (rc + p01 + p10))].

Fixpoint store_trace (bank : seq K) (updates : seq (nat * K)) : seq (seq K) :=
  bank :: if updates is (slot, value) :: rest
          then store_trace (set_nth 0 bank slot value) rest else [::].

(* Operation-level storage trace, including partially refreshed inputs and stale temporaries. *)
Definition trace a b ra rb rc :=
  store_trace (initial_bank a b) (writes a b ra rb rc).

Definition output (bank : seq K) : shares K :=
  (nth 0 bank 10, nth 0 bank 11).

Lemma trace_length a b ra rb rc : size (trace a b ra rb rc) = 17%N.
Proof. by []. Qed.

Lemma trace_footprint a b ra rb rc :
  all (fun bank => size bank == 12%N) (trace a b ra rb rc).
Proof. by []. Qed.

Lemma trace_output a b ra rb rc :
  output (last [::] (trace a b ra rb rc)) = multiply a b ra rb rc.
Proof. by []. Qed.

Theorem trace_correct a b ra rb rc :
  reconstruct (output (last [::] (trace a b ra rb rc))) = reconstruct a * reconstruct b.
Proof. by rewrite trace_output multiply_correct. Qed.

(* Observe every stored-bank snapshot; combinational signals are outside this model. *)
Definition leakage (hw : K -> nat) a b ra rb rc : seq nat :=
  map (fun bank => foldr addn 0%N (map hw bank)) (trace a b ra rb rc).

Lemma leakage_length hw a b ra rb rc : size (leakage hw a b ra rb rc) = 17%N.
Proof. by rewrite /leakage size_map trace_length. Qed.

End Gadget.

Section Distribution.
Variable R : realType.
Variable K : finComNzRingType.

Theorem output_pair_law (a b : shares K) ra rb :
  fdistmap (multiply a b ra rb) (uniform R K) =
  share_distribution R (reconstruct a * reconstruct b).
Proof.
have E : multiply a b ra rb =
    SharedLadder.shared_mul (refresh a ra) (refresh b rb) \o (fun rc => - rc).
  apply/boolp.funeqP => rc; exact: multiply_as_refresh.
rewrite E -fdistmap_comp.
rewrite (@uniform_bijection R K (fun x => - x) (fun x => - x) (opprK) (opprK)).
by rewrite FieldRefresh.shared_mul_pair_law !refresh_correct.
Qed.

End Distribution.
End FieldMulGadget.

Print Assumptions FieldMulGadget.trace_correct.
Print Assumptions FieldMulGadget.output_pair_law.
