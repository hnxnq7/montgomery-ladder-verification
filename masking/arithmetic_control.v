From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From Masking Require Import arithmetic_shares.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ArithmeticShares.
Local Open Scope ring_scope.

Module ArithmeticControl.
Section Swap.
Variable K : finComNzRingType.
Variable n : nat.
Local Notation Shares := (shares K n).
Local Notation Masks := (masks K n).

(* XOR of shared Boolean values, without reconstructing the control bit. *)
Definition xor_bits (left right : Shares) (randomness : Masks) : Shares :=
  let product := sequential_multiply left right randomness in
  sub (add left right) (add product product).

Lemma xor_bits_reconstruct left right randomness :
  reconstruct (xor_bits left right randomness) =
  reconstruct left + reconstruct right -
    (reconstruct left * reconstruct right + reconstruct left * reconstruct right).
Proof. by rewrite /xor_bits sub_correct !add_correct sequential_multiply_correct. Qed.

Theorem xor_bits_correct (b c : bool) left right randomness :
  reconstruct left = (if b then 1 else 0) ->
  reconstruct right = (if c then 1 else 0) ->
  reconstruct (xor_bits left right randomness) = (if xorb b c then 1 else 0).
Proof.
  move=> Hl Hr. rewrite xor_bits_reconstruct Hl Hr. clear Hl Hr.
  by case: b; case: c; rewrite /= ?mul1r ?mul0r ?addr0 ?add0r ?subrr ?subr0 ?oppr0.
Qed.

(* The caller supplies multiplication masks; the control shares are retained unchanged. *)
Definition cswap (control left right : Shares) (randomness : Masks) : Shares * (Shares * Shares) :=
  let delta := sequential_multiply control (sub right left) randomness in
  (control, (add left delta, sub right delta)).

Theorem cswap_control control left right randomness :
  (cswap control left right randomness).1 = control.
Proof. reflexivity. Qed.

Lemma cswap_reconstruct control left right randomness :
  (reconstruct (cswap control left right randomness).2.1,
   reconstruct (cswap control left right randomness).2.2) =
  (reconstruct left + reconstruct control * (reconstruct right - reconstruct left),
   reconstruct right - reconstruct control * (reconstruct right - reconstruct left)).
Proof.
rewrite /cswap /= add_correct sub_correct sequential_multiply_correct sub_correct.
reflexivity.
Qed.

Theorem cswap_zero control left right randomness :
  reconstruct control = 0 ->
  (reconstruct (cswap control left right randomness).2.1,
   reconstruct (cswap control left right randomness).2.2) =
  (reconstruct left, reconstruct right).
Proof. by move=> H; rewrite cswap_reconstruct H mul0r addr0 subr0. Qed.

Theorem cswap_one control left right randomness :
  reconstruct control = 1 ->
  (reconstruct (cswap control left right randomness).2.1,
   reconstruct (cswap control left right randomness).2.2) =
  (reconstruct right, reconstruct left).
Proof.
move=> H; rewrite cswap_reconstruct H mul1r.
congr (_, _).
- by rewrite addrC subrK.
- by rewrite opprB addrC subrK.
Qed.

(* The conditional is a specification only; cswap does not inspect the secret bit. *)
Theorem cswap_correct (bit : bool) control left right randomness :
  reconstruct control = (if bit then 1 else 0) ->
  (reconstruct (cswap control left right randomness).2.1,
   reconstruct (cswap control left right randomness).2.2) =
  if bit then (reconstruct right, reconstruct left) else (reconstruct left, reconstruct right).
Proof. case: bit; [exact: cswap_one | exact: cswap_zero]. Qed.

End Swap.
End ArithmeticControl.

Print Assumptions ArithmeticControl.cswap_control.
Print Assumptions ArithmeticControl.xor_bits_correct.
Print Assumptions ArithmeticControl.cswap_correct.
