From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.

Module SharedLadder.

(* Finite additive structures for coordinate vectors and mask tapes. *)
HB.instance Definition _ (A B : finZmodType) :=
  Finite.on (A * B)%type.
HB.instance Definition _ (A : finType) (B : finZmodType) :=
  Finite.on {ffun A -> B}.

Section Ladder.
Variable K : finComNzRingType.

Definition raw_add (a b : shares K) : shares K :=
  (a.1 + b.1, a.2 + b.2).

Definition raw_sub (a b : shares K) : shares K :=
  (a.1 - b.1, a.2 - b.2).

Definition raw_mul (a b : shares K) : shares K :=
  (a.1 * b.1, a.1 * b.2 + a.2 * b.1 + a.2 * b.2).

Definition shared_add a b r :=
  refresh (raw_add a b) r.

Definition shared_sub a b r :=
  refresh (raw_sub a b) r.

Definition shared_mul a b r :=
  refresh (raw_mul a b) r.

Lemma shared_add_correct a b r :
  reconstruct (shared_add a b r) = reconstruct a + reconstruct b.
Proof. by rewrite /shared_add refresh_correct /raw_add /reconstruct /= addrACA. Qed.

Lemma shared_sub_correct a b r :
  reconstruct (shared_sub a b r) = reconstruct a - reconstruct b.
Proof. by rewrite /shared_sub refresh_correct /raw_sub /reconstruct /= opprD addrACA. Qed.

Lemma shared_mul_correct a b r :
  reconstruct (shared_mul a b r) = reconstruct a * reconstruct b.
Proof.
by rewrite /shared_mul refresh_correct /raw_mul /reconstruct /= !mulrDl !mulrDr !addrA.
Qed.

Lemma shared_add_output_uniform (R : realType) a b :
  fdistmap (fun r => (shared_add a b r).2) (uniform R K) = uniform R K.
Proof. exact: refreshed_output_uniform. Qed.

Lemma shared_sub_output_uniform (R : realType) a b :
  fdistmap (fun r => (shared_sub a b r).2) (uniform R K) = uniform R K.
Proof. exact: refreshed_output_uniform. Qed.

Lemma shared_mul_output_uniform (R : realType) a b :
  fdistmap (fun r => (shared_mul a b r).2) (uniform R K) = uniform R K.
Proof. exact: refreshed_output_uniform. Qed.

Definition coordinates := ((K * K) * (K * K))%type.
Definition shared_coordinates := ((shares K * shares K) * (shares K * shares K))%type.
Definition mask_tape := {ffun 'I_18 -> K}.

(* Output order: ((Xd, Zd), (Xa, Za)); a24 uses the V2 + a24 * D convention. *)
Definition clear_step (a24 xP X2 Z2 X3 Z3 : K) : coordinates :=
  let U := X2 + Z2 in
  let V := X2 - Z2 in
  let W := X3 + Z3 in
  let T := X3 - Z3 in
  let U2 := U * U in
  let V2 := V * V in
  let UT := U * T in
  let VW := V * W in
  let Sp := UT + VW in
  let Sm := UT - VW in
  let Xa := Sp * Sp in
  let Sm2 := Sm * Sm in
  let Za := Sm2 * xP in
  let Xd := U2 * V2 in
  let D := U2 - V2 in
  let AD := a24 * D in
  let T2 := V2 + AD in
  let Zd := D * T2 in
  ((Xd, Zd), (Xa, Za)).

(* One mask per operation. Correctness holds for every tape, independently of its distribution. *)
Definition shared_step (a24 xP X2 Z2 X3 Z3 : shares K) (m : mask_tape) : shared_coordinates :=
  let U := shared_add X2 Z2 (m (inord 0)) in
  let V := shared_sub X2 Z2 (m (inord 1)) in
  let W := shared_add X3 Z3 (m (inord 2)) in
  let T := shared_sub X3 Z3 (m (inord 3)) in
  let U2 := shared_mul U U (m (inord 4)) in
  let V2 := shared_mul V V (m (inord 5)) in
  let UT := shared_mul U T (m (inord 6)) in
  let VW := shared_mul V W (m (inord 7)) in
  let Sp := shared_add UT VW (m (inord 8)) in
  let Sm := shared_sub UT VW (m (inord 9)) in
  let Xa := shared_mul Sp Sp (m (inord 10)) in
  let Sm2 := shared_mul Sm Sm (m (inord 11)) in
  let Za := shared_mul Sm2 xP (m (inord 12)) in
  let Xd := shared_mul U2 V2 (m (inord 13)) in
  let D := shared_sub U2 V2 (m (inord 14)) in
  let AD := shared_mul a24 D (m (inord 15)) in
  let T2 := shared_add V2 AD (m (inord 16)) in
  let Zd := shared_mul D T2 (m (inord 17)) in
  ((Xd, Zd), (Xa, Za)).

Definition reconstruct_coordinates (c : shared_coordinates) : coordinates :=
  ((reconstruct c.1.1, reconstruct c.1.2), (reconstruct c.2.1, reconstruct c.2.2)).

Lemma shared_step_correct a24 xP X2 Z2 X3 Z3 m :
  reconstruct_coordinates (shared_step a24 xP X2 Z2 X3 Z3 m) =
  clear_step (reconstruct a24) (reconstruct xP)
    (reconstruct X2) (reconstruct Z2) (reconstruct X3) (reconstruct Z3).
Proof.
rewrite /shared_step /reconstruct_coordinates /clear_step /=.
by repeat first [rewrite shared_add_correct | rewrite shared_sub_correct | rewrite shared_mul_correct].
Qed.

(* Regroup coordinate shares into two vectors for a separate output refresh. *)
Definition pack (c : shared_coordinates) : coordinates * coordinates :=
  (((c.1.1.1, c.1.2.1), (c.2.1.1, c.2.2.1)),
   ((c.1.1.2, c.1.2.2), (c.2.1.2, c.2.2.2))).

Definition reconstruct_packed (p : coordinates * coordinates) : coordinates :=
  ((p.1.1.1 + p.2.1.1, p.1.1.2 + p.2.1.2),
   (p.1.2.1 + p.2.2.1, p.1.2.2 + p.2.2.2)).

Lemma reconstruct_packedE p :
  reconstruct_packed p = @reconstruct [the finZmodType of coordinates] p.
Proof. by []. Qed.

Lemma pack_correct c : reconstruct_packed (pack c) = reconstruct_coordinates c.
Proof. by []. Qed.

Lemma packed_step_correct a24 xP X2 Z2 X3 Z3 m :
  reconstruct_packed (pack (shared_step a24 xP X2 Z2 X3 Z3 m)) =
  clear_step (reconstruct a24) (reconstruct xP)
    (reconstruct X2) (reconstruct Z2) (reconstruct X3) (reconstruct Z3).
Proof. by rewrite pack_correct shared_step_correct. Qed.

End Ladder.
End SharedLadder.
