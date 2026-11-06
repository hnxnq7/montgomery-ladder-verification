From Stdlib Require Import ZArith Lia.
From mathcomp Require Import boot order algebra reals.
Require Import ladder_math.
From Masking Require Import shared_ladder shared_loop shared_power.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Delimit Scope Z_scope with Z.
Local Open Scope ring_scope.

Module LadderBridge.
Section Bridge.
Variable K : finComNzRingType.
Variables p a24 : Z.
Variable encode : Z -> K.
Hypothesis encode_zero : encode 0%Z = 0.
Hypothesis encode_one : encode 1%Z = 1.
Hypothesis encode_add : forall x y, encode (x + y)%Z = encode x + encode y.
Hypothesis encode_sub : forall x y, encode (x - y)%Z = encode x - encode y.
Hypothesis encode_mul : forall x y, encode (x * y)%Z = encode x * encode y.
Hypothesis encode_mod : forall x, encode (x mod p)%Z = encode x.

(* The mathematical ladder uses left-associated tuples. *)
Definition encode_coordinates (c : Z * Z * Z * Z) : SharedLadder.coordinates K :=
  let '(X2, Z2, X3, Z3) := c in ((encode X2, encode Z2), (encode X3, encode Z3)).

Definition encode_state (s : (Z * Z * Z * Z) * bool) : SharedLoop.clear_state K :=
  (encode_coordinates s.1, s.2).

Definition encode_pair (c : Z * Z) : K * K :=
  (encode c.1, encode c.2).

Lemma step_matches_math xp X2 Z2 X3 Z3 :
  encode_coordinates (LadderStep p a24 xp X2 Z2 X3 Z3) =
  SharedLadder.clear_step (encode a24) (encode xp)
    (encode X2) (encode Z2) (encode X3) (encode Z3).
Proof.
rewrite /LadderStep /encode_coordinates /SharedLadder.clear_step /fsq /fadd /fsub /fmul /=.
by repeat first [rewrite encode_mod | rewrite encode_sub | rewrite encode_add | rewrite encode_mul].
Qed.

Lemma swap_matches_math b X2 Z2 X3 Z3 :
  encode_coordinates (CSwap X2 Z2 X3 Z3 b) =
  SharedLoop.clear_swap b (encode_coordinates (X2, Z2, X3, Z3)).
Proof. by case: b. Qed.

Lemma iteration_matches_math xp bit prev c :
  encode_state (MontLadderCSwap_step p a24 xp bit prev c) =
  SharedLoop.clear_iteration (encode a24) (encode xp) bit (encode_state (c, prev)).
Proof.
case: c => [[[X2 Z2] X3] Z3].
case: bit; case: prev;
  rewrite /MontLadderCSwap_step /CSwap /encode_state
    /SharedLoop.clear_iteration /SharedLoop.clear_swap /=;
  by rewrite -step_matches_math.
Qed.

Lemma run_matches_math m xp n s :
  encode_state (MontLadderCSwap_rec p a24 m xp n s) =
  SharedLoop.clear_run m (encode a24) (encode xp) (fun i => bit_i n i) (encode_state s).
Proof.
elim: m s => [|m IH] [c prev]; first by [].
by rewrite /= IH iteration_matches_math.
Qed.

Theorem projective_matches_math m xp n :
  encode_pair (MontLadderCSwap p a24 m xp n) =
  SharedLoop.clear_projective m (encode a24) (encode xp) (fun i => bit_i n i).
Proof.
rewrite /SharedLoop.clear_projective.
have init : (((1, 0), (encode xp, 1)), false) =
    encode_state ((1%Z, 0%Z, xp, 1%Z), false).
  by rewrite /encode_state /encode_coordinates /= encode_zero encode_one.
rewrite init -run_matches_math /MontLadderCSwap.
case: (MontLadderCSwap_rec p a24 m xp n ((1%Z, 0%Z, xp, 1%Z), false))
  => [[[[X2 Z2] X3] Z3] prev].
by case: prev.
Qed.

Lemma power_matches_math e x :
  SharedPower.clear_power e (encode x) = encode (x ^ Z.pos e)%Z.
Proof.
elim: e => [e IH | e IH |].
- change (encode x * (SharedPower.clear_power e (encode x) * SharedPower.clear_power e (encode x)) =
    encode (x ^ Z.pos (xI e))%Z).
  replace (Z.pos (xI e)) with (1 + (Z.pos e + Z.pos e))%Z by lia.
  rewrite Z.pow_add_r; try lia.
  rewrite Z.pow_add_r; try lia.
  by rewrite Z.pow_1_r !encode_mul -IH.
- change (SharedPower.clear_power e (encode x) * SharedPower.clear_power e (encode x) =
    encode (x ^ Z.pos (xO e))%Z).
  replace (Z.pos (xO e)) with (Z.pos e + Z.pos e)%Z by lia.
  rewrite Z.pow_add_r; try lia.
  by rewrite encode_mul -IH.
- change (encode x = encode (x ^ 1)%Z).
  by rewrite Z.pow_1_r.
Qed.

End Bridge.
End LadderBridge.
