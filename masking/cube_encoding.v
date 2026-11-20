From Stdlib Require Import ZArith List.
From mathcomp Require Import boot order algebra reals field_tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Module CubeEncoding.

Fixpoint weight (w x : nat) : nat :=
  if w is k.+1 then (weight k (x %% 2 ^ k) + (x %/ 2 ^ k) %% 2)%N else 0%N.

Lemma weight_low w x : (x < 2 ^ w)%N -> weight w.+1 x = weight w x.
Proof. by move=> Hx; rewrite /= modn_small // divn_small // mod0n addn0. Qed.

Lemma weight_high w x : (x < 2 ^ w)%N ->
  weight w.+1 (2 ^ w + x) = (weight w x).+1.
Proof.
  move=> Hx; rewrite /= modnDl modn_small //.
  rewrite divnDl ?dvdnn // divnn expn_gt0 /= divn_small // addn0.
  by rewrite modn_small // addn1.
Qed.

Definition bitcount w x : nat :=
  \sum_(j < w) (odd (x %/ 2 ^ j) : nat).

Lemma bit_mod_power x w j : (j < w)%N ->
  odd ((x %% 2 ^ w) %/ 2 ^ j) = odd (x %/ 2 ^ j).
Proof.
  move=> Hj.
  have Hle := ltnW Hj.
  have Hd : (2 ^ j %| 2 ^ w)%N by apply: dvdn_exp2l.
  rewrite (divn_modl x Hd).
  rewrite -expnB //.
  apply: odd_mod.
  by rewrite oddX /= subn_eq0 leqNgt Hj.
Qed.

Lemma weight_bitcount w x : weight w x = bitcount w x.
Proof.
  elim: w x => [|w IH] x; first by rewrite /bitcount big_ord0.
  rewrite /weight -/weight IH /bitcount big_ord_recr /=.
  congr (_ + _)%N.
    by apply: eq_bigr => j _; rewrite bit_mod_power // ltn_ord.
  by rewrite modn2.
Qed.

Lemma divn_nat x d : (0 < d)%N -> (x %/ d)%N = Nat.div x d.
Proof.
  move=> Hd; apply Nat.div_unique with (r := (x %% d)%N).
    by apply/ltP; rewrite ltn_mod.
  by rewrite plusE multE mulnC -divn_eq.
Qed.

Lemma modn_nat x d : (0 < d)%N -> (x %% d)%N = Nat.modulo x d.
Proof.
  move=> Hd; apply Nat.mod_unique with (q := (x %/ d)%N).
    by apply/ltP; rewrite ltn_mod.
  by rewrite plusE multE mulnC -divn_eq.
Qed.

Lemma expn_nat x w : (x ^ w)%N = Nat.pow x w.
Proof. by elim: w => [|w IH]; rewrite ?expn0 ?expnS /= ?IH ?mulnE. Qed.

Lemma canonical_bit x j :
  Z.testbit (Z.of_nat x) (Z.of_nat j) = odd (x %/ 2 ^ j).
Proof.
  have Hp : (0 < 2 ^ j)%N by rewrite expn_gt0.
  have Hpow : Z.of_nat (2 ^ j) = Z.pow 2 (Z.of_nat j).
    by rewrite expn_nat Nat2Z.inj_pow.
  apply Z.b2z_inj.
  rewrite (Z.testbit_spec' (Z.of_nat x) (Z.of_nat j) (Nat2Z.is_nonneg j)).
  rewrite -Hpow -Nat2Z.inj_div.
  rewrite -(Nat2Z.inj_mod (Nat.div x (2 ^ j)%N) 2).
  rewrite -(@divn_nat x (2 ^ j)%N Hp) -(@modn_nat (x %/ 2 ^ j)%N 2 erefl) modn2.
  by case: (odd (x %/ 2 ^ j)).
Qed.

Definition canonical_HW w (x : Z) : nat :=
  \sum_(j < w) (Z.testbit x (Z.of_nat j) : nat).

Theorem weight_canonical_HW w x : weight w x = canonical_HW w (Z.of_nat x).
Proof.
  rewrite weight_bitcount /bitcount /canonical_HW.
  by apply: eq_bigr => j _; rewrite canonical_bit.
Qed.

Lemma canonical_HW_fold w x : canonical_HW w x =
  List.fold_right (fun j acc =>
    ((if Z.testbit x (Z.of_nat j) then 1 else 0) + acc)%N) 0%N (List.seq 0 w).
Proof.
  rewrite /canonical_HW -(big_mkord (n:=w) predT (fun j => (Z.testbit x (Z.of_nat j) : nat))).
  rewrite /index_iota subn0 unlock /reducebig.
  by [].
Qed.

Section Weighted.
Variable C : numClosedFieldType.

Theorem weighted_binary_product (z t : C) w :
  \sum_(x < 2 ^ w) z ^+ x * t ^+ (weight w x) =
    \prod_(j < w) (1 + t * z ^+ (2 ^ j)).
Proof.
  elim: w => [|w IH].
    by rewrite expn0 big_ord_recl big_ord0 /= expr0 mulr1 addr0 big_ord0.
  rewrite expnS mul2n -addnn big_split_ord.
  change ((\sum_(i < 2 ^ w) z ^+ i * t ^+ weight w.+1 i) +
    (\sum_(i < 2 ^ w) z ^+ (2 ^ w + i) * t ^+ weight w.+1 (2 ^ w + i)) =
    \prod_(j < w.+1) (1 + t * z ^+ (2 ^ j))).
  under [X in X + _]eq_bigr do rewrite weight_low ?ltn_ord //.
  under [X in _ + X]eq_bigr do rewrite weight_high ?ltn_ord // exprD exprS.
  rewrite /=.
  have E : \sum_(i < 2 ^ w) z ^+ (2 ^ w) * z ^+ i * (t * t ^+ weight w i) =
    (t * z ^+ (2 ^ w)) * \sum_(i < 2 ^ w) z ^+ i * t ^+ weight w i.
    rewrite mulr_sumr; apply: eq_bigr => i _. ring.
  rewrite E IH big_ord_recr /= mulrDr mulr1.
  by rewrite [X in _ + X = _]mulrC.
Qed.

Corollary weighted_bitcount_product (z t : C) w :
  \sum_(x < 2 ^ w) z ^+ x * t ^+ (bitcount w x) =
    \prod_(j < w) (1 + t * z ^+ (2 ^ j)).
Proof.
  under eq_bigr do rewrite -weight_bitcount.
  exact: weighted_binary_product.
Qed.

Corollary weighted_canonical_product (z t : C) w :
  \sum_(x < 2 ^ w) z ^+ x * t ^+ (canonical_HW w (Z.of_nat x)) =
    \prod_(j < w) (1 + t * z ^+ (2 ^ j)).
Proof.
  under eq_bigr do rewrite -weight_canonical_HW.
  exact: weighted_binary_product.
Qed.

Corollary weighted_canonical_average (z t : C) w :
  (\sum_(x < 2 ^ w) z ^+ x * t ^+ (canonical_HW w (Z.of_nat x))) / (2 ^ w)%:R =
    \prod_(j < w) ((1 + t * z ^+ (2 ^ j)) / 2).
Proof.
  rewrite weighted_canonical_product big_split /= prodr_const card_ord.
  by rewrite natrX exprVn.
Qed.

End Weighted.
End CubeEncoding.

Print Assumptions CubeEncoding.weight_bitcount.
Print Assumptions CubeEncoding.weighted_bitcount_product.
Print Assumptions CubeEncoding.weight_canonical_HW.
Print Assumptions CubeEncoding.weighted_canonical_product.
Print Assumptions CubeEncoding.canonical_HW_fold.
Print Assumptions CubeEncoding.weighted_canonical_average.
