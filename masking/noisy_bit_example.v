From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist variation_dist.
From Stdlib Require Import Lia.
From Masking Require Import finite_masking noisy_leakage.
From mathcomp Require Import field_tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory FiniteMasking NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module NoisyBitExample.
Section Example.
Variable R : realType.

Definition fair : R.-fdist bool :=
  fdist_uniform card_bool.

Definition bit_value (b : bool) : nat :=
  if b then 1%N else 0%N.

Definition masked_hw (s r : bool) : 'I_3 :=
  inord (bit_value r + bit_value (xorb s r)).

Definition dual_hw (s : bool) : 'I_3 :=
  inord (bit_value s + bit_value (negb s)).

Definition plain_hw (s : bool) : 'I_3 :=
  inord (bit_value s).

Lemma masked_reconstruct s r : xorb r (xorb s r) = s.
Proof. by case: s; case: r. Qed.

Lemma dual_first s : (s, negb s).1 = s.
Proof. reflexivity. Qed.

Lemma plain_value_correct s : val (plain_hw s) = bit_value s.
Proof. by case: s; rewrite /plain_hw /= inordK. Qed.

Definition add_noise (h : 'I_3) (b1 b2 : bool) : 'I_5 :=
  inord (val h + bit_value b1 + bit_value b2).

Lemma add_noise_no_wrap h b1 b2 :
  val (add_noise h b1 b2) = (val h + bit_value b1 + bit_value b2)%N.
Proof.
rewrite /add_noise /= inordK //.
have /ltP H := ltn_ord h.
case: b1; case: b2; rewrite /bit_value /= ?addn0 ?addn1; apply/ltP; lia.
Qed.

(* All schemes use the same channel, with two fresh independent noise bits. *)
Definition channel (h : 'I_3) : R.-fdist 'I_5 :=
  fair >>= (fun b1 => fdistmap (add_noise h b1) fair).

Definition masked_law (s : bool) : R.-fdist 'I_5 :=
  fair >>= (fun r => channel (masked_hw s r)).

Definition plain_law (s : bool) : R.-fdist 'I_5 :=
  channel (plain_hw s).

Definition dual_law (s : bool) : R.-fdist 'I_5 :=
  channel (dual_hw s).

Lemma dual_hw_constant s : dual_hw s = inord 1.
Proof. by case: s. Qed.

Theorem dual_laws_equal s t : dual_law s = dual_law t.
Proof. by rewrite /dual_law !dual_hw_constant. Qed.

Lemma fair_mass b : fair b = 2^-1.
Proof. by rewrite /fair fdist_uniformE card_bool. Qed.

Lemma map_fair_mass (A : finType) (f : bool -> A) y :
  fdistmap f fair y =
    (if f true == y then 2^-1 else 0) + (if f false == y then 2^-1 else 0).
Proof. by rewrite fdistmapE big_mkcond big_bool !inE !fair_mass. Qed.

Lemma channel_mass h y :
  channel h y =
  ((if add_noise h true true == y then 1 else 0) +
   (if add_noise h true false == y then 1 else 0) +
   (if add_noise h false true == y then 1 else 0) +
   (if add_noise h false false == y then 1 else 0)) / 4.
Proof.
rewrite /channel fdistbindE big_bool.
rewrite !map_fair_mass !fair_mass /=.
case: (_ == y); case: (_ == y); case: (_ == y); case: (_ == y);
  field by rewrite ?pnatr_eq0.
Qed.

Lemma masked_mass s y :
  masked_law s y = (channel (masked_hw s true) y + channel (masked_hw s false) y) / 2.
Proof.
rewrite /masked_law fdistbindE big_bool !fair_mass /=.
field by rewrite ?pnatr_eq0.
Qed.

Lemma masked_false_mass (y : 'I_5) :
  masked_law false y = (nth 0%N [:: 1;2;2;2;1]%N (val y))%:R / 8.
Proof.
case: y => -[|[|[|[|[|i]]]]] // Hi;
  rewrite masked_mass !channel_mass /masked_hw /bit_value /= -!val_eqE /= /add_noise
    /= !inordK //=; field by rewrite ?pnatr_eq0.
Qed.

Lemma masked_true_mass (y : 'I_5) :
  masked_law true y = (nth 0%N [:: 0;2;4;2;0]%N (val y))%:R / 8.
Proof.
case: y => -[|[|[|[|[|i]]]]] // Hi;
  rewrite masked_mass !channel_mass /masked_hw /bit_value /= -!val_eqE /= /add_noise
    /= !inordK //=; field by rewrite ?pnatr_eq0.
Qed.

Lemma plain_false_mass (y : 'I_5) :
  plain_law false y = (nth 0%N [:: 1;2;1;0;0]%N (val y))%:R / 4.
Proof.
case: y => -[|[|[|[|[|i]]]]] // Hi;
  rewrite /plain_law channel_mass /plain_hw /bit_value /= -!val_eqE /= /add_noise
    /= !inordK //=; field by rewrite ?pnatr_eq0.
Qed.

Lemma plain_true_mass (y : 'I_5) :
  plain_law true y = (nth 0%N [:: 0;1;2;1;0]%N (val y))%:R / 4.
Proof.
case: y => -[|[|[|[|[|i]]]]] // Hi;
  rewrite /plain_law channel_mass /plain_hw /bit_value /= -!val_eqE /= /add_noise
    /= !inordK //=; field by rewrite ?pnatr_eq0.
Qed.

Theorem masked_TV : TV (masked_law false) (masked_law true) = 1 / 4.
Proof.
rewrite /TV /var_dist.
under eq_bigr do rewrite masked_false_mass masked_true_mass -mulrBl normrM normfV normr_nat.
rewrite !big_ord_recr big_ord0 /=.
have E : (2 : R) - 4 = -2 by field.
rewrite E ?subr0 ?subrr ?normr0 ?normrN ?normr_nat ?normr1.
field by rewrite ?pnatr_eq0.
Qed.

Theorem plain_TV : TV (plain_law false) (plain_law true) = 1 / 2.
Proof.
rewrite /TV /var_dist.
under eq_bigr do rewrite plain_false_mass plain_true_mass -mulrBl normrM normfV normr_nat.
rewrite !big_ord_recr big_ord0 /=.
have E21 : (2 : R) - 1 = 1 by field.
have E12 : (1 : R) - 2 = -1 by field.
rewrite E21 E12 ?subr0 ?subrr ?sub0r ?normr0 ?normrN ?normr_nat ?normr1.
field by rewrite ?pnatr_eq0.
Qed.

Theorem dual_TV : TV (dual_law false) (dual_law true) = 0.
Proof. apply: equal_law_TV_zero. exact: dual_laws_equal. Qed.

Theorem masked_laws_distinct : masked_law false <> masked_law true.
Proof.
move=> H.
have E := equal_law_TV_zero H.
rewrite masked_TV in E.
have Hnz : (1 / 4 : R) != 0 by rewrite mulf_eq0 oner_eq0 invr_eq0 pnatr_eq0.
by rewrite E eqxx in Hnz.
Qed.

End Example.
End NoisyBitExample.

Print Assumptions NoisyBitExample.masked_reconstruct.
Print Assumptions NoisyBitExample.add_noise_no_wrap.
Print Assumptions NoisyBitExample.dual_laws_equal.
Print Assumptions NoisyBitExample.masked_TV.
Print Assumptions NoisyBitExample.plain_TV.
Print Assumptions NoisyBitExample.dual_TV.
Print Assumptions NoisyBitExample.masked_laws_distinct.
