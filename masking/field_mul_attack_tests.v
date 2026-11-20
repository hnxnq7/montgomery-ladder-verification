From HB Require Import structures.
From mathcomp Require Import boot order algebra reals field_tactic.
From infotheo Require Import fdist variation_dist.
From Masking Require Import finite_masking word_masking noisy_leakage noisy_trace
  noisy_bit_example noisy_shares noisy_channel_bridge field_mul_gadget field_mul_leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FieldMulAttackTests.
Section Attack.
Variable R : realType.
Local Notation K := [the finComNzRingType of WordMasking.word 0].

(* F2, all twelve stored words, and exactly two independent fair noise bits per snapshot. *)
Definition hw (x : K) : nat := val x.
Definition full_law (s : K) :=
  FieldMulLeakage.square_trace_law R 1 2 hw s.
Definition initial_law (s : K) :=
  share_distribution R s >>= (fun a =>
    FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank a a)).

Definition first (O : finType) n (t : repetitions_type O n.+1) : O := t.1.
Arguments first {O} n _.

Lemma observe_first (S : finComNzRingType) (O : finType) (observe : seq S -> R.-fdist O) n banks :
  fdistmap (first n) (FieldMulLeakage.observe_trace observe n.+1 banks) = observe (head [::] banks).
Proof.
rewrite /first /= map_bind.
have -> : (fun o : O => fdistmap fst (fdistmap (fun rest => (o, rest))
    (FieldMulLeakage.observe_trace observe n (behead banks)))) = (fun o => fdist1 o).
  apply/boolp.funeqP => o. rewrite fdistmap_comp. exact: map_constant.
exact: fdistbind1.
Qed.

Lemma gadget_first (a b : shares K) :
  fdistmap (first 16) (FieldMulLeakage.aggregate_trace_law R 1 2 hw a b) =
    FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank a b).
Proof.
rewrite /FieldMulLeakage.aggregate_trace_law /FieldMulLeakage.trace_law map_bind.
have H ra rb : fdistmap (first 16) (uniform R K >>= (fun rc =>
    FieldMulLeakage.observe_trace (FieldMulLeakage.aggregate_channel R 1 2 hw) 17
      (FieldMulGadget.trace a b ra rb rc))) =
    FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank a b).
  rewrite map_bind.
  have -> : (fun rc => fdistmap (first 16)
      (FieldMulLeakage.observe_trace (FieldMulLeakage.aggregate_channel R 1 2 hw) 17
        (FieldMulGadget.trace a b ra rb rc))) =
      (fun _ : K => FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank a b)).
    apply/boolp.funeqP => rc. rewrite observe_first. reflexivity.
  exact: bind_constant.
have Hra ra : fdistmap (first 16) (uniform R K >>= (fun rb => uniform R K >>= (fun rc =>
    FieldMulLeakage.observe_trace (FieldMulLeakage.aggregate_channel R 1 2 hw) 17
      (FieldMulGadget.trace a b ra rb rc)))) =
    FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank a b).
  rewrite map_bind.
  have -> : (fun rb => fdistmap (first 16) (uniform R K >>= (fun rc =>
      FieldMulLeakage.observe_trace (FieldMulLeakage.aggregate_channel R 1 2 hw) 17
        (FieldMulGadget.trace a b ra rb rc)))) =
      (fun _ : K => FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank a b)).
    exact/boolp.funeqP.
  exact: bind_constant.
have -> : (fun ra => fdistmap (first 16) (uniform R K >>= (fun rb => uniform R K >>= (fun rc =>
    FieldMulLeakage.observe_trace (FieldMulLeakage.aggregate_channel R 1 2 hw) 17
      (FieldMulGadget.trace a b ra rb rc))))) =
    (fun _ : K => FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank a b)).
  exact/boolp.funeqP.
exact: bind_constant.
Qed.

Theorem first_snapshot_projection s : fdistmap (first 16) (full_law s) = initial_law s.
Proof.
rewrite /full_law /FieldMulLeakage.square_trace_law map_bind /initial_law.
congr (fdistbind (share_distribution R s) _).
apply/boolp.funeqP => a. exact: gadget_first.
Qed.

Lemma channel_mass h (y : 'I_15) :
  NoisyChannelBridge.scalar_channel R 14 2 h y =
  ((if (inord (h + 2) : 'I_15) == y then 1 else 0) +
   (if (inord (h + 1) : 'I_15) == y then 2 else 0) +
   (if (inord h : 'I_15) == y then 1 else 0)) / 4.
Proof.
rewrite NoisyChannelBridge.scalar_channel_S fdistbindE big_bool !NoisyBitExample.fair_mass.
rewrite !NoisyChannelBridge.scalar_channel_S !fdistbindE !big_bool !NoisyBitExample.fair_mass.
rewrite /NoisyChannelBridge.scalar_channel /= ?fdistmap1 ?fdist1E.
rewrite /NoisyBitExample.bit_value /= ?addn0 ?addn1 ?addnS ?addn0.
rewrite !(eq_sym y).
case: (_ == y); case: (_ == y); case: (_ == y) => /=;
  field by rewrite ?pnatr_eq0.
Qed.

Lemma initial_mass s y :
  initial_law s y =
  (FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank (split s 0) (split s 0)) y +
   FieldMulLeakage.aggregate_channel R 1 2 hw (FieldMulGadget.initial_bank (split s 1) (split s 1)) y) / 2.
Proof.
rewrite /initial_law /share_distribution bind_map fdistbindE.
under eq_bigr do rewrite /uniform fdist_uniformE WordMasking.word_cardinality.
rewrite !big_ord_recr big_ord0 /=.
field by rewrite ?pnatr_eq0.
Qed.

Lemma initial_zero_mass (y : 'I_15) :
  initial_law 0 y = (nth 0%N [:: 1;2;1;0;1;2;1]%N (val y))%:R / 8.
Proof.
rewrite initial_mass /FieldMulLeakage.aggregate_channel.
change ((NoisyChannelBridge.scalar_channel R 14 2 0 y +
  NoisyChannelBridge.scalar_channel R 14 2 4 y) / 2 =
  (nth 0%N [:: 1;2;1;0;1;2;1]%N (val y))%:R / 8).
rewrite !channel_mass.
case: y => -[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]] // Hi;
  rewrite /= -!val_eqE /= !inordK //=; field by rewrite ?pnatr_eq0.
Qed.

Lemma initial_one_mass (y : 'I_15) :
  initial_law 1 y = (nth 0%N [:: 0;0;2;4;2]%N (val y))%:R / 8.
Proof.
rewrite initial_mass /FieldMulLeakage.aggregate_channel.
change ((NoisyChannelBridge.scalar_channel R 14 2 2 y +
  NoisyChannelBridge.scalar_channel R 14 2 2 y) / 2 =
  (nth 0%N [:: 0;0;2;4;2]%N (val y))%:R / 8).
rewrite !channel_mass.
case: y => -[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]] // Hi;
  rewrite /= -!val_eqE /= !inordK //=; field by rewrite ?pnatr_eq0.
Qed.

Theorem initial_TV : TV (initial_law 0) (initial_law 1) = 3 / 4.
Proof.
rewrite /TV /var_dist.
under eq_bigr do rewrite initial_zero_mass initial_one_mass -mulrBl normrM normfV normr_nat.
rewrite !big_ord_recr big_ord0 /=.
have E12 : (1 : R) - 2 = -1 by field.
rewrite E12 ?subr0 ?subrr ?sub0r ?normr0 ?normrN ?normr_nat ?normr1.
field by rewrite ?pnatr_eq0.
Qed.

(* Lower bound for the actual complete candidate trace, not an isolated surrogate intermediate. *)
Theorem full_trace_TV_lower_bound : 3 / 4 <= TV (full_law 0) (full_law 1).
Proof.
have H := NoisyTrace.map_TV_contraction (full_law 0) (full_law 1) (first 16).
by rewrite !first_snapshot_projection initial_TV in H.
Qed.

End Attack.
End FieldMulAttackTests.

Print Assumptions FieldMulAttackTests.first_snapshot_projection.
Print Assumptions FieldMulAttackTests.initial_TV.
Print Assumptions FieldMulAttackTests.full_trace_TV_lower_bound.
