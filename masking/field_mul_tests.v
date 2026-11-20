From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking field_refresh field_mul_gadget noisy_shares word_masking.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FieldMulTests.
Section Sampling.
Variable R : realType.
Variable K : finComNzRingType.

(* Independent masks, with the input sharings fixed. This excludes the trace prefix. *)
Definition refreshed_operands (a b : shares K) :=
  uniform R K >>= (fun ra =>
    fdistmap (fun rb => (refresh a ra, refresh b rb)) (uniform R K)).

Theorem refreshed_operands_product a b :
  refreshed_operands a b =
    (share_distribution R (reconstruct a)) `x (share_distribution R (reconstruct b)).
Proof.
rewrite /refreshed_operands -(FieldRefresh.refresh_pair_law R a)
  -(FieldRefresh.refresh_pair_law R b) NoisyShares.product_bind bind_map.
congr (fdistbind (uniform R K) _).
apply/boolp.funeqP => ra. by rewrite fdistmap_comp.
Qed.

Corollary square_operands_product a :
  refreshed_operands a a =
    (share_distribution R (reconstruct a)) `x (share_distribution R (reconstruct a)).
Proof. exact: refreshed_operands_product. Qed.

Definition sampled_multiply (a b : shares K) :=
  uniform R K >>= (fun ra => uniform R K >>= (fun rb =>
    fdistmap (FieldMulGadget.multiply a b ra rb) (uniform R K))).

Theorem sampled_output_pair_law a b :
  sampled_multiply a b = share_distribution R (reconstruct a * reconstruct b).
Proof.
rewrite /sampled_multiply.
have H ra : (uniform R K >>= (fun rb =>
    fdistmap (FieldMulGadget.multiply a b ra rb) (uniform R K))) =
    share_distribution R (reconstruct a * reconstruct b).
  have -> : (fun rb => fdistmap (FieldMulGadget.multiply a b ra rb) (uniform R K)) =
      (fun _ : K => share_distribution R (reconstruct a * reconstruct b)).
    apply/boolp.funeqP => rb. exact: FieldMulGadget.output_pair_law.
  exact: bind_constant.
have -> : (fun ra => uniform R K >>= (fun rb =>
    fdistmap (FieldMulGadget.multiply a b ra rb) (uniform R K))) =
    (fun _ : K => share_distribution R (reconstruct a * reconstruct b)).
  exact/boolp.funeqP.
exact: bind_constant.
Qed.

Corollary sampled_multiply_correct a b :
  fdistmap (@reconstruct K) (sampled_multiply a b) = fdist1 (reconstruct a * reconstruct b).
Proof. by rewrite sampled_output_pair_law reconstruction_distribution. Qed.

Corollary sampled_square_correct a :
  fdistmap (@reconstruct K) (sampled_multiply a a) = fdist1 ((reconstruct a)^+2).
Proof. by rewrite sampled_multiply_correct expr2. Qed.

Corollary sampled_final_Y_uniform a b :
  fdistmap snd (sampled_multiply a b) = uniform R K.
Proof. by rewrite sampled_output_pair_law second_share_uniform. Qed.

End Sampling.

Example square_refresh_masks_may_differ (a : shares [the finComNzRingType of WordMasking.word 1]) :
  reconstruct (FieldMulGadget.multiply a a 0 1 2) = (reconstruct a)^+2.
Proof. exact: FieldMulGadget.square_correct. Qed.

Example multiply_mod_four :
  reconstruct (FieldMulGadget.multiply
    (split (3 : WordMasking.word 1) 1) (split 2 3) 0 1 2) = 2.
Proof.
rewrite FieldMulGadget.multiply_correct !split_correct.
apply/val_inj. by vm_compute.
Qed.

End FieldMulTests.

Print Assumptions FieldMulTests.refreshed_operands_product.
Print Assumptions FieldMulTests.square_operands_product.
Print Assumptions FieldMulTests.sampled_output_pair_law.
Print Assumptions FieldMulTests.sampled_square_correct.
