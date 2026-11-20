From Stdlib Require Import ZArith Bits List Vector.
From mathcomp Require Import boot algebra.
From quartz.lang Require Import Syntax transform.
From LadderQuartz Require Import hamming_weight packed_storage.
From Masking Require Import fiat_field cube_encoding quartz_hw_encoding.
From Crypto Require Import Spec.ModularArithmetic Arithmetic.ModularArithmeticTheorems.

Set Default Proof Mode "Classic".
Open Scope Z_scope.

Module QuartzMaskedHW.

Definition decode (word : bits 255) : FiatField.curve25519 :=
  FiatField.encode FiatField.curve25519_modulus_gt1 (Zmod.unsigned word).

Definition canonical (word : bits 255) : Prop :=
  0 <= Zmod.unsigned word < Z.pos FiatField.curve25519_modulus.

Lemma decode_canonical word : canonical word -> F.to_Z (decode word) = Zmod.unsigned word.
Proof.
  intros H. unfold decode, FiatField.encode.
  rewrite F.to_Z_of_Z. apply Z.mod_small. exact H.
Qed.

Theorem word_HW_decode word : canonical word ->
  RegisterHW.word_HW word = CubeEncoding.canonical_HW 255 (F.to_Z (decode word)).
Proof.
  intros H. rewrite (decode_canonical word H).
  apply QuartzHWEncoding.word_HW_exact.
Qed.

Theorem bank_HW_decode count (words : Vector.t (bits 255) count) :
  List.Forall canonical (Vector.to_list words) ->
  RegisterHW.bank_HW words =
    List.fold_right (fun word acc =>
      (CubeEncoding.canonical_HW 255 (F.to_Z (decode word)) + acc)%nat)
      0%nat (Vector.to_list words).
Proof.
  induction words; intros H; cbn [RegisterHW.bank_HW Vector.to_list List.fold_right].
  - reflexivity.
  - inversion H; subst.
    erewrite word_HW_decode; [|eassumption].
    erewrite IHwords; [reflexivity|eassumption].
Qed.

End QuartzMaskedHW.

Module QuartzMaskedHWTests.
Definition modulus_word : bits 255 :=
  bits.of_Z 255 (Z.pos FiatField.curve25519_modulus).

(* Modular decoding alone does not preserve the physical bit count. *)
Example modulus_decodes_zero : F.to_Z (QuartzMaskedHW.decode modulus_word) = 0.
Proof. vm_compute. reflexivity. Qed.

Example modulus_storage_HW : RegisterHW.word_HW modulus_word = 253%nat.
Proof. vm_compute. reflexivity. Qed.

Example modulus_not_canonical : ~ QuartzMaskedHW.canonical modulus_word.
Proof. vm_compute. intros H. destruct H as [_ H]. discriminate. Qed.
End QuartzMaskedHWTests.

Print Assumptions QuartzMaskedHW.bank_HW_decode.
Print Assumptions QuartzMaskedHWTests.modulus_storage_HW.
