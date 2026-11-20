From Stdlib Require Import ZArith Bits List Vector.
From quartz.lang Require Import Syntax transform.
From LadderQuartz Require Import hamming_weight packed_storage.
From Masking Require Import cube_encoding.

Set Default Proof Mode "Classic".
Open Scope Z_scope.

Module QuartzHWEncoding.

Theorem word_HW_exact n (word : bits n) :
  RegisterHW.word_HW word =
    CubeEncoding.canonical_HW (Z.to_nat n) (Zmod.unsigned word).
Proof.
  rewrite CubeEncoding.canonical_HW_fold. reflexivity.
Qed.

Theorem encode_HW_exact (width : nat) x :
  0 <= x < 2 ^ Z.of_nat width ->
  RegisterHW.word_HW (bits.of_Z (Z.of_nat width) x) = CubeEncoding.canonical_HW width x.
Proof.
  intros Hx. rewrite word_HW_exact, bits.unsigned_of_Z_small by assumption.
  now rewrite Nat2Z.id.
Qed.

Theorem bank_HW_exact n count (words : Vector.t (bits n) count) :
  RegisterHW.bank_HW words =
    List.fold_right (fun word acc =>
      (CubeEncoding.canonical_HW (Z.to_nat n) (Zmod.unsigned word) + acc)%nat)
      0%nat (Vector.to_list words).
Proof.
  induction words; cbn [RegisterHW.bank_HW Vector.to_list List.fold_right].
  - reflexivity.
  - rewrite word_HW_exact, IHwords. reflexivity.
Qed.

Lemma array_HW_exact n count (words : Vector.t (bits n) count) :
  PackedStorage.storage_HW (Syntax.type.Array (Syntax.type.Bits n) count) words =
    RegisterHW.bank_HW words.
Proof.
  induction words; cbn [PackedStorage.storage_HW PackedStorage.array_HW RegisterHW.bank_HW].
  - reflexivity.
  - now rewrite <- IHwords.
Qed.

Theorem packed_bank_HW_exact n count (words : Vector.t (bits n) count) :
  0 <= n ->
  RegisterHW.word_HW
    (@transform.type.pack (Syntax.type.Array (Syntax.type.Bits n) count) words) =
    List.fold_right (fun word acc =>
      (CubeEncoding.canonical_HW (Z.to_nat n) (Zmod.unsigned word) + acc)%nat)
      0%nat (Vector.to_list words).
Proof.
  intros Hn. rewrite PackedStorage.pack_HW by exact Hn.
  rewrite array_HW_exact. apply bank_HW_exact.
Qed.

End QuartzHWEncoding.

Print Assumptions QuartzHWEncoding.word_HW_exact.
Print Assumptions QuartzHWEncoding.encode_HW_exact.
Print Assumptions QuartzHWEncoding.bank_HW_exact.
Print Assumptions QuartzHWEncoding.packed_bank_HW_exact.
