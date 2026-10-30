From Stdlib Require Import ZArith Bits List Lia.
Import ListNotations.
Open Scope Z_scope.

Module Curve25519Words.
  Definition word := bits 32.
  Definition radix : Z := 2 ^ 32.
  Definition modulus : Z := 2 ^ 255 - 19.

  Fixpoint encode (count : nat) (x : Z) : list word :=
    match count with
    | O => []
    | S rest => bits.of_Z 32 x :: encode rest (x / radix)
    end.

  Fixpoint decode (xs : list word) : Z :=
    match xs with
    | [] => 0
    | x :: rest => Zmod.unsigned x + radix * decode rest
    end.

  Lemma encode_length count x : length (encode count x) = count.
  Proof. revert x. induction count; intro x; cbn; auto. Qed.

  Lemma encode_decode count x :
    0 <= x < radix ^ Z.of_nat count -> decode (encode count x) = x.
  Proof.
    revert x. induction count as [|count IH]; intros x Hx.
    - cbn in *. lia.
    - cbn [encode decode]. rewrite bits.unsigned_of_Z.
      assert (Hb : 0 < radix) by (unfold radix; lia).
      assert (Hpow : 0 < radix ^ Z.of_nat count) by (apply Z.pow_pos_nonneg; lia).
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
      rewrite IH.
      + unfold radix. pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)). lia.
      + split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; nia.
  Qed.

  Theorem field_roundtrip x :
    0 <= x < modulus -> decode (encode 8 x) = x.
  Proof.
    intro Hx. apply encode_decode. unfold modulus in Hx. unfold radix.
    change (0 <= x < 2 ^ 256). split; [lia |].
    assert (2 ^ 255 - 19 < 2 ^ 256) by (vm_compute; reflexivity). lia.
  Qed.

  Example zero_words : encode 8 0 = repeat (bits.of_Z 32 0) 8.
  Proof. vm_compute. reflexivity. Qed.

  Example largest_field_element :
    map Zmod.unsigned (encode 8 (modulus - 1)) =
      [4294967276; 4294967295; 4294967295; 4294967295;
       4294967295; 4294967295; 4294967295; 2147483647].
  Proof. vm_compute. reflexivity. Qed.

  Print Assumptions field_roundtrip.
End Curve25519Words.
