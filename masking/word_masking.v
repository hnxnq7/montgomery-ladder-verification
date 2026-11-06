From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module WordMasking.

(* A positive-width word: width = n + 1, arithmetic modulo 2^(n + 1). *)
Definition word (n : nat) :=
  'Z_(2 ^ n.+1).

Lemma word_cardinality n : #|word n| = (2 ^ n.+1)%N.
Proof.
rewrite /word card_ord Zp_cast //.
by rewrite -{1}(expn0 2) ltn_exp2l.
Qed.

Section WordDistributions.
Variable R : realType.
Variable n : nat.
Local Notation K := [the finZmodType of word n].

Theorem masked_word_uniform (s : word n) :
  fdistmap (fun r => s + r) (@FiniteMasking.uniform R K) = FiniteMasking.uniform R K.
Proof. exact: FiniteMasking.uniform_add. Qed.

Theorem masked_word_independent (s t : word n) :
  fdistmap (fun r => s + r) (@FiniteMasking.uniform R K) =
  fdistmap (fun r => t + r) (@FiniteMasking.uniform R K).
Proof. by rewrite !masked_word_uniform. Qed.

End WordDistributions.

(* MathComp's modular ring has at least two elements; zero bits need a singleton. *)
Definition word_type (width : nat) : finType :=
  match width with
  | 0 => [the finType of (unit : Type)]
  | n.+1 => [the finType of (word n : Type)]
  end.

Definition mask_law (R : realType) (width : nat) : word_type width -> R.-fdist (word_type width) :=
  match width as w return word_type w -> R.-fdist (word_type w) with
  | 0 => fun _ => fdist1 tt
  | n.+1 => fun s => fdistmap (fun r => s + r)
      (@FiniteMasking.uniform R [the finZmodType of word n])
  end.

Theorem every_width_independent (R : realType) width (s t : word_type width) :
  mask_law R s = mask_law R t.
Proof.
case: width s t => [|n] s t; first by [].
exact: masked_word_independent.
Qed.

Example two_bit_zero_copies :
  map val (FiniteMasking.copies (0 : word 1)) = [:: 0; 1; 2; 3]%N.
Proof. rewrite /FiniteMasking.copies !enum_ordSl enum_ord0. by vm_compute. Qed.

Example two_bit_one_copies :
  map val (FiniteMasking.copies (1 : word 1)) = [:: 1; 2; 3; 0]%N.
Proof. rewrite /FiniteMasking.copies !enum_ordSl enum_ord0. by vm_compute. Qed.

End WordMasking.
