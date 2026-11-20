From HB Require Import structures.
From mathcomp Require Import boot order algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module ArithmeticShares.

Section Sharing.
Variable K : finComNzRingType.

Definition shares n := {ffun 'I_n -> K}.
Definition masks n := {ffun 'I_n * 'I_n -> K}.

Definition reconstruct n (a : shares n) :=
  \sum_i a i.

Definition add n (a b : shares n) : shares n :=
  [ffun i => a i + b i].

Definition sub n (a b : shares n) : shares n :=
  [ffun i => a i - b i].

Lemma add_correct n (a b : shares n) :
  reconstruct (add a b) = reconstruct a + reconstruct b.
Proof. by rewrite /reconstruct /add; under eq_bigr do rewrite ffunE; rewrite big_split. Qed.

Lemma sub_correct n (a b : shares n) :
  reconstruct (sub a b) = reconstruct a - reconstruct b.
Proof. by rewrite /reconstruct /sub; under eq_bigr do rewrite ffunE; rewrite sumrB. Qed.

(* A distinguished share compensates for the other entries; there is at least one share. *)
Definition share n (s : K) (r : shares n.+1) : shares n.+1 :=
  [ffun i => r i + if i == ord0 then s - reconstruct r else 0].

Lemma share_correct n (s : K) (r : shares n.+1) : reconstruct (share s r) = s.
Proof.
rewrite /reconstruct /share.
under eq_bigr do rewrite ffunE.
rewrite big_split /= -big_mkcond big_pred1_eq /reconstruct.
by rewrite addrC subrK.
Qed.

(* Each unordered pair uses one mask with opposite signs; this is not XOR sharing. *)
Definition multiply n (a b : shares n) (r : masks n) : shares n :=
  [ffun i => a i * b i - \sum_(j : 'I_n | (i < j)%N) r (i, j) +
    \sum_(j : 'I_n | (j < i)%N) (r (j, i) + a j * b i + a i * b j)].

Lemma sum_split_index n (i : 'I_n) (f : 'I_n -> K) :
  \sum_j f j = f i + \sum_(j : 'I_n | (i < j)%N) f j + \sum_(j : 'I_n | (j < i)%N) f j.
Proof.
rewrite (bigD1 i) // -addrA; congr (_ + _).
rewrite (bigID (fun j : 'I_n => (i < j)%N)) /=.
congr (_ + _); apply: eq_bigl => j;
  rewrite -val_eqE; case: ltngtP => //=.
Qed.

Lemma lower_upper n (f : 'I_n -> 'I_n -> K) :
  \sum_(i : 'I_n) \sum_(j : 'I_n | (j < i)%N) f j i =
    \sum_(i : 'I_n) \sum_(j : 'I_n | (i < j)%N) f i j.
Proof.
under [LHS]eq_bigr do rewrite big_mkcond.
rewrite exchange_big.
by apply: eq_bigr => i _; rewrite -big_mkcond.
Qed.

Theorem multiply_correct n (a b : shares n) (r : masks n) :
  reconstruct (multiply a b r) = reconstruct a * reconstruct b.
Proof.
rewrite /reconstruct /multiply.
under eq_bigr do rewrite ffunE.
rewrite big_split /= sumrB.
rewrite lower_upper.
under [X in _ + X]eq_bigr do rewrite !big_split.
rewrite !big_split /=.
rewrite !addrA subrK.
rewrite mulr_suml.
under [RHS]eq_bigr => i _ do rewrite mulr_sumr (sum_split_index i).
rewrite !big_split /=.
congr (_ + _ + _).
by rewrite -lower_upper.
Qed.

Corollary square_correct n (a : shares n) (r : masks n) :
  reconstruct (multiply a a r) = (reconstruct a)^+2.
Proof. by rewrite multiply_correct expr2. Qed.

Definition diagonal n (a b : shares n) : shares n :=
  [ffun i => a i * b i].

Definition increment n (c : shares n) (i : 'I_n) (x : K) : shares n :=
  [ffun k => c k + if k == i then x else 0].

Lemma increment_reconstruct n (c : shares n) i x :
  reconstruct (increment c i x) = reconstruct c + x.
Proof.
rewrite /reconstruct /increment.
under eq_bigr do rewrite ffunE.
by rewrite big_split /= -big_mkcond big_pred1_eq.
Qed.

Definition cross n (a b : shares n) (ij : 'I_n * 'I_n) :=
  a ij.1 * b ij.2 + a ij.2 * b ij.1.

(* The two writes are sequential; the operands and mask matrix remain unchanged. *)
Definition pair_update n (a b : shares n) (r : masks n) (c : shares n)
    (ij : 'I_n * 'I_n) : shares n :=
  increment (increment c ij.1 (- r ij)) ij.2 (r ij + cross a b ij).

Lemma pair_update_reconstruct n (a b : shares n) (r : masks n) c ij :
  reconstruct (pair_update a b r c ij) = reconstruct c + cross a b ij.
Proof. by rewrite /pair_update !increment_reconstruct addrA subrK. Qed.

(* Public enumeration visits each unordered pair exactly once. *)
Definition pair_order n :=
  filter (fun ij : 'I_n * 'I_n => (ij.1 < ij.2)%N)
    (index_enum [the finType of ('I_n * 'I_n)%type]).

Definition sequential_multiply n (a b : shares n) (r : masks n) : shares n :=
  foldl (pair_update a b r) (diagonal a b) (pair_order n).

Lemma pair_fold_reconstruct n (a b : shares n) (r : masks n) pairs c :
  reconstruct (foldl (pair_update a b r) c pairs) =
    reconstruct c + \sum_(ij <- pairs) cross a b ij.
Proof.
elim: pairs c => [|ij pairs IH] c; first by rewrite /= big_nil addr0.
by rewrite /= IH pair_update_reconstruct big_cons /cross !addrA.
Qed.

Lemma pair_order_sum n (a b : shares n) :
  \sum_(ij <- pair_order n) cross a b ij =
    \sum_(i : 'I_n) \sum_(j : 'I_n | (i < j)%N) (a i * b j + a j * b i).
Proof.
rewrite /pair_order /cross big_filter big_mkcond.
rewrite -(pair_bigA _ (fun i j : 'I_n =>
  if (i < j)%N then a i * b j + a j * b i else 0)).
by apply: eq_bigr => i _; rewrite -big_mkcond.
Qed.

Theorem sequential_multiply_correct n (a b : shares n) (r : masks n) :
  reconstruct (sequential_multiply a b r) = reconstruct a * reconstruct b.
Proof.
rewrite /sequential_multiply pair_fold_reconstruct pair_order_sum /reconstruct /diagonal.
under [X in X + _]eq_bigr do rewrite ffunE.
under [X in _ + X]eq_bigr do rewrite big_split.
rewrite big_split /= addrA.
rewrite mulr_suml.
under [RHS]eq_bigr => i _ do rewrite mulr_sumr (sum_split_index i).
rewrite !big_split /=.
congr (_ + _ + _).
by rewrite -lower_upper.
Qed.

End Sharing.
End ArithmeticShares.

Print Assumptions ArithmeticShares.share_correct.
Print Assumptions ArithmeticShares.add_correct.
Print Assumptions ArithmeticShares.sub_correct.
Print Assumptions ArithmeticShares.multiply_correct.
Print Assumptions ArithmeticShares.sequential_multiply_correct.
