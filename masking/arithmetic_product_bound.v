From mathcomp Require Import boot order algebra reals.
From infotheo Require Import bigop_ext fdist variation_dist.
From Masking Require Import arithmetic_channel noisy_leakage noisy_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory ArithmeticChannel NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module ArithmeticProductBound.
Section Product.
Variable R : realType.
Variables I A : finType.
Local Notation Output := [the finType of {ffun I -> A}].

Definition replace_law (laws : I -> R.-fdist A) (i : I) (d : R.-fdist A) :=
  fun j => if j == i then d else laws j.

Lemma independent_replaceE laws i d (out : Output) :
  independent (replace_law laws i d) out = d (out i) * \prod_(j | j != i) laws j (out j).
Proof.
rewrite independentE (bigD1 i) // /replace_law eqxx.
congr (_ * _). by apply: eq_bigr => j Hj; rewrite (negbTE Hj).
Qed.

Lemma replace_TV laws i d :
  TV (independent laws) (independent (replace_law laws i d)) = TV (laws i) d.
Proof.
rewrite /TV; congr (_ / 2).
rewrite /var_dist.
transitivity (\sum_(out : Output) \prod_j
  (if j == i then `|laws i (out j) - d (out j)| else laws j (out j))).
- apply: eq_bigr => out _.
  rewrite independent_replaceE independentE (bigD1 i) //.
  rewrite -mulrBl normrM.
  have Hnonnegative : 0 <= \prod_(j | j != i) laws j (out j).
    apply: prodr_ge0 => j _. exact: FDist.ge0.
  rewrite (ger0_norm Hnonnegative).
  rewrite [RHS](bigD1 i) // eqxx.
  congr (_ * _). by apply: eq_bigr => j Hj; rewrite (negbTE Hj).
- rewrite -(bigA_distr_bigA (fun j y =>
    if j == i then `|laws i y - d y| else laws j y)) /=.
  rewrite (bigD1 i) // eqxx.
  have E : \prod_(j | j != i) \sum_(y : A)
      (if j == i then `|laws i y - d y| else laws j y) = 1.
    apply: big1 => j Hj. rewrite (negbTE Hj). exact: FDist.f1.
  by rewrite E /= mulr1.
Qed.

Variables laws1 laws2 : I -> R.-fdist A.

Fixpoint hybrid (indices : seq I) : I -> R.-fdist A :=
  if indices is i :: rest then replace_law (hybrid rest) i (laws2 i) else laws1.

Lemma hybrid_outside indices i : i \notin indices -> hybrid indices i = laws1 i.
Proof.
elim: indices => [|j rest IH] //=.
rewrite in_cons negb_or => /andP [Hij Hrest].
by rewrite /replace_law (negbTE Hij) IH.
Qed.

Lemma hybrid_inside indices i : i \in indices -> hybrid indices i = laws2 i.
Proof.
elim: indices => [|j rest IH] //=.
rewrite in_cons => /orP [/eqP ->|Hrest]; first by rewrite /replace_law eqxx.
rewrite /replace_law. case: ifP => [/eqP ->|_]; first reflexivity.
exact: IH Hrest.
Qed.

Lemma hybrid_TV_bound indices : uniq indices ->
  TV (independent laws1) (independent (hybrid indices)) <=
    \sum_(i <- indices) TV (laws1 i) (laws2 i).
Proof.
elim: indices => [|i rest IH] /=; first by rewrite big_nil TV_self.
move=> /andP [Hfresh Huniq].
apply: le_trans (NoisyTrace.TV_triangle _ (independent (hybrid rest)) _) _.
rewrite replace_TV (hybrid_outside Hfresh) big_cons addrC.
exact: lerD (lexx _) (IH Huniq).
Qed.

(* The full joint law is an explicit independent product, not an arbitrary law with these marginals. *)
Theorem independent_TV_bound :
  TV (independent laws1) (independent laws2) <= \sum_i TV (laws1 i) (laws2 i).
Proof.
have E : hybrid (index_enum I) = laws2.
  apply/boolp.funeqP => i. apply: hybrid_inside. exact: mem_index_enum.
have H := hybrid_TV_bound (index_enum_uniq I).
by rewrite E in H.
Qed.

Theorem independent_channel_bound (B : finType) (channel : Output -> R.-fdist B) :
  TV (apply_channel (independent laws1) channel) (apply_channel (independent laws2) channel) <=
    \sum_i TV (laws1 i) (laws2 i).
Proof.
exact: le_trans (channel_TV_contraction _ _ channel) independent_TV_bound.
Qed.

Corollary independent_map_bound (B : finType) (observe : Output -> B) :
  TV (fdistmap observe (independent laws1)) (fdistmap observe (independent laws2)) <=
    \sum_i TV (laws1 i) (laws2 i).
Proof. exact: independent_channel_bound (fun out => fdist1 (observe out)). Qed.

End Product.
End ArithmeticProductBound.

Print Assumptions ArithmeticProductBound.independent_TV_bound.
Print Assumptions ArithmeticProductBound.independent_map_bound.
