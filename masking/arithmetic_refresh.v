From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import ssr_ext bigop_ext fdist.
From Masking Require Import finite_masking shared_ladder arithmetic_shares arithmetic_privacy history_semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module ArithmeticRefresh.
Section Refresh.
Variable R : realType.
Variable K : finComNzRingType.
Variable n : nat.
Local Notation V := [the finZmodType of {ffun 'I_n.+1 -> K}].
Local Notation M := [the finZmodType of {ffun 'I_n -> K}].
Local Notation P := [the finZmodType of (K * M)%type].

Definition tail (a : V) : M := [ffun i => a (lift ord0 i)].

Definition join (p : P) : V :=
  [ffun i => match unlift ord0 i with Some j => p.2 j | None => p.1 end].

Lemma join_anchor p : join p ord0 = p.1.
Proof. by rewrite /join ffunE unlift_none. Qed.

Lemma join_tail p i : join p (lift ord0 i) = p.2 i.
Proof. by rewrite /join ffunE liftK. Qed.

Definition split (a : V) : P := (a ord0, tail a).

Lemma join_split : cancel split join.
Proof.
move=> a; apply/ffunP => i; rewrite /join /split ffunE /=.
by case: (unliftP ord0 i) => [j ->|->]; rewrite /tail ?ffunE.
Qed.

Lemma split_join : cancel join split.
Proof.
move=> [h r]; rewrite /split join_anchor /=; congr (_, _).
by apply/ffunP => i; rewrite /tail ffunE join_tail.
Qed.

Lemma reconstruct_split a :
  ArithmeticShares.reconstruct a = a ord0 + \sum_i tail a i.
Proof.
rewrite /ArithmeticShares.reconstruct big_ord_recl.
by congr (_ + _); apply: eq_bigr => i _; rewrite /tail ffunE.
Qed.

Definition canonical (s : K) (r : M) : V := join (s - \sum_i r i, r).

Lemma canonical_correct s r : ArithmeticShares.reconstruct (canonical s r) = s.
Proof.
rewrite reconstruct_split /canonical join_anchor.
have -> : tail (join (s - \sum_i r i, r)) = r by exact: (congr1 snd (split_join _)).
by rewrite subrK.
Qed.

(* Exactly n masks refresh n+1 shares; no reconstruction occurs in this definition. *)
Definition refresh (a : V) (r : M) : V :=
  join (a ord0 - \sum_i r i, tail a + r).

Lemma refresh_anchor a r : refresh a r ord0 = a ord0 - \sum_i r i.
Proof. exact: join_anchor. Qed.

Lemma refresh_tail a r i : refresh a r (lift ord0 i) = a (lift ord0 i) + r i.
Proof. by rewrite /refresh join_tail /tail !ffunE. Qed.

Lemma refresh_as_canonical a r :
  refresh a r = canonical (ArithmeticShares.reconstruct a) (tail a + r).
Proof.
have Hsum : \sum_i (tail a + r) i = \sum_i tail a i + \sum_i r i.
  by under eq_bigr do rewrite ffunE; rewrite big_split.
rewrite /refresh /canonical reconstruct_split Hsum.
by rewrite opprD !addrA addrK.
Qed.

Theorem refresh_correct a r :
  ArithmeticShares.reconstruct (refresh a r) = ArithmeticShares.reconstruct a.
Proof. by rewrite refresh_as_canonical canonical_correct. Qed.

Lemma share_as_canonical s a : ArithmeticShares.share s a = canonical s (tail a).
Proof.
apply/ffunP => i; case: (unliftP ord0 i) => [j ->|->].
- by rewrite /ArithmeticShares.share ffunE lift_eqF addr0 /canonical join_tail /tail ffunE.
- rewrite /ArithmeticShares.share ffunE eqxx /canonical join_anchor reconstruct_split.
  by rewrite opprD !addrA (addrAC (a ord0) s (- a ord0)) subrr add0r.
Qed.

Lemma uniform_join : fdistmap join (uniform R P) = uniform R V.
Proof.
apply/fdist_ext => a.
rewrite fdistmapE /= -{1}(join_split a) (big_pred1_inj (can_inj split_join)).
rewrite /uniform !fdist_uniformE.
have Hcard : #|P| = #|V| by apply: bij_eq_card; exists split; [exact: split_join|exact: join_split].
by rewrite Hcard.
Qed.

Lemma uniform_pair : uniform R P = (uniform R K) `x (uniform R M).
Proof.
apply/fdist_ext => -[h r].
by rewrite fdist_prodE /uniform !fdist_uniformE card_prod natrM invfM.
Qed.

Lemma uniform_tail : fdistmap tail (uniform R V) = uniform R M.
Proof.
rewrite -uniform_join fdistmap_comp.
have -> : tail \o join = snd.
  apply/boolp.funeqP => p; exact: (congr1 snd (split_join p)).
rewrite uniform_pair HistorySemantics.dependent_product_bind map_bind.
have -> : (fun h : K => fdistmap snd
    (fdistmap (fun r : M => (h, r)) (uniform R M))) = (fun _ : K => uniform R M).
  by apply/boolp.funeqP => h; rewrite fdistmap_comp /= fdistmap_id.
exact: bind_constant.
Qed.

Lemma canonical_law s :
  fdistmap (canonical s) (uniform R M) = ArithmeticPrivacy.sharing_law R n s.
Proof.
rewrite /ArithmeticPrivacy.sharing_law.
have -> : ArithmeticShares.share s = canonical s \o tail.
  by apply/boolp.funeqP => a; exact: share_as_canonical.
by rewrite -(fdistmap_comp (canonical s) tail) uniform_tail.
Qed.

(* Uniform finite functions are the explicit product of n uniform field draws. *)
Lemma mask_probability (r : M) : uniform R M r = \prod_i uniform R K (r i).
Proof.
rewrite /uniform fdist_uniformE card_ffun card_ord natrX.
under eq_bigr do rewrite fdist_uniformE.
by rewrite prodr_const card_ord exprVn.
Qed.

Theorem refresh_law (a : V) :
  fdistmap (refresh a) (uniform R M) =
    ArithmeticPrivacy.sharing_law R n (ArithmeticShares.reconstruct a).
Proof.
have -> : refresh a = canonical (ArithmeticShares.reconstruct a) \o (fun r => tail a + r).
  by apply/boolp.funeqP => r; exact: refresh_as_canonical.
by rewrite -(fdistmap_comp (canonical (ArithmeticShares.reconstruct a))
  (fun r => tail a + r)) uniform_add canonical_law.
Qed.

(* The prior may correlate context and operands arbitrarily; the new draw is explicit. *)
Theorem refresh_joint_law (C : finType) (prior : R.-fdist (C * V)) :
  (prior >>= (fun ca => (uniform R M) >>= (fun r => fdist1 (ca.1, refresh ca.2 r)))) =
  (prior >>= (fun ca => fdistmap (fun a => (ca.1, a))
    (ArithmeticPrivacy.sharing_law R n (ArithmeticShares.reconstruct ca.2)))).
Proof.
congr (fdistbind prior _); apply/boolp.funeqP => -[c a].
by rewrite -refresh_law fdistmap_comp.
Qed.

End Refresh.
End ArithmeticRefresh.

Print Assumptions ArithmeticRefresh.refresh_correct.
Print Assumptions ArithmeticRefresh.mask_probability.
Print Assumptions ArithmeticRefresh.refresh_law.
Print Assumptions ArithmeticRefresh.refresh_joint_law.
