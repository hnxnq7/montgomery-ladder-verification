From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import ssr_ext bigop_ext fdist.
From Masking Require Import finite_masking shared_ladder arithmetic_shares arithmetic_privacy
  arithmetic_refresh arithmetic_channel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module ArithmeticBankRefresh.

Section ProductMap.
Variable R : realType.
Variables I A B : finType.

Lemma independent_point (f : I -> B) :
  ArithmeticChannel.independent (fun i => @fdist1 R B (f i)) = fdist1 [ffun i => f i].
Proof.
apply/eqP; rewrite -fdist1E1 ArithmeticChannel.independentE; apply/eqP.
by rewrite big1 // => i _; rewrite ffunE fdist1xx.
Qed.

(* This is a joint pushforward of a product law, not a collection of marginal equalities. *)
Lemma independent_map (laws : I -> R.-fdist A) (f : I -> A -> B) :
  fdistmap (fun a : {ffun I -> A} => [ffun i => f i (a i)])
    (ArithmeticChannel.independent laws) =
  ArithmeticChannel.independent (fun i => fdistmap (f i) (laws i)).
Proof.
rewrite /fdistmap ArithmeticChannel.independent_bind.
congr (fdistbind (ArithmeticChannel.independent laws) _).
by apply/boolp.funeqP => a; rewrite independent_point.
Qed.
End ProductMap.

Section Bank.
Variable R : realType.
Variable K : finComNzRingType.
Variable I : finType.
Variable n : nat.
Local Notation V := [the finZmodType of {ffun 'I_n.+1 -> K}].
Local Notation M := [the finZmodType of {ffun 'I_n -> K}].
Local Notation Bank := [the finZmodType of {ffun I -> V}].
Local Notation Coins := [the finZmodType of {ffun I -> M}].
Local Notation Values := [the finZmodType of {ffun I -> K}].

Definition values (a : Bank) : Values :=
  [ffun i => ArithmeticShares.reconstruct (a i)].

(* Each indexed group uses its own mask vector in a single simultaneous refresh. *)
Definition refresh (a : Bank) (r : Coins) : Bank :=
  [ffun i => ArithmeticRefresh.refresh (a i) (r i)].

Lemma refresh_group a r i : refresh a r i = ArithmeticRefresh.refresh (a i) (r i).
Proof. by rewrite /refresh ffunE. Qed.

Theorem refresh_correct a r : values (refresh a r) = values a.
Proof.
by apply/ffunP => i; rewrite /values !ffunE ArithmeticRefresh.refresh_correct.
Qed.

Definition canonical_bank_law (s : Values) : R.-fdist Bank :=
  ArithmeticChannel.independent (fun i => ArithmeticPrivacy.sharing_law R n (s i)).

Definition canonical_bank (s : Values) (r : Coins) : Bank :=
  [ffun i => ArithmeticRefresh.canonical (s i) (r i)].

Lemma uniform_masks : uniform R Coins = ArithmeticChannel.independent (fun _ : I => uniform R M).
Proof.
apply/fdist_ext => r.
rewrite ArithmeticChannel.independentE /uniform fdist_uniformE card_ffun natrX.
under eq_bigr do rewrite fdist_uniformE.
by rewrite prodr_const exprVn.
Qed.

(* One draw supplies independent masks for every pair (group, non-anchor share). *)
Theorem mask_probability (r : Coins) :
  uniform R Coins r = \prod_i \prod_j uniform R K (r i j).
Proof.
rewrite uniform_masks ArithmeticChannel.independentE.
by apply: eq_bigr => i _; exact: ArithmeticRefresh.mask_probability.
Qed.

Lemma canonical_bank_lawE s :
  fdistmap (canonical_bank s) (uniform R Coins) = canonical_bank_law s.
Proof.
rewrite /canonical_bank uniform_masks.
rewrite (independent_map (fun _ : I => uniform R M) (fun i => ArithmeticRefresh.canonical (s i))).
rewrite /canonical_bank_law.
congr (ArithmeticChannel.independent _); apply/boolp.funeqP => i.
exact: ArithmeticRefresh.canonical_law.
Qed.

Theorem refresh_law (a : Bank) :
  fdistmap (refresh a) (uniform R Coins) = canonical_bank_law (values a).
Proof.
rewrite /refresh uniform_masks.
rewrite (independent_map (fun _ : I => uniform R M) (fun i => ArithmeticRefresh.refresh (a i))).
rewrite /canonical_bank_law.
congr (ArithmeticChannel.independent _); apply/boolp.funeqP => i.
by rewrite ArithmeticRefresh.refresh_law /values ffunE.
Qed.

Corollary refresh_probability (a out : Bank) :
  fdistmap (refresh a) (uniform R Coins) out =
  \prod_i ArithmeticPrivacy.sharing_law R n (ArithmeticShares.reconstruct (a i)) (out i).
Proof.
rewrite refresh_law /canonical_bank_law ArithmeticChannel.independentE.
by apply: eq_bigr => i _; rewrite /values ffunE.
Qed.

Section Context.
Variable C : finType.

(* Context, values, and groups in the prior can all be correlated. *)
Definition refresh_prior (prior : R.-fdist (C * Bank)) : R.-fdist (C * Bank) :=
  prior >>= (fun ca => fdistmap (fun r => (ca.1, refresh ca.2 r)) (uniform R Coins)).

Theorem refresh_joint_law (prior : R.-fdist (C * Bank)) :
  refresh_prior prior = prior >>= (fun ca =>
    fdistmap (fun out => (ca.1, out)) (canonical_bank_law (values ca.2))).
Proof.
rewrite /refresh_prior; congr (fdistbind prior _); apply/boolp.funeqP => -[c a].
by rewrite -refresh_law fdistmap_comp.
Qed.

(* The complete value vector keeps its prior joint law, not just its individual marginals. *)
Theorem refresh_values_joint_law (prior : R.-fdist (C * Bank)) :
  fdistmap (fun ca => (ca.1, values ca.2)) (refresh_prior prior) =
  fdistmap (fun ca => (ca.1, values ca.2)) prior.
Proof.
rewrite /refresh_prior; apply: map_bind_pure => -[c a].
rewrite fdistmap_comp.
have -> : (fun ca : C * Bank => (ca.1, values ca.2)) \o
    (fun r : Coins => (c, refresh a r)) = (fun _ : Coins => (c, values a)).
  by apply/boolp.funeqP => r; rewrite /= refresh_correct.
exact: map_constant.
Qed.

Corollary refresh_observation_law (O : finType) (observe : C * Bank -> O)
    (prior : R.-fdist (C * Bank)) :
  fdistmap observe (refresh_prior prior) = prior >>= (fun ca =>
    fdistmap (fun out => observe (ca.1, out)) (canonical_bank_law (values ca.2))).
Proof.
rewrite refresh_joint_law map_bind.
by congr (fdistbind prior _); apply/boolp.funeqP => ca; rewrite fdistmap_comp.
Qed.

End Context.
End Bank.
End ArithmeticBankRefresh.

Print Assumptions ArithmeticBankRefresh.independent_map.
Print Assumptions ArithmeticBankRefresh.refresh_correct.
Print Assumptions ArithmeticBankRefresh.mask_probability.
Print Assumptions ArithmeticBankRefresh.refresh_law.
Print Assumptions ArithmeticBankRefresh.refresh_joint_law.
Print Assumptions ArithmeticBankRefresh.refresh_values_joint_law.
Print Assumptions ArithmeticBankRefresh.refresh_observation_law.
