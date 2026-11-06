From mathcomp Require Import boot order algebra reals.
From infotheo Require Import bigop_ext fdist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module FiniteMasking.

Section Distributions.
Variable R : realType.

Lemma bind_constant (A B : finType) (d : R.-fdist A) (e : R.-fdist B) :
  d >>= (fun _ => e) = e.
Proof.
apply/fdist_ext => y.
by rewrite fdistbindE -big_distrl /= FDist.f1 mul1r.
Qed.

Lemma map_constant (A B : finType) (d : R.-fdist A) (b : B) :
  fdistmap (fun _ => b) d = fdist1 b.
Proof. exact: bind_constant. Qed.

Lemma map_bind (A B C : finType) (d : R.-fdist A)
    (f : A -> R.-fdist B) (g : B -> C) :
  fdistmap g (d >>= f) = d >>= (fun a => fdistmap g (f a)).
Proof. exact: fdistbindA. Qed.

Lemma bind_map (A B C : finType) (d : R.-fdist A) (f : A -> B) (g : B -> R.-fdist C) :
  fdistmap f d >>= g = d >>= (fun a => g (f a)).
Proof.
rewrite /fdistmap fdistbindA; congr (fdistbind d _).
by apply/boolp.funeqP => a; rewrite fdist1bind.
Qed.

Lemma map_bind_pure (A B C : finType) (d : R.-fdist A) (f : A -> R.-fdist B)
    (observe : B -> C) (next : A -> C) :
  (forall a, fdistmap observe (f a) = fdist1 (next a)) ->
  fdistmap observe (d >>= f) = fdistmap next d.
Proof.
move=> H; rewrite map_bind /fdistmap; congr (fdistbind d _).
by apply/boolp.funeqP => a; exact: H.
Qed.

Section AdditiveShares.
Variable K : finZmodType.

Lemma cardinal_positive : (0 < #|K|)%N.
Proof. by rewrite (cardD1 (0 : K)) inE. Qed.

Definition uniform : R.-fdist K :=
  fdist_uniform (esym (prednK cardinal_positive)).

Lemma uniform_bijection (f g : K -> K) :
  cancel f g -> cancel g f -> fdistmap f uniform = uniform.
Proof.
move=> fg gf; apply/fdist_ext => y.
rewrite fdistmapE /= -[y](gf y) (big_pred1_inj (can_inj fg)).
by rewrite /uniform !fdist_uniformE.
Qed.

Lemma uniform_add (s : K) : fdistmap (fun r => s + r) uniform = uniform.
Proof.
apply: (@uniform_bijection _ (fun y => y - s)).
- by move=> r; rewrite (addrC s r) addrK.
- exact: subrKC.
Qed.

Lemma observed_mask_independent (B : finType) (observe : K -> B) (s t : K) :
  fdistmap observe (fdistmap (fun r => s + r) uniform) =
  fdistmap observe (fdistmap (fun r => t + r) uniform).
Proof. by rewrite !uniform_add. Qed.

(* Enumerating masks is the finite, equally weighted version of sampling them. *)
Definition copies (s : K) :=
  map (fun r => s + r) (enum K).

Lemma copies_permutation s : perm_eq (copies s) (enum K).
Proof.
apply: uniq_perm; first by rewrite /copies map_inj_uniq ?enum_uniq //; exact: addrI.
- exact: enum_uniq.
- move=> y; rewrite mem_enum /copies.
  apply/mapP; exists (y - s); first by rewrite mem_enum.
  by rewrite addrC subrK.
Qed.

Lemma copies_observations (B : eqType) (observe : K -> B) s t :
  perm_eq (map observe (copies s)) (map observe (copies t)).
Proof.
apply: perm_map.
apply: perm_trans (copies_permutation s) _.
by rewrite perm_sym copies_permutation.
Qed.

Lemma uniform_sub (s : K) : fdistmap (fun r => s - r) uniform = uniform.
Proof.
apply: (@uniform_bijection _ (fun y => s - y));
  exact: subKr.
Qed.

Definition shares := (K * K)%type.
Definition reconstruct (a : shares) :=
  a.1 + a.2.
Definition split (s r : K) : shares :=
  (r, s - r).
Definition share_distribution (s : K) :=
  fdistmap (split s) uniform.

Lemma split_correct s r : reconstruct (split s r) = s.
Proof. by rewrite /reconstruct /split /= addrC subrK. Qed.

Lemma first_share_uniform s :
  fdistmap fst (share_distribution s) = uniform.
Proof. by rewrite /share_distribution fdistmap_comp /= fdistmap_id. Qed.

Lemma second_share_uniform s :
  fdistmap snd (share_distribution s) = uniform.
Proof. by rewrite /share_distribution fdistmap_comp /= uniform_sub. Qed.

Lemma reconstruction_distribution s :
  fdistmap reconstruct (share_distribution s) = fdist1 s.
Proof.
rewrite /share_distribution fdistmap_comp.
have -> : reconstruct \o split s = (fun _ => s).
  by apply/boolp.funeqP => r; exact: split_correct.
exact: map_constant.
Qed.

Lemma both_shares_reveal s t : share_distribution s = share_distribution t -> s = t.
Proof.
move=> eqst; apply: (@fdist1_inj R K).
by rewrite -!reconstruction_distribution eqst.
Qed.

Definition refresh (a : shares) (r : K) : shares :=
  (a.1 + r, a.2 - r).

Lemma refresh_correct a r : reconstruct (refresh a r) = reconstruct a.
Proof. by rewrite /reconstruct /refresh /= addrACA subrr addr0. Qed.

Lemma refresh_distribution_correct a :
  fdistmap reconstruct (fdistmap (refresh a) uniform) = fdist1 (reconstruct a).
Proof.
rewrite fdistmap_comp.
have -> : reconstruct \o refresh a = (fun _ => reconstruct a).
  by apply/boolp.funeqP => r; exact: refresh_correct.
exact: map_constant.
Qed.

Lemma refreshed_output_uniform a :
  fdistmap (fun r => (refresh a r).2) uniform = uniform.
Proof. exact: uniform_sub. Qed.

(* Only the second share is observed; the mask and the first share stay hidden. *)
Lemma output_distribution_independent (A : finType) (d : R.-fdist A) (f : A -> shares) :
  d >>= (fun a => fdistmap (fun r => (refresh (f a) r).2) uniform) = uniform.
Proof.
have -> : (fun a => fdistmap (fun r => (refresh (f a) r).2) uniform) = (fun _ => uniform).
  by apply/boolp.funeqP => a; exact: refreshed_output_uniform.
exact: bind_constant.
Qed.

End AdditiveShares.
End Distributions.
End FiniteMasking.
