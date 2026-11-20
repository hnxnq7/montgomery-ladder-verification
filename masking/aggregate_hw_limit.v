From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking.
Local Open Scope ring_scope.

Module AggregateHWLimit.
Section Limit.
Variable R : realType.
Variable K : finZmodType.
Variable hw : K -> nat.
Hypothesis hw_zero : forall x, (hw x == 0%N) = (x == 0).

Definition pair_HW (a : shares K) : nat :=
  (hw a.1 + hw a.2)%N.
Definition zero_event (a : shares K) : bool :=
  pair_HW a == 0%N.
Definition event_law (s : K) :=
  fdistmap zero_event (share_distribution R s).

Lemma split_zero_event s r :
  zero_event (split s r) = ((r == 0) && (s == 0)).
Proof.
rewrite /zero_event /pair_HW /split /= addn_eq0 !hw_zero.
case Hr: (r == 0); last by [].
move/eqP: Hr => ->. by rewrite subr0.
Qed.

Lemma zero_secret_probability : event_law 0 true = (#|K|%:R)^-1.
Proof.
rewrite /event_law /share_distribution fdistmap_comp fdistmapE /=.
under eq_bigl do rewrite !inE /comp split_zero_event eqxx andbT eqb_id.
rewrite big_pred1_eq /uniform fdist_uniformE. reflexivity.
Qed.

Lemma nonzero_secret_law s : s != 0 -> event_law s = fdist1 false.
Proof.
move=> Hs. rewrite /event_law /share_distribution fdistmap_comp.
have -> : zero_event \o split s = (fun _ : K => false).
  apply/boolp.funeqP => r. by rewrite /= split_zero_event (negbTE Hs) andbF.
exact: map_constant.
Qed.

Lemma nonzero_secret_probability s : s != 0 -> event_law s true = 0.
Proof. by move=> Hs; rewrite (nonzero_secret_law Hs) fdist1E. Qed.

Lemma zero_secret_positive : 0 < event_law 0 true.
Proof.
rewrite zero_secret_probability invr_gt0 ltr0n.
exact: cardinal_positive.
Qed.

Theorem zero_vs_nonzero s : s != 0 -> event_law 0 <> event_law s.
Proof.
move=> Hs Heq.
have Hpos := zero_secret_positive.
by rewrite Heq (nonzero_secret_probability Hs) ltxx in Hpos.
Qed.

Theorem equal_event_laws_zero_status s t :
  event_law s = event_law t -> (s == 0) = (t == 0).
Proof.
move=> Heq. case Hs: (s == 0); case Ht: (t == 0) => //.
- move/eqP: Hs => Hs. subst s.
  exfalso. exact: (zero_vs_nonzero (negbT Ht) Heq).
- move/eqP: Ht => Ht. subst t.
  exfalso. apply: (zero_vs_nonzero (negbT Hs)). exact: esym Heq.
Qed.

(* Any finite observation exposing the zero-HW event inherits the distinction. *)
Theorem finite_observation_distinguishes (B : finType) (observe : shares K -> B)
    (is_zero : B -> bool) s :
  (forall a, is_zero (observe a) = zero_event a) -> s != 0 ->
  fdistmap observe (share_distribution R 0) <>
    fdistmap observe (share_distribution R s).
Proof.
move=> Hfactor Hs Heq. apply: (zero_vs_nonzero Hs).
have Hmap := congr1 (fun d => fdistmap is_zero d) Heq.
rewrite !fdistmap_comp in Hmap.
have Hfun : is_zero \o observe = zero_event.
  by apply/boolp.funeqP => a; exact: Hfactor.
rewrite Hfun in Hmap.
rewrite /event_law /share_distribution !fdistmap_comp. exact: Hmap.
Qed.

End Limit.
End AggregateHWLimit.

Print Assumptions AggregateHWLimit.zero_vs_nonzero.
Print Assumptions AggregateHWLimit.equal_event_laws_zero_status.
Print Assumptions AggregateHWLimit.finite_observation_distinguishes.
