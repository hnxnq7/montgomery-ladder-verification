From mathcomp Require Import boot order algebra reals field_tactic.
From infotheo Require Import bigop_ext fdist.
From Masking Require Import shared_ladder arithmetic_privacy noisy_leakage noisy_common_mass
  noisy_channel_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory SharedLadder NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module ArithmeticChannel.

Section Normalize.
Variable R : realType.
Variable O : finType.
Variable fallback : R.-fdist O.
Variable f : O -> R.
Hypothesis f_nonnegative : forall y, 0 <= f y.
Let mass := \sum_y f y.

Lemma entry_le_mass y : f y <= mass.
Proof.
have E : f y = \sum_(z : O | z == y) f z by rewrite big_pred1_eq.
rewrite /mass {1}E big_mkcond.
apply: ler_sum => z _. by case: ifP => // _; exact: f_nonnegative.
Qed.

Definition normalize : R.-fdist O.
Proof.
case: (boolp.pselect (mass = 0)) => E.
- exact fallback.
- apply: (@FDist.make R O [ffun y => f y / mass]).
  + move=> y; rewrite ffunE. apply: divr_ge0; first exact: f_nonnegative.
    exact: sumr_ge0.
  + under eq_bigr do rewrite ffunE.
    rewrite -big_distrl /= -/mass divff //.
    by apply/eqP.
Defined.

Lemma normalize_weight y : mass * normalize y = f y.
Proof.
rewrite /normalize; case: boolp.pselect => E.
- rewrite E mul0r. apply/eqP. rewrite eq_le f_nonnegative andTb.
  by move: (entry_le_mass y); rewrite E.
- rewrite ffunE.
  rewrite mulrC divfK //; by apply/eqP.
Qed.

End Normalize.

Section Product.
Variable R : realType.
Variables I O : finType.
Variable laws : I -> R.-fdist O.
Local Notation Output := [the finType of {ffun I -> O}].

Definition independent : R.-fdist Output.
Proof.
apply: (@FDist.make R Output [ffun out : {ffun I -> O} => \prod_i laws i (out i)]).
- move=> out; rewrite ffunE; apply: prodr_ge0 => i _; exact: FDist.ge0.
- under eq_bigr do rewrite ffunE.
  rewrite -(bigA_distr_bigA (fun i y => laws i y)) /=.
  under eq_bigr do rewrite FDist.f1.
  by rewrite big1.
Defined.

Lemma independentE out : independent out = \prod_i laws i (out i).
Proof. by rewrite /independent ffunE. Qed.
End Product.

Section ProductBind.
Variable R : realType.
Variables I A B : finType.
Variable laws : I -> R.-fdist A.
Variable channel : I -> A -> R.-fdist B.

Lemma independent_bind :
  independent (fun i => laws i >>= channel i) =
  independent laws >>= (fun a => independent (fun i => channel i (a i))).
Proof.
apply/fdist_ext => out.
rewrite independentE fdistbindE.
under eq_bigr do rewrite fdistbindE.
rewrite bigA_distr_bigA /=.
apply: eq_bigr => a _.
rewrite !independentE -big_split /=.
by apply: eq_bigr => i _.
Qed.
End ProductBind.

Section Channel.
Variable R : realType.
Variable K : finComNzRingType.
Variable O : finType.
Variable channel : K -> R.-fdist O.
Variable common : O -> R.
Hypothesis common_nonnegative : forall y, 0 <= common y.
Hypothesis common_below : forall x y, common y <= channel x y.

Definition alpha : R :=
  \sum_y common y.

Lemma alpha_nonnegative : 0 <= alpha.
Proof. exact: sumr_ge0. Qed.

Lemma alpha_at_most_one : alpha <= 1.
Proof. exact: NoisyCommonMass.common_mass_at_most_one (common_below 0). Qed.

Lemma residual_nonnegative x y : 0 <= channel x y - common y.
Proof. by rewrite subr_ge0; exact: common_below. Qed.

Lemma residual_mass x : \sum_y (channel x y - common y) = 1 - alpha.
Proof. by rewrite sumrB FDist.f1. Qed.

Definition common_law :=
  normalize (channel 0) common_nonnegative.

Definition residual_law x :=
  normalize (channel x) (residual_nonnegative x).

Lemma common_weight y : alpha * common_law y = common y.
Proof. exact: normalize_weight. Qed.

Lemma residual_weight x y : (1 - alpha) * residual_law x y = channel x y - common y.
Proof. rewrite -[1 - alpha](residual_mass x). exact: normalize_weight. Qed.

Theorem channel_decomposition x y :
  channel x y = alpha * common_law y + (1 - alpha) * residual_law x y.
Proof. by rewrite common_weight residual_weight addrC subrK. Qed.

Lemma alpha_zero_residual : alpha = 0 -> forall x, residual_law x = channel x.
Proof.
move=> E x; apply/fdist_ext => y.
have H := common_weight y. rewrite E mul0r in H.
have := residual_weight x y. by rewrite E subr0 mul1r -H subr0.
Qed.

Lemma alpha_one_common : alpha = 1 -> forall x, channel x = common_law.
Proof.
move=> E x; apply/fdist_ext => y.
by rewrite channel_decomposition E subrr mul0r mul1r addr0.
Qed.

Definition reveal_coin : R.-fdist bool.
Proof.
apply: (@FDist.make R bool [ffun b => if b then 1 - alpha else alpha]).
- case; rewrite ffunE /=; [by rewrite subr_ge0; exact: alpha_at_most_one | exact: alpha_nonnegative].
- by rewrite big_bool !ffunE /= addrC subrK.
Defined.

Lemma reveal_coinE b : reveal_coin b = if b then 1 - alpha else alpha.
Proof. by rewrite /reveal_coin ffunE. Qed.

Definition decode (v : option K) : R.-fdist O :=
  if v is Some x then residual_law x else common_law.

Lemma channel_simulation x :
  channel x = reveal_coin >>= (fun b => decode (if b then Some x else None)).
Proof.
apply/fdist_ext => y.
by rewrite fdistbindE big_bool !reveal_coinE /= /decode channel_decomposition addrC.
Qed.

Variable n : nat.
Local Notation V := [the finZmodType of {ffun 'I_n.+1 -> K}].
Local Notation View := [the finType of {ffun 'I_n.+1 -> option K}].
Local Notation Output := [the finType of {ffun 'I_n.+1 -> O}].

Lemma independent_flagsE (coin : R.-fdist bool) :
  ArithmeticPrivacy.independent_flags n coin = independent (fun _ : 'I_n.+1 => coin).
Proof.
apply/fdist_ext => flags.
have E : ArithmeticPrivacy.row_flags (\row_i flags i) = flags.
  by apply/ffunP => i; rewrite /ArithmeticPrivacy.row_flags ffunE mxE.
rewrite /ArithmeticPrivacy.independent_flags fdistmapE -{1}E
  (big_pred1_inj (@ArithmeticPrivacy.row_flags_injective n)) fdist_rVE independentE.
by apply: eq_bigr => i _; rewrite mxE.
Qed.

Definition vector_channel (a : V) : R.-fdist Output :=
  independent (fun i => channel (a i)).

Definition decode_view (v : View) : R.-fdist Output :=
  independent (fun i => decode (v i)).

Theorem fixed_shares_simulation (a : V) :
  vector_channel a = ArithmeticPrivacy.independent_flags n reveal_coin >>=
    (fun flags => decode_view (ArithmeticPrivacy.probe flags a)).
Proof.
rewrite independent_flagsE /vector_channel /decode_view.
have E : (fun i => channel (a i)) =
    (fun i => reveal_coin >>= (fun b => decode (if b then Some (a i) else None))).
  apply/boolp.funeqP => i. exact: channel_simulation.
rewrite E independent_bind.
congr (fdistbind _ _). apply/boolp.funeqP => flags.
congr (independent _). apply/boolp.funeqP => i.
by rewrite /ArithmeticPrivacy.probe ffunE.
Qed.

(* Channels are independent conditional on the sharing, not independent of their inputs. *)
Definition actual_law (s : K) : R.-fdist Output :=
  ArithmeticPrivacy.sharing_law R n s >>= vector_channel.

Theorem actual_channel_simulation s :
  actual_law s = ArithmeticPrivacy.probe_law
    (ArithmeticPrivacy.independent_flags n reveal_coin) s >>= decode_view.
Proof.
rewrite /actual_law /ArithmeticPrivacy.probe_law fdistbindA.
have E : vector_channel = (fun a : V => ArithmeticPrivacy.independent_flags n reveal_coin >>=
    (fun flags => decode_view (ArithmeticPrivacy.probe flags a))).
  apply/boolp.funeqP => a. exact: fixed_shares_simulation.
rewrite E NoisyChannelBridge.bind_swap.
congr (fdistbind _ _). apply/boolp.funeqP => flags.
by rewrite /fdistmap fdistbindA; congr (fdistbind _ _); apply/boolp.funeqP => a;
  rewrite fdist1bind.
Qed.

Theorem vector_TV_bound s t :
  TV (actual_law s) (actual_law t) <= (1 - alpha)^+n.+1.
Proof.
rewrite !actual_channel_simulation.
have H := ArithmeticPrivacy.simulated_channel_bound reveal_coin decode_view s t.
by rewrite reveal_coinE in H.
Qed.

Corollary aggregate_TV_bound (B : finType) (aggregate : Output -> B) s t :
  TV (fdistmap aggregate (actual_law s)) (fdistmap aggregate (actual_law t)) <=
    (1 - alpha)^+n.+1.
Proof.
apply: le_trans (channel_TV_contraction (actual_law s) (actual_law t)
  (fun out => fdist1 (aggregate out))) _.
exact: vector_TV_bound.
Qed.

End Channel.

End ArithmeticChannel.

Print Assumptions ArithmeticChannel.channel_decomposition.
Print Assumptions ArithmeticChannel.actual_channel_simulation.
Print Assumptions ArithmeticChannel.vector_TV_bound.
Print Assumptions ArithmeticChannel.aggregate_TV_bound.
