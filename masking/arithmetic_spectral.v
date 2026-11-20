From mathcomp Require Import boot order algebra reals field_tactic sesquilinear spectral.
From infotheo Require Import fdist variation_dist.
From Masking Require Import noisy_leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module ArithmeticSpectral.

Section Coefficients.
Variable C : numClosedFieldType.
Variable I : finType.
Variable trivial : I.
Variables coefficient left right : I -> C.
Variable rho : C.
Hypothesis rho_nonnegative : 0 <= rho.
Hypothesis trivial_agrees : left trivial = right trivial.
Hypothesis left_unit : forall i, `|left i| <= 1.
Hypothesis right_unit : forall i, `|right i| <= 1.
Hypothesis coefficient_bound : forall i, i != trivial -> `|coefficient i| <= rho.
Hypothesis coefficient_energy : \sum_i `|coefficient i| ^+ 2 <= 1.

Lemma nontrivial_energy : \sum_(i | i != trivial) `|coefficient i| ^+ 2 <= 1.
Proof.
apply: le_trans _ coefficient_energy.
rewrite [X in X <= _]big_mkcond.
apply: ler_sum => i _. case: ifP => // _.
exact: exprn_ge0 (normr_ge0 _).
Qed.

Lemma phase_difference_bound i : `|left i - right i| <= 2.
Proof.
apply: le_trans (ler_normB _ _) _.
exact: lerD (left_unit i) (right_unit i).
Qed.

Lemma coefficient_power_bound k i : i != trivial ->
  `|(left i - right i) * coefficient i ^+ (k + 2)| <=
    (2 * rho ^+ k) * `|coefficient i| ^+ 2.
Proof.
move=> Hi. rewrite normrM normrX exprD.
have Hk : `|coefficient i| ^+ k <= rho ^+ k.
  apply: lerXn2r; rewrite ?nnegrE //.
  exact: coefficient_bound Hi.
have Hphase := phase_difference_bound i.
have H : `|left i - right i| * `|coefficient i| ^+ k <= 2 * rho ^+ k.
  apply: ler_pM => //; exact: exprn_ge0 (normr_ge0 _).
rewrite mulrA.
apply: ler_wpM2r H.
exact: exprn_ge0 (normr_ge0 _).
Qed.

(* The coefficient and energy premises still need a concrete Fourier instantiation. *)
Theorem coefficient_gap k :
  `|(\sum_i left i * coefficient i ^+ (k + 2)) -
    (\sum_i right i * coefficient i ^+ (k + 2))| <= 2 * rho ^+ k.
Proof.
rewrite -sumrB.
under eq_bigr do rewrite -mulrBl.
rewrite (bigD1 trivial) //= trivial_agrees subrr mul0r add0r.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_(i | i != trivial)
    `|(left i - right i) * coefficient i ^+ (k + 2)| <=
    \sum_(i | i != trivial) (2 * rho ^+ k) * `|coefficient i| ^+ 2) _.
  by apply: ler_sum => i Hi; exact: coefficient_power_bound.
rewrite -big_distrr /=.
have H0 : 0 <= 2 * rho ^+ k by apply: mulr_ge0; [exact: ler0n | exact: exprn_ge0].
by move: (ler_wpM2l H0 nontrivial_energy); rewrite mulr1.
Qed.

Corollary coefficient_gap_n n : (2 <= n)%N ->
  `|(\sum_i left i * coefficient i ^+ n) - (\sum_i right i * coefficient i ^+ n)| <=
    2 * rho ^+ (n - 2).
Proof. move=> Hn. by move: (coefficient_gap (n - 2)%N); rewrite subnK. Qed.

End Coefficients.

Section FiniteParseval.
Variable C : numClosedFieldType.
Variables I J : finType.
Variable kernel : J -> I -> C.
Variable scale : C.
Hypothesis orthogonal : forall i j,
  \sum_k kernel k i * (kernel k j)^* = if i == j then scale else 0.
Variable f : I -> C.

Definition transform (k : J) : C :=
  \sum_i f i * kernel k i.

Lemma transform_square k :
  `|transform k| ^+ 2 =
  \sum_i \sum_j (f i * (f j)^*) * (kernel k i * (kernel k j)^*).
Proof.
rewrite normCK /transform rmorph_sum big_distrl /=.
apply: eq_bigr => i _. rewrite big_distrr /=.
apply: eq_bigr => j _. rewrite rmorphM /=. ring.
Qed.

Lemma pair_sum i j :
  \sum_k (f i * (f j)^*) * (kernel k i * (kernel k j)^*) =
    if i == j then scale * `|f i| ^+ 2 else 0.
Proof.
rewrite -big_distrr /= orthogonal.
case: ifP => [/eqP ->|_]; last by rewrite mulr0.
by rewrite normCK mulrC.
Qed.

Theorem finite_parseval :
  \sum_k `|transform k| ^+ 2 = scale * \sum_i `|f i| ^+ 2.
Proof.
under eq_bigr do rewrite transform_square.
rewrite exchange_big.
under eq_bigr do rewrite exchange_big.
under eq_bigr do under eq_bigr do rewrite pair_sum.
have diagonal i : (\sum_j if i == j then scale * `|f i| ^+ 2 else 0) = scale * `|f i| ^+ 2.
  under eq_bigr do rewrite eq_sym.
  by rewrite -big_mkcond big_pred1_eq.
under eq_bigr do rewrite diagonal.
by rewrite -big_distrr.
Qed.

End FiniteParseval.

Section FiniteCauchy.
Variable C : numClosedFieldType.

Lemma dot_Cauchy n (u v : 'rV[C]_n) :
  `|dotmx u v| ^+ 2 <= dotmx u u * dotmx v v.
Proof.
have [H _] : `|dotmx u v| ^+ 2 <= dotmx u u * dotmx v v ?= iff ~~ free [:: u; v].
  exact: CauchySchwarz.
exact: H.
Qed.

Lemma ordinal_l1_l2 n (f : 'I_n -> C) :
  (\sum_i `|f i|) ^+ 2 <= n%:R * \sum_i `|f i| ^+ 2.
Proof.
pose u : 'rV[C]_n := \row_i `|f i|.
pose v : 'rV[C]_n := \row_i 1.
have Euv : dotmx u v = \sum_i `|f i|.
  rewrite dotmxE mxE. by apply: eq_bigr => i _; rewrite /u /v !mxE conjC1 mulr1.
have Euu : dotmx u u = \sum_i `|f i| ^+ 2.
  rewrite dotmxE mxE. apply: eq_bigr => i _.
  by rewrite /u !mxE conj_Creal ?normr_real // -expr2.
have Evv : dotmx v v = n%:R.
  rewrite dotmxE mxE.
  under eq_bigr do rewrite /v !mxE conjC1 mulr1.
  by rewrite sumr_const card_ord.
have H := dot_Cauchy u v.
have H0 : 0 <= \sum_i `|f i| by apply: sumr_ge0 => i _; exact: normr_ge0.
by rewrite Euv Euu Evv (ger0_norm H0) mulrC in H.
Qed.

Lemma finite_l1_l2 (I : finType) (f : I -> C) :
  (\sum_i `|f i|) ^+ 2 <= #|I|%:R * \sum_i `|f i| ^+ 2.
Proof.
have H := ordinal_l1_l2 (fun i : 'I_#|I| => f (enum_val i)).
rewrite -(big_enum_val (A := predT) (fun i => `|f i|)) in H.
by rewrite -(big_enum_val (A := predT) (fun i => `|f i| ^+ 2)) in H.
Qed.

End FiniteCauchy.

Section SpectralL1.
Variable C : numClosedFieldType.
Variables I J : finType.
Variable kernel : J -> I -> C.
Hypothesis grid_nonempty : (0 < #|J|)%N.
Hypothesis grid_orthogonal : forall i j,
  \sum_k kernel k i * (kernel k j)^* = if i == j then #|J|%:R else 0.
Variable f : I -> C.
Variable bound : C.
Hypothesis bound_nonnegative : 0 <= bound.
Hypothesis transform_bound : forall k, `|transform kernel f k| <= bound.

Lemma transform_energy_bound : \sum_i `|f i| ^+ 2 <= bound ^+ 2.
Proof.
have H : \sum_k `|transform kernel f k| ^+ 2 <= #|J|%:R * bound ^+ 2.
  rewrite mulr_natl -sumr_const.
  apply: ler_sum => k _.
  apply: lerXn2r; rewrite ?nnegrE //; exact: transform_bound.
rewrite (finite_parseval grid_orthogonal) in H.
have HJ : (0 : C) < #|J|%:R by rewrite ltr0n.
by move: H; rewrite (ler_pM2l HJ).
Qed.

Theorem spectral_l1_squared :
  (\sum_i `|f i|) ^+ 2 <= #|I|%:R * bound ^+ 2.
Proof.
apply: le_trans (finite_l1_l2 f) _.
apply: ler_wpM2l transform_energy_bound.
exact: ler0n.
Qed.

End SpectralL1.

Section RationalAdapter.
Variable I : finType.
Variables p q : I -> rat.

Definition rational_TV : rat :=
  (\sum_i `|p i - q i|) / 2.

Lemma rational_TV_embedding (F : numFieldType) :
  @ratr F rational_TV = (\sum_i `|@ratr F (p i) - @ratr F (q i)|) / 2.
Proof.
rewrite /rational_TV fmorph_div rmorph_nat rmorph_sum.
congr (_ / _). apply: eq_bigr => i _.
by rewrite /= ratr_norm rmorphB.
Qed.

Lemma rational_square_transfer (C R : numFieldType) (bound : rat) :
  (@ratr C rational_TV) ^+ 2 <= @ratr C bound ->
  (@ratr R rational_TV) ^+ 2 <= @ratr R bound.
Proof. by rewrite -!rmorphXn /= !ler_rat. Qed.

Variable R : realType.
Variables d e : R.-fdist I.
Hypothesis d_rational : forall i, d i = @ratr R (p i).
Hypothesis e_rational : forall i, e i = @ratr R (q i).

Lemma actual_TV_rational : NoisyLeakage.TV d e = @ratr R rational_TV.
Proof.
rewrite rational_TV_embedding /NoisyLeakage.TV /var_dist.
congr (_ / _). by apply: eq_bigr => i _; rewrite d_rational e_rational.
Qed.

(* Fourier estimates over algebraic complex numbers transfer only after matching the actual masses. *)
Theorem actual_TV_square_transfer (C : numFieldType) (bound : rat) :
  (@ratr C rational_TV) ^+ 2 <= @ratr C bound -> NoisyLeakage.TV d e ^+ 2 <= @ratr R bound.
Proof. rewrite actual_TV_rational. exact: rational_square_transfer. Qed.

Theorem actual_TV_from_spectral (C : numClosedFieldType) (J : finType)
    (kernel : J -> I -> C) (bound : rat) :
  (0 < #|J|)%N ->
  (forall i j, \sum_k kernel k i * (kernel k j)^* = if i == j then #|J|%:R else 0) ->
  0 <= bound ->
  (forall k, `|transform kernel (fun i => @ratr C (p i) - @ratr C (q i)) k| <= @ratr C bound) ->
  NoisyLeakage.TV d e ^+ 2 <= @ratr R (#|I|%:R * bound ^+ 2 / 4).
Proof.
move=> HJ Horth Hb Htransform.
apply: (actual_TV_square_transfer (C := C)).
rewrite rational_TV_embedding fmorph_div rmorphM rmorphXn !rmorph_nat /=.
have E (x : C) : (x / 2) ^+ 2 = x ^+ 2 / 4 by field.
rewrite E.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
have HbC : 0 <= @ratr C bound by rewrite ler0q.
exact: (@spectral_l1_squared C I J kernel HJ Horth
  (fun i => @ratr C (p i) - @ratr C (q i)) (@ratr C bound) HbC Htransform).
Qed.

End RationalAdapter.
End ArithmeticSpectral.

Print Assumptions ArithmeticSpectral.coefficient_gap_n.
Print Assumptions ArithmeticSpectral.finite_parseval.
Print Assumptions ArithmeticSpectral.spectral_l1_squared.
Print Assumptions ArithmeticSpectral.actual_TV_square_transfer.
Print Assumptions ArithmeticSpectral.actual_TV_from_spectral.
