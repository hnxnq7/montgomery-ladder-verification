From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import bigop_ext fdist.
From Masking Require Import finite_masking shared_ladder arithmetic_shares noisy_leakage noisy_trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking SharedLadder.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module ArithmeticPrivacy.
Section Sharing.
Variable R : realType.
Variable K : finComNzRingType.
Variable n : nat.
Local Notation V := [the finZmodType of {ffun 'I_n.+1 -> K}].

Definition single (i : 'I_n.+1) (x : K) : V :=
  [ffun j => if j == i then x else 0].

Lemma reconstruct_single i x : ArithmeticShares.reconstruct (single i x) = x.
Proof.
rewrite /ArithmeticShares.reconstruct /single.
under eq_bigr do rewrite ffunE.
by rewrite -big_mkcond big_pred1_eq.
Qed.

Lemma reconstruct_add (a b : V) :
  ArithmeticShares.reconstruct (a + b) =
  ArithmeticShares.reconstruct a + ArithmeticShares.reconstruct b.
Proof. exact: ArithmeticShares.add_correct. Qed.

Lemma share_shift i s t (r : V) :
  ArithmeticShares.share t (r + single i (t - s)) =
  ArithmeticShares.share s r + single i (t - s).
Proof.
have H (u : K) : t - (u + (t - s)) = s - u.
  by rewrite [u + _]addrC opprD addrA subKr.
apply/ffunP => j.
rewrite /ArithmeticShares.share !ffunE reconstruct_add reconstruct_single H.
exact: addrAC.
Qed.

Definition sharing_law (s : K) :=
  fdistmap (ArithmeticShares.share s) (uniform R V).

Variable O : finType.
Variable observe : V -> O.

Definition ignores (i : 'I_n.+1) :=
  forall a b : V, (forall j, j != i -> a j = b j) -> observe a = observe b.

Lemma observe_shift i : ignores i -> forall (a : V) x, observe (a + single i x) = observe a.
Proof.
move=> H a x. apply: H => j Hj.
by rewrite !ffunE (negbTE Hj) addr0.
Qed.

(* Any observation omitting one entire share has a secret-independent joint law. *)
Theorem missing_share_independent i : ignores i -> forall s t,
  fdistmap observe (sharing_law s) = fdistmap observe (sharing_law t).
Proof.
move=> H s t.
rewrite /sharing_law !fdistmap_comp -{2}(uniform_add R (single i (t - s))) fdistmap_comp.
congr (fdistmap _ _). apply/boolp.funeqP => r.
rewrite /= addrC share_shift.
symmetry.
exact: (@observe_shift i H (ArithmeticShares.share s r) (t - s)).
Qed.

End Sharing.

Section Probes.
Variable R : realType.
Variable K : finComNzRingType.
Variable n : nat.
Local Notation V := [the finZmodType of {ffun 'I_n.+1 -> K}].
Local Notation Flags := [the finType of {ffun 'I_n.+1 -> bool}].
Local Notation View := [the finType of {ffun 'I_n.+1 -> option K}].

Definition probe (flags : Flags) (a : V) : View :=
  [ffun i => if flags i then Some (a i) else None].

Definition all_flags : Flags :=
  [ffun _ => true].

Lemma all_flagsE (flags : Flags) : [forall i, flags i] = (flags == all_flags).
Proof.
apply/forallP/eqP => H.
- apply/ffunP => i. by rewrite ffunE H.
- move=> i. by rewrite H ffunE.
Qed.

Lemma incomplete_probe_independent (flags : Flags) :
  ~~ [forall i, flags i] -> forall s t,
  fdistmap (probe flags) (sharing_law R n s) = fdistmap (probe flags) (sharing_law R n t).
Proof.
rewrite negb_forall => /existsP [i Hi] s t.
apply: (@missing_share_independent R K n View (probe flags) i) => a b Hab.
apply/ffunP => j; rewrite /probe !ffunE.
case E: (j == i).
- move/eqP: E => ->. by rewrite (negbTE Hi).
- by rewrite (Hab j (negbT E)).
Qed.

Definition probe_law (flags : R.-fdist Flags) s :=
  flags >>= (fun f => fdistmap (probe f) (sharing_law R n s)).

(* A snapshot bound; a noisy execution still needs a justified reduction to these probes. *)
Theorem random_probe_bound (flags : R.-fdist Flags) s t :
  NoisyLeakage.TV (probe_law flags s) (probe_law flags t) <= flags all_flags.
Proof.
rewrite /probe_law.
apply: Order.POrderTheory.le_trans (NoisyTrace.bind_TV_kernel _ _ _) _.
have E f : flags f * (if [forall i, f i] then 1 else 0) =
    if f == all_flags then flags f else 0.
  rewrite all_flagsE; case: (f == all_flags); by rewrite ?mulr1 ?mulr0.
have H : \sum_f flags f * (if [forall i, f i] then 1 else 0) = flags all_flags.
  under eq_bigr do rewrite E.
  by rewrite -big_mkcond big_pred1_eq.
rewrite -H. apply: Num.Theory.ler_sum => f _.
apply: Num.Theory.ler_wpM2l; first exact: FDist.ge0.
case Ef: [forall i, f i]; first exact: NoisyLeakage.TV_at_most_one.
by rewrite (incomplete_probe_independent (negbT Ef) s t) NoisyLeakage.TV_self.
Qed.

Definition row_flags (row : 'rV[bool]_n.+1) : Flags :=
  [ffun i => row ord0 i].

Lemma row_flags_injective : injective row_flags.
Proof.
move=> x y H; apply/rowP => i.
have := congr1 (fun f : Flags => f i) H.
by rewrite /row_flags !ffunE.
Qed.

Definition independent_flags (coin : R.-fdist bool) :=
  fdistmap row_flags (coin `^ n.+1).

Lemma independent_all_flags coin : independent_flags coin all_flags = (coin true)^+n.+1.
Proof.
have H : row_flags (\row_i true) = all_flags.
  by apply/ffunP => i; rewrite /row_flags /all_flags !ffunE mxE.
rewrite /independent_flags fdistmapE -H (big_pred1_inj row_flags_injective) fdist_rVE.
under eq_bigr do rewrite mxE.
by rewrite prodr_const card_ord.
Qed.

Corollary independent_probe_bound coin s t :
  NoisyLeakage.TV (probe_law (independent_flags coin) s) (probe_law (independent_flags coin) t) <=
    (coin true)^+n.+1.
Proof. by move: (random_probe_bound (independent_flags coin) s t); rewrite independent_all_flags. Qed.

(* Applying this to HW noise requires proving that the actual channel has this simulation. *)
Corollary simulated_channel_bound coin (O : finType) (channel : View -> R.-fdist O) s t :
  NoisyLeakage.TV (probe_law (independent_flags coin) s >>= channel)
    (probe_law (independent_flags coin) t >>= channel) <= (coin true)^+n.+1.
Proof.
apply: Order.POrderTheory.le_trans (NoisyLeakage.channel_TV_contraction _ _ _) _.
exact: independent_probe_bound.
Qed.

End Probes.
End ArithmeticPrivacy.

Print Assumptions ArithmeticPrivacy.missing_share_independent.
Print Assumptions ArithmeticPrivacy.random_probe_bound.
Print Assumptions ArithmeticPrivacy.independent_probe_bound.
Print Assumptions ArithmeticPrivacy.simulated_channel_bound.
