From mathcomp Require Import boot order algebra reals field_tactic.
From infotheo Require Import fdist variation_dist.
From Masking Require Import finite_masking noisy_leakage noisy_bit_example xor_shares.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.POrderTheory FiniteMasking NoisyLeakage.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module NoisyShares.
Section Noise.
Variable R : realType.

Definition bit_channel (b : bool) : R.-fdist 'I_3 :=
  fdistmap (fun c => inord (NoisyBitExample.bit_value b + NoisyBitExample.bit_value c))
    (NoisyBitExample.fair R).

Lemma bit_channel_mass b (y : 'I_3) :
  bit_channel b y =
  (nth 0%N (if b then [:: 0; 1; 1]%N else [:: 1; 1; 0]%N) (val y))%:R / 2.
Proof.
case: b; case: y => -[|[|[|i]]] // Hi;
  rewrite /bit_channel NoisyBitExample.map_fair_mass /NoisyBitExample.bit_value
    /= -!val_eqE /= !inordK //=; field by rewrite ?pnatr_eq0.
Qed.

(* Exposing each noisy share separately is stronger than exposing their sum. *)
Definition extend (A : finType) (tail : bool -> R.-fdist A) s :=
  NoisyBitExample.fair R >>= (fun r => (bit_channel r) `x (tail (xorb s r))).

Lemma extend_mass (A : finType) (tail : bool -> R.-fdist A) s h a :
  extend tail s (h, a) =
    (bit_channel true h * tail (xorb s true) a +
     bit_channel false h * tail (xorb s false) a) / 2.
Proof.
rewrite /extend fdistbindE big_bool !NoisyBitExample.fair_mass !fdist_prodE /=.
field by rewrite ?pnatr_eq0.
Qed.

Lemma extend_difference (A : finType) (tail : bool -> R.-fdist A) (h : 'I_3) a :
  extend tail false (h, a) - extend tail true (h, a) =
    (if val h == 0%N then tail false a - tail true a
     else if val h == 2%N then tail true a - tail false a else 0) / 4.
Proof.
case: h => -[|[|[|i]]] // Hi;
  rewrite !extend_mass !bit_channel_mass /=; field by rewrite ?pnatr_eq0.
Qed.

Lemma extend_L1 (A : finType) (tail : bool -> R.-fdist A) :
  var_dist (extend tail false) (extend tail true) = var_dist (tail false) (tail true) / 2.
Proof.
have H a : (\sum_(h : 'I_3) `|extend tail false (h, a) - extend tail true (h, a)|) =
    `|tail false a - tail true a| / 2.
  under eq_bigr do rewrite extend_difference.
  rewrite !big_ord_recr big_ord0 /=.
  rewrite mul0r normr0 !normrM !normfV !normr_nat distrC.
  field by rewrite ?pnatr_eq0.
rewrite /var_dist.
have E (p : 'I_3 * A) : `|extend tail false p - extend tail true p| =
    `|extend tail false (p.1, p.2) - extend tail true (p.1, p.2)| by case: p.
rewrite (eq_bigr _ (fun p _ => E p)).
rewrite -(pair_bigA _ (fun h a =>
  `|extend tail false (h, a) - extend tail true (h, a)|)) /= exchange_big.
by rewrite (eq_bigr _ (fun a _ => H a)) -big_distrl.
Qed.

Lemma product_bind (A B : finType) (d : R.-fdist A) (e : R.-fdist B) :
  d `x e = d >>= (fun a => fdistmap (fun b => (a, b)) e).
Proof.
apply/fdist_ext => -[a b]. rewrite fdist_prodE /= fdistbindE.
have H x : fdistmap (fun y => (x, y)) e (a, b) = if x == a then e b else 0.
  rewrite fdistmapE /=.
  under eq_bigl do rewrite !inE xpair_eqE.
  case E: (x == a); first by rewrite /= big_pred1_eq.
  by rewrite /= big_pred0.
rewrite (eq_bigr _ (fun x _ => congr1 (fun z => d x * z) (H x))).
rewrite (bigD1 a) // eqxx /=.
rewrite big1 ?addr0 // => x /negbTE Hxa.
by rewrite Hxa mulr0.
Qed.

Fixpoint fine_type (d : nat) : finType :=
  match d with
  | O => [the finType of 'I_3]
  | S n => [the finType of ('I_3 * fine_type n)%type]
  end.

Fixpoint fine_law (d : nat) (s : bool) : R.-fdist (fine_type d) :=
  match d as n return R.-fdist (fine_type n) with
  | O => bit_channel s
  | S n => extend (fine_law n) s
  end.

Theorem fine_TV d :
  TV (fine_law d false) (fine_law d true) = (2^-1) ^+ d.+1.
Proof.
elim: d => [|d IH].
- rewrite /TV /var_dist /=.
  under eq_bigr do rewrite !bit_channel_mass.
  rewrite !big_ord_recr big_ord0 /=.
  rewrite ?mul0r ?mul1r ?subr0 ?subrr ?sub0r ?normr0 ?normrN ?normfV ?normr_nat ?expr1.
  field by rewrite ?pnatr_eq0.
- rewrite /TV /= extend_L1.
  change (TV (fine_law d false) (fine_law d true) / 2 = (2^-1) ^+ d.+2).
  rewrite IH [RHS]exprS.
  exact: mulrC.
Qed.

Lemma fine_bound d s t :
  TV (fine_law d s) (fine_law d t) <= (2^-1) ^+ d.+1.
Proof.
case: s; case: t; try by rewrite TV_self exprn_ge0 // invr_ge0 ler0n.
- rewrite /TV symmetric_var_dist -/(TV (fine_law d false) (fine_law d true)) fine_TV.
  exact: lexx.
- by rewrite fine_TV.
Qed.

(* Keep the actual shares alongside the observations, so erasure checks the encoding. *)
Fixpoint sample (d : nat) (s : bool) :
    R.-fdist [the finType of (XorShares.share_type d * fine_type d)%type] :=
  match d as n return R.-fdist [the finType of (XorShares.share_type n * fine_type n)%type] with
  | O => fdistmap (fun h => (s, h)) (bit_channel s)
  | S n => NoisyBitExample.fair R >>= (fun r => bit_channel r >>= (fun h =>
      fdistmap (fun p => ((r, p.1), (h, p.2))) (sample n (xorb s r))))
  end.

Lemma sample_shares d s :
  fdistmap fst (sample d s) = XorShares.share R d s.
Proof.
elim: d s => [|d IH] s.
- rewrite /= fdistmap_comp. exact: map_constant.
- rewrite /= map_bind.
  congr (fdistbind (NoisyBitExample.fair R) _). apply/boolp.funeqP => r.
  rewrite map_bind.
  transitivity (bit_channel r >>= (fun _ =>
    fdistmap (fun t => (r, t)) (XorShares.share R d (xorb s r)))).
  + congr (fdistbind (bit_channel r) _). apply/boolp.funeqP => h.
    rewrite fdistmap_comp.
    change (fdistmap ((fun t => (r, t)) \o fst) (sample d (xorb s r)) =
      fdistmap (fun t => (r, t)) (XorShares.share R d (xorb s r))).
    by rewrite -fdistmap_comp IH.
  + exact: bind_constant.
Qed.

Lemma sample_observations d s : fdistmap snd (sample d s) = fine_law d s.
Proof.
elim: d s => [|d IH] s.
- by rewrite /= fdistmap_comp /= fdistmap_id.
- rewrite /= map_bind /extend.
  congr (fdistbind (NoisyBitExample.fair R) _). apply/boolp.funeqP => r.
  rewrite map_bind product_bind.
  congr (fdistbind (bit_channel r) _). apply/boolp.funeqP => h.
  rewrite fdistmap_comp.
  change (fdistmap ((fun t => (h, t)) \o snd) (sample d (xorb s r)) =
    fdistmap (fun t => (h, t)) (fine_law d (xorb s r))).
  by rewrite -fdistmap_comp IH.
Qed.

Theorem sample_correct d s :
  fdistmap (fun p => XorShares.reconstruct d p.1) (sample d s) = fdist1 s.
Proof.
rewrite -(fdistmap_comp (XorShares.reconstruct d) fst) sample_shares.
exact: XorShares.share_correct.
Qed.

Fixpoint fine_sum (d : nat) : fine_type d -> nat :=
  match d as n return fine_type n -> nat with
  | O => fun h => val h
  | S n => fun p => (val p.1 + @fine_sum n p.2)%N
  end.

Lemma fine_sum_bound d (x : fine_type d) : (fine_sum x <= 2 * d.+1)%N.
Proof.
elim: d x => [|d IH] x.
- change (val x <= 2)%N. by rewrite -ltnS; exact: ltn_ord.
- case: x => h t. change (val h + @fine_sum d t <= 2 * d.+2)%N.
  rewrite mulnS. apply: leq_add; last exact: IH.
  by rewrite -ltnS; exact: ltn_ord.
Qed.

Fixpoint noise_sum (e : nat) : repetitions_type [the finType of (bool : Type)] e -> nat :=
  match e as n return repetitions_type [the finType of (bool : Type)] n -> nat with
  | O => fun _ => 0%N
  | S n => fun p => (NoisyBitExample.bit_value p.1 + @noise_sum n p.2)%N
  end.

Lemma noise_sum_bound e (x : repetitions_type [the finType of (bool : Type)] e) :
  (noise_sum x <= e)%N.
Proof.
elim: e x => [|e IH] x; first by [].
case: x => b t. case: b => /=.
- exact: IH.
- exact: leq_trans (IH t) (leqnSn e).
Qed.

Definition aggregate_value d e (x : fine_type d) (noise : repetitions_type [the finType of (bool : Type)] e)
    : 'I_(2 * d.+1 + e).+1 :=
  inord (fine_sum x + noise_sum noise).

Lemma aggregate_no_wrap d e (x : fine_type d) noise :
  val (@aggregate_value d e x noise) = (fine_sum x + noise_sum noise)%N.
Proof.
rewrite /aggregate_value /= inordK //.
rewrite ltnS. exact: leq_add (fine_sum_bound x) (noise_sum_bound noise).
Qed.

Definition aggregate_channel d e (x : fine_type d) :=
  fdistmap (@aggregate_value d e x) (iid (NoisyBitExample.fair R) e).

(* d+1 shares, d+1+e independent fair noise bits, and no modular reduction. *)
Definition aggregate_law d e s :=
  apply_channel (fine_law d s) (@aggregate_channel d e).

Theorem aggregate_TV_bound d e s t :
  TV (aggregate_law d e s) (aggregate_law d e t) <= (2^-1) ^+ d.+1.
Proof.
exact: le_trans (channel_TV_contraction _ _ _) (fine_bound d s t).
Qed.

End Noise.
End NoisyShares.

Print Assumptions NoisyShares.fine_TV.
Print Assumptions NoisyShares.sample_correct.
Print Assumptions NoisyShares.aggregate_TV_bound.
