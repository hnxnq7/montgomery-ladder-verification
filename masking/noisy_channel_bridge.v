From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking noisy_leakage noisy_bit_example xor_shares noisy_shares.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking NoisyLeakage NoisyShares.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module NoisyChannelBridge.
Section Bridge.
Variable R : realType.

Lemma bind_swap (A B C : finType) (d : R.-fdist A) (e : R.-fdist B)
    (f : A -> B -> R.-fdist C) :
  (d >>= (fun a => e >>= f a)) = (e >>= (fun b => d >>= (fun a => f a b))).
Proof.
apply/fdist_ext => y. rewrite !fdistbindE.
have H a : d a * (e >>= f a) y = \sum_(b : B) d a * (e b * f a b y).
  by rewrite fdistbindE big_distrr.
rewrite (eq_bigr _ (fun a _ => H a)) exchange_big.
apply: eq_bigr => b _. rewrite fdistbindE big_distrr /=.
apply: eq_bigr => a _. by rewrite !mulrA [d a * e b]mulrC.
Qed.

Lemma product_bind_right (A B C : finType) (d : R.-fdist A) (e : R.-fdist B)
    (f : B -> R.-fdist C) :
  d `x (e >>= f) = e >>= (fun b => d `x (f b)).
Proof.
rewrite product_bind.
have -> : (fun a : A => fdistmap (fun c => (a, c)) (e >>= f)) =
    (fun a => e >>= (fun b => fdistmap (fun c => (a, c)) (f b))).
  by apply/boolp.funeqP => a; rewrite map_bind.
rewrite bind_swap. congr (fdistbind e _).
apply/boolp.funeqP => b. by rewrite product_bind.
Qed.

(* Each stored share gets an independent instance of the same bit channel. *)
Fixpoint per_share_channel (d : nat) : XorShares.share_type d -> R.-fdist (fine_type d) :=
  match d as n return XorShares.share_type n -> R.-fdist (fine_type n) with
  | O => fun b => bit_channel R b
  | S n => fun p => (bit_channel R p.1) `x (@per_share_channel n p.2)
  end.
Arguments per_share_channel d _ : clear implicits.

Theorem fine_law_as_share_channel d s :
  fine_law R d s = XorShares.share R d s >>= per_share_channel d.
Proof.
elim: d s => [|d IH] s; first by rewrite /= fdist1bind.
rewrite /= /extend fdistbindA.
congr (fdistbind (NoisyBitExample.fair R) _).
apply/boolp.funeqP => r.
rewrite bind_map IH product_bind_right. reflexivity.
Qed.

Definition scalar_channel (bound count offset : nat) : R.-fdist 'I_bound.+1 :=
  fdistmap (fun noise => inord (offset + noise_sum noise)) (iid (NoisyBitExample.fair R) count).

Lemma scalar_channel_no_clip bound count offset
    (noise : repetitions_type [the finType of (bool : Type)] count) :
  (offset + count <= bound)%N ->
  val (inord (offset + noise_sum noise) : 'I_bound.+1) = (offset + noise_sum noise)%N.
Proof.
move=> H. rewrite /= inordK // ltnS.
apply: leq_trans _ H. exact: leq_add (leqnn offset) (noise_sum_bound noise).
Qed.

Lemma share_channel_no_clip d e (a : XorShares.share_type d)
    (noise : repetitions_type [the finType of (bool : Type)] (d.+1 + e)) :
  val (inord (XorShares.hw d a + noise_sum noise) : 'I_(2 * d.+1 + e).+1) =
    (XorShares.hw d a + noise_sum noise)%N.
Proof.
apply: scalar_channel_no_clip.
rewrite addnA mul2n -addnn.
apply: leq_add; last exact: leqnn.
apply: leq_add; [exact: XorShares.hw_bound | exact: leqnn].
Qed.

Lemma scalar_channel_S bound count offset :
  scalar_channel bound count.+1 offset = NoisyBitExample.fair R >>= (fun b =>
    scalar_channel bound count (offset + NoisyBitExample.bit_value b)).
Proof.
rewrite /scalar_channel /= product_bind map_bind.
congr (fdistbind (NoisyBitExample.fair R) _).
apply/boolp.funeqP => b. rewrite fdistmap_comp.
congr (fdistmap _ _). apply/boolp.funeqP => noise.
by rewrite /comp /= addnA.
Qed.

Definition sum_after d bound e offset (x : fine_type d) : R.-fdist 'I_bound.+1 :=
  scalar_channel bound e (offset + fine_sum x).

Lemma per_share_sum_channel d bound e offset (a : XorShares.share_type d) :
  per_share_channel d a >>= (@sum_after d bound e offset) =
  scalar_channel bound (d.+1 + e) (offset + XorShares.hw d a).
Proof.
elim: d a offset => [|d IH] a offset.
- rewrite /= /bit_channel bind_map scalar_channel_S.
  congr (fdistbind (NoisyBitExample.fair R) _).
  apply/boolp.funeqP => b.
  rewrite /sum_after /=.
  rewrite inordK; first by case: a; case: b.
  congr (scalar_channel _ _ _).
  by case: a; case: b; rewrite /NoisyBitExample.bit_value /= ?addn0 ?addn1 ?addnS ?addn0.
- case: a => a tail.
  rewrite /= product_bind fdistbindA.
  rewrite /bit_channel bind_map scalar_channel_S.
  congr (fdistbind (NoisyBitExample.fair R) _).
  apply/boolp.funeqP => b.
  rewrite bind_map.
  have Hfun : (fun x => @sum_after d.+1 bound e offset (inord
      (NoisyBitExample.bit_value a + NoisyBitExample.bit_value b), x)) =
      @sum_after d bound e (offset + NoisyBitExample.bit_value a + NoisyBitExample.bit_value b).
    apply/boolp.funeqP => x. rewrite /sum_after /= inordK; first by case: a; case: b.
    by rewrite !addnA.
  rewrite Hfun IH. clear Hfun.
  congr (scalar_channel _ _ _).
  case: a; case: b; rewrite /NoisyBitExample.bit_value /= !addnA.
  all: by rewrite ?addn0 ?addn1 ?addnS ?addSn.
Qed.

(* The common scalar channel depends on the raw HW, not on the secret or share layout. *)
Theorem aggregate_common_channel d e s :
  aggregate_law R d e s = XorShares.share R d s >>= (fun a =>
    scalar_channel (2 * d.+1 + e) (d.+1 + e) (XorShares.hw d a)).
Proof.
rewrite /aggregate_law /apply_channel fine_law_as_share_channel fdistbindA.
congr (fdistbind (XorShares.share R d s) _).
apply/boolp.funeqP => a.
change (per_share_channel d a >>= (@sum_after d (2 * d.+1 + e) e 0) =
  scalar_channel (2 * d.+1 + e) (d.+1 + e) (XorShares.hw d a)).
by rewrite per_share_sum_channel add0n.
Qed.

Theorem aggregate_as_HW_channel d e s :
  aggregate_law R d e s = apply_channel
    (fdistmap (fun a => inord (XorShares.hw d a) : 'I_d.+2) (XorShares.share R d s))
    (fun h => scalar_channel (2 * d.+1 + e) (d.+1 + e) (val h)).
Proof.
rewrite /apply_channel bind_map aggregate_common_channel.
congr (fdistbind (XorShares.share R d s) _).
apply/boolp.funeqP => a.
by rewrite /= inordK // ltnS; exact: XorShares.hw_bound.
Qed.

Definition dual_law d e (s : bool) :=
  scalar_channel (2 * d.+1 + e) (d.+1 + e)
    (NoisyBitExample.bit_value s + NoisyBitExample.bit_value (negb s)).

Theorem dual_laws_equal d e s t : dual_law d e s = dual_law d e t.
Proof. by case: s; case: t. Qed.

End Bridge.
End NoisyChannelBridge.

Print Assumptions NoisyChannelBridge.fine_law_as_share_channel.
Print Assumptions NoisyChannelBridge.aggregate_common_channel.
Print Assumptions NoisyChannelBridge.share_channel_no_clip.
Print Assumptions NoisyChannelBridge.dual_laws_equal.
