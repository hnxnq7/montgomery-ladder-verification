From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From infotheo Require Import fdist.
From Masking Require Import finite_masking.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory FiniteMasking.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Module XorShares.

(* d counts extra shares; even d=0 stores one bit. *)
Fixpoint share_type (d : nat) : finType :=
  match d with
  | O => [the finType of (bool : Type)]
  | S n => [the finType of (bool * share_type n)%type]
  end.

Fixpoint reconstruct (d : nat) : share_type d -> bool :=
  match d as k return share_type k -> bool with
  | O => fun b => b
  | S n => fun p => xorb p.1 (@reconstruct n p.2)
  end.
Arguments reconstruct d _ : clear implicits.

Fixpoint hw (d : nat) : share_type d -> nat :=
  match d as k return share_type k -> nat with
  | O => fun b => nat_of_bool b
  | S n => fun p => (nat_of_bool p.1 + @hw n p.2)%N
  end.
Arguments hw d _ : clear implicits.

Lemma hw_bound d (s : share_type d) : (hw d s <= d.+1)%N.
Proof.
elim: d s => [|d IH] s; first by case: s.
case: s => b tail. case: b => /=.
- exact: IH.
- exact: leq_trans (IH tail) (leqnSn d.+1).
Qed.

Section Distributions.
Variable R : realType.

Definition fair : R.-fdist bool :=
  fdist_uniform card_bool.

Lemma fair_mass b : fair b = 2^-1.
Proof. by rewrite /fair fdist_uniformE card_bool. Qed.

Fixpoint share (d : nat) (secret : bool) : R.-fdist (share_type d) :=
  match d as k return R.-fdist (share_type k) with
  | O => fdist1 secret
  | S n => fair >>= (fun r =>
      fdistmap (fun tail => (r, tail)) (share n (xorb secret r)))
  end.

Theorem share_correct d secret :
  fdistmap (reconstruct d) (share d secret) = fdist1 secret.
Proof.
elim: d secret => [|d IH] secret; first by rewrite /= fdistmap1.
rewrite /= map_bind.
transitivity (fair >>= (fun _ => fdist1 secret)).
- congr (fdistbind fair _). apply/boolp.funeqP => r.
  rewrite fdistmap_comp.
  change (fdistmap (xorb r \o reconstruct d) (share d (xorb secret r)) = fdist1 secret).
  rewrite -(fdistmap_comp (xorb r) (reconstruct d)) IH fdistmap1.
  by case: secret; case: r.
- exact: bind_constant.
Qed.

End Distributions.
End XorShares.

Print Assumptions XorShares.hw_bound.
Print Assumptions XorShares.share_correct.
