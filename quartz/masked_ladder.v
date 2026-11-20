From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import masked_arithmetic.
From Masking Require Import fiat_field arithmetic_shares shared_ladder arithmetic_control arithmetic_ladder.
From Stdlib Require Import ZArith Bits Vector.

Module MaskedLadder.
Module M := MaskedArithmetic.
Module Core := M.Core.
Import fn type InterfaceExample.QStdlib.
Import (notations) eexpr expr.
Local Open Scope string_scope.

Definition Coordinates k := Pair (Pair (M.Shares k) (M.Shares k)) (Pair (M.Shares k) (M.Shares k)).
Definition Tape k := Array (M.Masks k) 18.
Definition StepInput k := Pair (M.Shares k) (Pair (M.Shares k) (Pair (Coordinates k) (Tape k))).
Definition SwapInput k := Pair (M.Shares k) (Pair (M.Shares k) (Pair (M.Shares k) (M.Masks k))).
Definition SwapOutput k := Pair (M.Shares k) (Pair (M.Shares k) (M.Shares k)).

Definition decode_coordinates k (c : type.interp (Coordinates k)) :=
  ((M.decode k c.1.1, M.decode k c.1.2), (M.decode k c.2.1, M.decode k c.2.2)).
Definition canonical_coordinates k (c : type.interp (Coordinates k)) :=
  M.canonical k c.1.1 /\ M.canonical k c.1.2 /\ M.canonical k c.2.1 /\ M.canonical k c.2.2.
Definition decode_tape k (r : type.interp (Tape k)) : ArithmeticLadder.mask_tape FiatField.curve25519 k :=
  [ffun i => M.decode_masks k (@M.read (M.Masks k) 18 r (val i))].

Definition get_mask {var} k (i : 'I_18) : fn var (Tape k) (M.Masks k) :=
  Fn (fun r => quartz_eexpr:(
    let i := $(expr.Const (t := Bits (M.index_width 18)) (M.index_bits 18 i)) in
    return #r[#i])).

Lemma get_mask_interp k i r :
  fn.interp (get_mask k i) r = @M.read (M.Masks k) 18 r (val i).
Proof.
  change (@M.read (M.Masks k) 18 r (Z.to_nat (Zmod.unsigned (M.index_bits 18 i))) =
    @M.read (M.Masks k) 18 r (val i)).
  by rewrite M.index_unsigned Nat2Z.id.
Qed.

(* The control remains shared; the executable function never branches on its value. *)
Definition cswap {var} k : fn var (SwapInput k) (SwapOutput k) :=
  Fn (fun p => quartz_eexpr:(
    let b := #p .1 in let left := #p .2 .1 in
    let right := #p .2 .2 .1 in let r := #p .2 .2 .2 in
    let difference := {M.share_map Core.Sub k} ((#right,#left)) in
    let delta := {M.multiply k} ((#b,(#difference,#r))) in
    let left := {M.share_map Core.Add k} ((#left,#delta)) in
    let right := {M.share_map Core.Sub k} ((#right,#delta)) in
    return (#b,(#left,#right)))).

Local Opaque M.share_map M.multiply get_mask.

Definition xor_bits {var} k : fn var (Pair (M.Shares k) (Pair (M.Shares k) (M.Masks k))) (M.Shares k) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let b := #p .2 .1 in let r := #p .2 .2 in
    let sum := {M.share_map Core.Add k} ((#a,#b)) in
    let product := {M.multiply k} ((#a,(#b,#r))) in
    let twice := {M.share_map Core.Add k} ((#product,#product)) in
    let result := {M.share_map Core.Sub k} ((#sum,#twice)) in
    return #result)).

Lemma xor_bits_interp k a b r :
  fn.interp (xor_bits k) (a,(b,r)) =
  let product := fn.interp (M.multiply k) (a,(b,r)) in
  fn.interp (M.share_map Core.Sub k)
    (fn.interp (M.share_map Core.Add k) (a,b),
     fn.interp (M.share_map Core.Add k) (product,product)).
Proof. reflexivity. Qed.

Theorem xor_bits_refines k a b r :
  M.decode k (fn.interp (xor_bits k) (a,(b,r))) =
  ArithmeticControl.xor_bits (M.decode k a) (M.decode k b) (M.decode_masks k r).
Proof.
  rewrite xor_bits_interp /ArithmeticControl.xor_bits.
  by rewrite M.sub_refines !M.add_refines M.multiply_refines.
Qed.

Theorem xor_bits_canonical k a b r : M.canonical k (fn.interp (xor_bits k) (a,(b,r))).
Proof. rewrite xor_bits_interp. apply M.share_map_canonical. Qed.

Corollary xor_bits_correct k a b r (s t : bool) :
  ArithmeticShares.reconstruct (M.decode k a) = (if s then 1 else 0)%R ->
  ArithmeticShares.reconstruct (M.decode k b) = (if t then 1 else 0)%R ->
  ArithmeticShares.reconstruct (M.decode k (fn.interp (xor_bits k) (a,(b,r)))) =
    (if xorb s t then 1 else 0)%R.
Proof. rewrite xor_bits_refines. apply ArithmeticControl.xor_bits_correct. Qed.

Lemma cswap_interp k b left right r :
  fn.interp (cswap k) (b,(left,(right,r))) =
  let difference := fn.interp (M.share_map Core.Sub k) (right,left) in
  let delta := fn.interp (M.multiply k) (b,(difference,r)) in
  (b,(fn.interp (M.share_map Core.Add k) (left,delta),
      fn.interp (M.share_map Core.Sub k) (right,delta))).
Proof. reflexivity. Qed.

Definition decode_swap k (c : type.interp (SwapOutput k)) :=
  (M.decode k c.1, (M.decode k c.2.1, M.decode k c.2.2)).

Theorem cswap_refines k b left right r :
  decode_swap k (fn.interp (cswap k) (b,(left,(right,r)))) =
  ArithmeticControl.cswap (M.decode k b) (M.decode k left) (M.decode k right) (M.decode_masks k r).
Proof.
  rewrite cswap_interp /decode_swap /ArithmeticControl.cswap /=.
  by rewrite M.add_refines M.sub_refines M.multiply_refines M.sub_refines.
Qed.

Theorem cswap_control k b left right r :
  (fn.interp (cswap k) (b,(left,(right,r)))).1 = b.
Proof. reflexivity. Qed.

Corollary cswap_correct k b left right r (bit : bool) :
  ArithmeticShares.reconstruct (M.decode k b) = (if bit then 1 else 0)%R ->
  let out := decode_swap k (fn.interp (cswap k) (b,(left,(right,r)))) in
  (ArithmeticShares.reconstruct out.2.1, ArithmeticShares.reconstruct out.2.2) =
  if bit then (ArithmeticShares.reconstruct (M.decode k right), ArithmeticShares.reconstruct (M.decode k left))
  else (ArithmeticShares.reconstruct (M.decode k left), ArithmeticShares.reconstruct (M.decode k right)).
Proof. rewrite cswap_refines. apply ArithmeticControl.cswap_correct. Qed.

Theorem cswap_canonical k b left right r :
  M.canonical k b ->
  let out := fn.interp (cswap k) (b,(left,(right,r))) in
  M.canonical k out.1 /\ M.canonical k out.2.1 /\ M.canonical k out.2.2.
Proof.
  move=> Hb. rewrite cswap_interp /=. split; first exact Hb.
  split; apply M.share_map_canonical.
Qed.

(* Combinational reference only. The clocked controller must retain and observe its intermediates.
   Mask addresses agree with ArithmeticLadder.step; coins remain runtime inputs. *)
Definition step {var} k : fn var (StepInput k) (Coordinates k) :=
  Fn (fun p => quartz_eexpr:(
    let a24 := #p .1 in let xP := #p .2 .1 in
    let c := #p .2 .2 .1 in let r := #p .2 .2 .2 in
    let x2 := #c .1 .1 in let z2 := #c .1 .2 in
    let x3 := #c .2 .1 in let z3 := #c .2 .2 in
    let u := {M.share_map Core.Add k} ((#x2,#z2)) in
    let v := {M.share_map Core.Sub k} ((#x2,#z2)) in
    let w := {M.share_map Core.Add k} ((#x3,#z3)) in
    let t := {M.share_map Core.Sub k} ((#x3,#z3)) in
    let mask := {get_mask k (inord 4)} (#r) in
    let u2 := {M.multiply k} ((#u,(#u,#mask))) in
    let mask := {get_mask k (inord 5)} (#r) in
    let v2 := {M.multiply k} ((#v,(#v,#mask))) in
    let mask := {get_mask k (inord 6)} (#r) in
    let ut := {M.multiply k} ((#u,(#t,#mask))) in
    let mask := {get_mask k (inord 7)} (#r) in
    let vw := {M.multiply k} ((#v,(#w,#mask))) in
    let sp := {M.share_map Core.Add k} ((#ut,#vw)) in
    let sm := {M.share_map Core.Sub k} ((#ut,#vw)) in
    let mask := {get_mask k (inord 10)} (#r) in
    let xa := {M.multiply k} ((#sp,(#sp,#mask))) in
    let mask := {get_mask k (inord 11)} (#r) in
    let sm2 := {M.multiply k} ((#sm,(#sm,#mask))) in
    let mask := {get_mask k (inord 12)} (#r) in
    let za := {M.multiply k} ((#sm2,(#xP,#mask))) in
    let mask := {get_mask k (inord 13)} (#r) in
    let xd := {M.multiply k} ((#u2,(#v2,#mask))) in
    let d := {M.share_map Core.Sub k} ((#u2,#v2)) in
    let mask := {get_mask k (inord 15)} (#r) in
    let ad := {M.multiply k} ((#a24,(#d,#mask))) in
    let t2 := {M.share_map Core.Add k} ((#v2,#ad)) in
    let mask := {get_mask k (inord 17)} (#r) in
    let zd := {M.multiply k} ((#d,(#t2,#mask))) in
    return ((#xd,#zd),(#xa,#za)))).

Lemma step_interp k a24 xP x2 z2 x3 z3 r :
  fn.interp (step k) (a24,(xP,(((x2,z2),(x3,z3)),r))) =
  let u := fn.interp (M.share_map Core.Add k) (x2,z2) in
  let v := fn.interp (M.share_map Core.Sub k) (x2,z2) in
  let w := fn.interp (M.share_map Core.Add k) (x3,z3) in
  let t := fn.interp (M.share_map Core.Sub k) (x3,z3) in
  let u2 := fn.interp (M.multiply k) (u,(u,fn.interp (get_mask k (inord 4)) r)) in
  let v2 := fn.interp (M.multiply k) (v,(v,fn.interp (get_mask k (inord 5)) r)) in
  let ut := fn.interp (M.multiply k) (u,(t,fn.interp (get_mask k (inord 6)) r)) in
  let vw := fn.interp (M.multiply k) (v,(w,fn.interp (get_mask k (inord 7)) r)) in
  let sp := fn.interp (M.share_map Core.Add k) (ut,vw) in
  let sm := fn.interp (M.share_map Core.Sub k) (ut,vw) in
  let xa := fn.interp (M.multiply k) (sp,(sp,fn.interp (get_mask k (inord 10)) r)) in
  let sm2 := fn.interp (M.multiply k) (sm,(sm,fn.interp (get_mask k (inord 11)) r)) in
  let za := fn.interp (M.multiply k) (sm2,(xP,fn.interp (get_mask k (inord 12)) r)) in
  let xd := fn.interp (M.multiply k) (u2,(v2,fn.interp (get_mask k (inord 13)) r)) in
  let d := fn.interp (M.share_map Core.Sub k) (u2,v2) in
  let ad := fn.interp (M.multiply k) (a24,(d,fn.interp (get_mask k (inord 15)) r)) in
  let t2 := fn.interp (M.share_map Core.Add k) (v2,ad) in
  let zd := fn.interp (M.multiply k) (d,(t2,fn.interp (get_mask k (inord 17)) r)) in
  ((xd,zd),(xa,za)).
Proof. reflexivity. Qed.

Theorem step_refines k a24 xP x2 z2 x3 z3 r :
  decode_coordinates k (fn.interp (step k) (a24,(xP,(((x2,z2),(x3,z3)),r)))) =
  ArithmeticLadder.step (M.decode k a24) (M.decode k xP)
    (M.decode k x2) (M.decode k z2) (M.decode k x3) (M.decode k z3) (decode_tape k r).
Proof.
  rewrite step_interp /decode_coordinates /ArithmeticLadder.step /=.
  repeat first [rewrite M.multiply_refines | rewrite M.add_refines | rewrite M.sub_refines].
  by rewrite /decode_tape !ffunE !get_mask_interp.
Qed.

Theorem step_canonical k a24 xP x2 z2 x3 z3 r :
  canonical_coordinates k (fn.interp (step k) (a24,(xP,(((x2,z2),(x3,z3)),r)))).
Proof.
  rewrite step_interp /canonical_coordinates /=.
  repeat split; apply M.multiply_canonical.
Qed.

Corollary step_correct k a24 xP x2 z2 x3 z3 r :
  ArithmeticLadder.reconstruct_coordinates
    (decode_coordinates k (fn.interp (step k) (a24,(xP,(((x2,z2),(x3,z3)),r))))) =
  SharedLadder.clear_step (ArithmeticShares.reconstruct (M.decode k a24))
    (ArithmeticShares.reconstruct (M.decode k xP))
    (ArithmeticShares.reconstruct (M.decode k x2)) (ArithmeticShares.reconstruct (M.decode k z2))
    (ArithmeticShares.reconstruct (M.decode k x3)) (ArithmeticShares.reconstruct (M.decode k z3)).
Proof. rewrite step_refines. apply ArithmeticLadder.step_correct. Qed.

End MaskedLadder.

Print Assumptions MaskedLadder.cswap_refines.
Print Assumptions MaskedLadder.xor_bits_refines.
Print Assumptions MaskedLadder.xor_bits_correct.
Print Assumptions MaskedLadder.cswap_canonical.
Print Assumptions MaskedLadder.cswap_correct.
Print Assumptions MaskedLadder.step_refines.
Print Assumptions MaskedLadder.step_canonical.
Print Assumptions MaskedLadder.step_correct.
