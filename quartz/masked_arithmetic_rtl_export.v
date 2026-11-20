From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax transform pp sv.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import masked_arithmetic.
From Masking Require Import arithmetic_shares.
From mathcomp Require Import boot.
From Stdlib Require Import String ZArith Bits.
Import fn Syntax.type InterfaceExample.QStdlib.
Import (notations) Syntax.eexpr Syntax.expr.
Local Open Scope string_scope.

(* Static specialization only: operands and mask arrays remain runtime inputs. *)
Module MaskedArithmeticRTL.
Module M := MaskedArithmetic.
Module Core := M.Core.

Fixpoint indices k : seq 'I_k :=
  match k with
  | O => [::]
  | S n => ord0 :: map (lift ord0) (indices n)
  end.

Lemma indices_correct k : indices k = enum 'I_k.
Proof.
  induction k as [|k IH]; simpl.
  - symmetry. apply enum_ord0.
  - rewrite IH. symmetry. apply enum_ordSl.
Qed.

Definition pairs k :=
  filter (fun ij : 'I_k * 'I_k => ssrnat.ltn (val ij.1) (val ij.2))
    [seq (i,j) | i <- indices k, j <- indices k].

Lemma pairs_correct k : pairs k = ArithmeticShares.pair_order k.
Proof.
  rewrite /pairs indices_correct /ArithmeticShares.pair_order /index_enum unlock.
  rewrite Finite.enum.unlock.
  reflexivity.
Qed.

Definition static_map {var} op k : fn var (Pair (M.Shares k) (M.Shares k)) (M.Shares k) :=
  Fn (fun p => quartz_eexpr:(
    let c := $(Syntax.expr.Const (t := M.Shares k) (type.default (M.Shares k))) in
    let result := {M.map_steps op k (indices k)} ((#p .1,(#p .2,#c))) in
    return #result)).

Lemma static_map_correct {var} op k : @static_map var op k = M.share_map op k.
Proof. unfold static_map. rewrite indices_correct. reflexivity. Qed.

Definition static_multiply {var} k :
    fn var (Pair (M.Shares k) (Pair (M.Shares k) (M.Masks k))) (M.Shares k) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let b := #p .2 .1 in let r := #p .2 .2 in
    let c := {static_map Core.Mul k} ((#a,#b)) in
    let result := {M.multiply_steps k (pairs k)} ((#a,(#b,(#r,#c)))) in
    return #result)).

Lemma static_multiply_correct {var} k : @static_multiply var k = M.multiply k.
Proof. unfold static_multiply. rewrite static_map_correct pairs_correct. reflexivity. Qed.

Definition static_refresh {var} n : fn var (Pair (M.Shares (S n)) (M.Shares n)) (M.Shares (S n)) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let r := #p .2 in
    let h := {M.get (S n) ord0} (#a) in
    let h := {M.refresh_anchor n (indices n)} ((#h,#r)) in
    let c := {M.refresh_tail n (indices n)} ((#a,(#r,#a))) in
    let c := {M.put (S n) ord0} ((#c,#h)) in
    return #c)).

Lemma static_refresh_correct {var} n : @static_refresh var n = M.refresh n.
Proof. unfold static_refresh. rewrite indices_correct. reflexivity. Qed.

Definition Request n := Pair (M.Shares (S n))
  (Pair (M.Shares (S n)) (Pair (M.Masks (S n)) (M.Shares n))).
Definition Response n := Pair (M.Shares (S n))
  (Pair (M.Shares (S n)) (Pair (M.Shares (S n)) (M.Shares (S n)))).

Definition primitives {var} n : fn var (Request n) (Response n) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let b := #p .2 .1 in
    let matrix := #p .2 .2 .1 in let coins := #p .2 .2 .2 in
    let sum := {M.share_map Core.Add (S n)} ((#a,#b)) in
    let difference := {M.share_map Core.Sub (S n)} ((#a,#b)) in
    let product := {M.multiply (S n)} ((#a,(#b,#matrix))) in
    let refreshed := {M.refresh n} ((#a,#coins)) in
    return (#sum,(#difference,(#product,#refreshed))))).

Lemma primitives_interp n a b matrix coins :
  fn.interp (primitives n) (a,(b,(matrix,coins))) =
  (fn.interp (M.share_map Core.Add (S n)) (a,b),
   (fn.interp (M.share_map Core.Sub (S n)) (a,b),
    (fn.interp (M.multiply (S n)) (a,(b,matrix)), fn.interp (M.refresh n) (a,coins)))).
Proof. reflexivity. Qed.

Definition static_primitives {var} n : fn var (Request n) (Response n) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let b := #p .2 .1 in
    let matrix := #p .2 .2 .1 in let coins := #p .2 .2 .2 in
    let sum := {static_map Core.Add (S n)} ((#a,#b)) in
    let difference := {static_map Core.Sub (S n)} ((#a,#b)) in
    let product := {static_multiply (S n)} ((#a,(#b,#matrix))) in
    let refreshed := {static_refresh n} ((#a,#coins)) in
    return (#sum,(#difference,(#product,#refreshed))))).

Lemma static_primitives_correct {var} n : @static_primitives var n = primitives n.
Proof.
  unfold static_primitives.
  rewrite !static_map_correct static_multiply_correct static_refresh_correct. reflexivity.
Qed.

Ltac2 Type counter := { mutable names : ident list }.
Ltac2 rec name_functions counter c :=
  let c := Constr.Unsafe.map (name_functions counter) c in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App head args =>
    if Constr.equal head '(@fn.Fn) then
      let used := counter.(names) in
      let name := Fresh.fresh (Fresh.Free.of_ids used) @quartz_helper in
      counter.(names) := name :: counter.(names);
      let ty := Constr.Unsafe.make (Constr.Unsafe.App '(@fn.fn)
        [| Array.get args 0; Array.get args 1; Array.get args 2 |]) in
      let binder := Constr.Binder.unsafe_make (Some name) Constr.Binder.Relevant ty in
      Constr.Unsafe.make (Constr.Unsafe.LetIn binder c (Constr.Unsafe.make (Constr.Unsafe.Rel 1)))
    else c
  | _ => c
  end.

(* Word constants stay symbolic while all function applications receive static names. *)
Definition specialized2 {var} : fn var (Request 1) (Response 1) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta
      -[Zmod.of_Z M.index_bits M.index_width] in (@static_primitives var 1) in
    let c := name_functions { names := [] } c in exact $c).

Lemma specialized2_correct :
  fn.interp (@specialized2 type.interp) = fn.interp (@primitives type.interp 1).
Proof. rewrite <- static_primitives_correct. reflexivity. Qed.

Definition packaged2 {var : type -> Type} {func : type -> type -> Type} :
    fns.fns var func (Request 1) (Response 1) :=
  fns.package_global_fns'' var func (@specialized2).

Lemma packaged2_correct :
  fns.interp (@packaged2 type.interp type.interpfn) = fn.interp (@primitives type.interp 1).
Proof. rewrite <- specialized2_correct. reflexivity. Qed.

Definition safe_hint (name : string) :=
  if String.eqb (sv.valid_ident name) EmptyString then name else "v".

Fixpoint safe_locals {var func t} (e : Syntax.eexpr.eexpr var func t) : Syntax.eexpr.eexpr var func t :=
  match e with
  | @Syntax.eexpr.Ret _ _ _ e => Syntax.eexpr.Ret e
  | @Syntax.eexpr.Let _ _ name _ e _ k => Syntax.eexpr.Let (safe_hint name) e (fun x => safe_locals (k x))
  | @Syntax.eexpr.Bind _ _ name _ e _ k =>
      Syntax.eexpr.Bind (safe_hint name) (safe_locals e) (fun x => safe_locals (k x))
  | @Syntax.eexpr.If _ _ _ b l r => Syntax.eexpr.If b (safe_locals l) (safe_locals r)
  | @Syntax.eexpr.Case _ _ _ _ e _ l r =>
      Syntax.eexpr.Case e (fun x => safe_locals (l x)) (fun x => safe_locals (r x))
  | @Syntax.eexpr.Upd _ _ _ i _ s v => Syntax.eexpr.Upd i s v
  end.

Lemma safe_locals_correct t (e : Syntax.eexpr.eexpr type.interp type.interpfn t) :
  Syntax.eexpr.interp (safe_locals e) = Syntax.eexpr.interp e.
Proof.
  induction e; cbn [safe_locals Syntax.eexpr.interp Syntax.eexpr.LetBlock]; try reflexivity.
  - apply H.
  - rewrite IHe. apply H.
  - match goal with |- context [if ?b then _ else _] => destruct b; assumption end.
  - match goal with |- context [match ?v with inl _ => _ | inr _ => _ end] =>
      destruct v; [apply H|apply H0] end.
Qed.

Fixpoint safe_names {var func a b} (fs : fns.fns var func a b) : fns.fns var func a b :=
  match fs with
  | @fns.Let _ _ _ _ _ _ name arg body rest =>
      fns.Let name (safe_hint arg) (fun x => safe_locals (body x)) (fun f => safe_names (rest f))
  | @fns.Ret _ _ _ _ name arg body => fns.Ret name (safe_hint arg) (fun x => safe_locals (body x))
  end.

Definition native2 {var : type -> Type} {func : type -> type -> Type} :=
  safe_names (@packaged2 var func).

Theorem native2_correct :
  fns.interp (@native2 type.interp type.interpfn) = fn.interp (@primitives type.interp 1).
Proof. rewrite <- packaged2_correct. reflexivity. Qed.

Definition specialized4 {var} : fn var (Request 3) (Response 3) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta
      -[Zmod.of_Z M.index_bits M.index_width] in (@static_primitives var 3) in
    let c := name_functions { names := [] } c in exact $c).

Lemma specialized4_correct :
  fn.interp (@specialized4 type.interp) = fn.interp (@primitives type.interp 3).
Proof. rewrite <- static_primitives_correct. reflexivity. Qed.

Definition packaged4 {var : type -> Type} {func : type -> type -> Type} :
    fns.fns var func (Request 3) (Response 3) :=
  fns.package_global_fns'' var func (@specialized4).

Lemma packaged4_correct :
  fns.interp (@packaged4 type.interp type.interpfn) = fn.interp (@primitives type.interp 3).
Proof. rewrite <- specialized4_correct. reflexivity. Qed.

Definition native4 {var : type -> Type} {func : type -> type -> Type} :=
  safe_names (@packaged4 var func).

Theorem native4_correct :
  fns.interp (@native4 type.interp type.interpfn) = fn.interp (@primitives type.interp 3).
Proof. rewrite <- packaged4_correct. reflexivity. Qed.

End MaskedArithmeticRTL.

Print Assumptions MaskedArithmeticRTL.indices_correct.
Print Assumptions MaskedArithmeticRTL.pairs_correct.
Print Assumptions MaskedArithmeticRTL.static_primitives_correct.
Print Assumptions MaskedArithmeticRTL.safe_locals_correct.
Print Assumptions MaskedArithmeticRTL.native2_correct.
Print Assumptions MaskedArithmeticRTL.native4_correct.
