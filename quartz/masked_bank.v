From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import masked_arithmetic.
From Masking Require Import arithmetic_bank_refresh shared_ladder.
From Stdlib Require Import ZArith Bits Vector.

Module MaskedBank.
Module M := MaskedArithmetic.
Import fn type InterfaceExample.QStdlib SharedLadder.
Import (notations) eexpr expr.
Local Open Scope string_scope.

Definition Bank n groups := Array (M.Shares (S n)) groups.
Definition Coins n groups := Array (M.Shares n) groups.

Definition get {var} t groups (i : 'I_groups) : fn var (Array t groups) t :=
  Fn (fun a => quartz_eexpr:(
    let i := $(expr.Const (t := Bits (M.index_width groups)) (M.index_bits groups i)) in
    return #a[#i])).

Definition put {var} t groups (i : 'I_groups) : fn var (Pair (Array t groups) t) (Array t groups) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in
    let i := $(expr.Const (t := Bits (M.index_width groups)) (M.index_bits groups i)) in
    let a <- #a[#i] = #p .2 in return #a)).

Lemma get_interp t groups i a :
  fn.interp (get t groups i) a = @M.read t groups a (val i).
Proof.
  change (@M.read t groups a (Z.to_nat (Zmod.unsigned (M.index_bits groups i))) =
    @M.read t groups a (val i)).
  by rewrite M.index_unsigned Nat2Z.id.
Qed.

Lemma put_interp t groups i a x :
  fn.interp (put t groups i) (a,x) = domain.Vector.upd a (val i) (fun _ => x).
Proof.
  change (domain.Vector.upd a (Z.to_nat (Zmod.unsigned (M.index_bits groups i))) (fun _ => x) =
    domain.Vector.upd a (val i) (fun _ => x)).
  by rewrite M.index_unsigned Nat2Z.id.
Qed.

Local Opaque get put M.refresh.

Fixpoint refresh_steps {var} n groups (indices : seq 'I_groups) :
    fn var (Pair (Bank n groups) (Pair (Coins n groups) (Bank n groups))) (Bank n groups) :=
  match indices with
  | List.nil => Fn (fun p => quartz_eexpr:(return #p .2 .2))
  | i :: rest => Fn (fun p => quartz_eexpr:(
      let a := #p .1 in let r := #p .2 .1 in let c := #p .2 .2 in
      let x := {get (M.Shares (S n)) groups i} (#a) in
      let coins := {get (M.Shares n) groups i} (#r) in
      let x := {M.refresh n} ((#x,#coins)) in
      let c := {put (M.Shares (S n)) groups i} ((#c,#x)) in
      let result := {refresh_steps n groups rest} ((#a,(#r,#c))) in
      return #result))
  end.

Definition refresh {var} n groups : fn var (Pair (Bank n groups) (Coins n groups)) (Bank n groups) :=
  Fn (fun p => quartz_eexpr:(
    let result := {refresh_steps n groups (enum 'I_groups)} ((#p .1,(#p .2,#p .1))) in
    return #result)).

Lemma refresh_steps_interp n groups indices a r c :
  fn.interp (refresh_steps n groups indices) (a,(r,c)) =
  foldl (fun acc i => domain.Vector.upd acc (val i)
    (fun _ => fn.interp (M.refresh n)
      (@M.read (M.Shares (S n)) groups a (val i), @M.read (M.Shares n) groups r (val i)))) c indices.
Proof.
  revert c. induction indices as [|i rest IH]; intro c; [reflexivity|].
  change (fn.interp (refresh_steps n groups rest)
    (a,(r,fn.interp (put (M.Shares (S n)) groups i)
      (c,fn.interp (M.refresh n)
        (fn.interp (get (M.Shares (S n)) groups i) a,
         fn.interp (get (M.Shares n) groups i) r)))) =
    foldl (fun acc j => domain.Vector.upd acc (val j)
      (fun _ => fn.interp (M.refresh n)
        (@M.read (M.Shares (S n)) groups a (val j), @M.read (M.Shares n) groups r (val j))))
      c (i :: rest)).
  rewrite !get_interp put_interp. apply IH.
Qed.

Lemma refresh_steps_read n groups indices a r c (j : 'I_groups) :
  @M.read (M.Shares (S n)) groups
    (fn.interp (refresh_steps n groups indices) (a,(r,c))) (val j) =
  if j \in indices then fn.interp (M.refresh n)
    (@M.read (M.Shares (S n)) groups a (val j), @M.read (M.Shares n) groups r (val j))
  else @M.read (M.Shares (S n)) groups c (val j).
Proof.
  rewrite refresh_steps_interp. revert c.
  induction indices as [|i rest IH]; intro c; [reflexivity|].
  simpl foldl. rewrite IH in_cons.
  case Hrest: (j \in rest); simpl; [by rewrite orbT|].
  have Hj : Nat.lt (val j) groups := elimT ltP (ltn_ord j).
  rewrite orbF (M.read_upd _ _ _ _ Hj).
  case E: (j == i).
  - move/eqP: E => ->. rewrite Nat.eqb_refl. reflexivity.
  - have Hneq : Nat.eqb (val j) (val i) = false.
    { apply Nat.eqb_neq. intro H. have Hij : j = i := val_inj H.
      subst i. rewrite eqxx in E. discriminate. }
    rewrite Hneq. reflexivity.
Qed.

Theorem refresh_read n groups a r (j : 'I_groups) :
  @M.read (M.Shares (S n)) groups (fn.interp (refresh n groups) (a,r)) (val j) =
  fn.interp (M.refresh n)
    (@M.read (M.Shares (S n)) groups a (val j), @M.read (M.Shares n) groups r (val j)).
Proof.
  change (@M.read (M.Shares (S n)) groups
    (fn.interp (refresh_steps n groups (enum 'I_groups)) (a,(r,a))) (val j) =
    fn.interp (M.refresh n)
      (@M.read (M.Shares (S n)) groups a (val j), @M.read (M.Shares n) groups r (val j))).
  by rewrite refresh_steps_read mem_enum.
Qed.
Definition decode n groups (a : type.interp (Bank n groups)) :=
  [ffun i : 'I_groups => M.decode (S n) (@M.read (M.Shares (S n)) groups a (val i))].

Definition decode_coins n groups (r : type.interp (Coins n groups)) :=
  [ffun i : 'I_groups => M.decode n (@M.read (M.Shares n) groups r (val i))].

Theorem refresh_refines n groups a r :
  decode n groups (fn.interp (refresh n groups) (a,r)) =
  ArithmeticBankRefresh.refresh (decode n groups a) (decode_coins n groups r).
Proof.
  apply/ffunP => i.
  rewrite /decode /decode_coins /ArithmeticBankRefresh.refresh !ffunE refresh_read.
  exact: M.refresh_refines.
Qed.

Definition canonical n groups (a : type.interp (Bank n groups)) :=
  forall i : 'I_groups, M.canonical (S n) (@M.read (M.Shares (S n)) groups a (val i)).

Theorem refresh_canonical n groups a r :
  canonical n groups a -> canonical n groups (fn.interp (refresh n groups) (a,r)).
Proof.
  move=> Ha i. rewrite refresh_read. apply M.refresh_canonical. exact: Ha.
Qed.
End MaskedBank.
Print Assumptions MaskedBank.refresh_read.
Print Assumptions MaskedBank.refresh_refines.
Print Assumptions MaskedBank.refresh_canonical.
