From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax transform pp sv.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import masked_arithmetic masked_arithmetic_rtl_export.
From Masking Require Import arithmetic_shares.
From mathcomp Require Import boot.
From Stdlib Require Import ZArith Bits List String NArith HexString.
Import fn Syntax.type InterfaceExample.QStdlib.
Import (coercions) domain.Zmod.
Import (notations) Syntax.eexpr Syntax.expr.
Local Open Scope string_scope.
Set Default Timeout 10.

Module RuntimePair.
Module M := MaskedArithmetic.
Module Core := M.Core.
Definition Index k := Bits (M.index_width k).
Definition Input k := Pair (Index k) (Pair (Index k) (M.PairInput k)).

Definition body {var func} k
    (add sub mul : func (Pair M.Word M.Word) M.Word)
    (p : var (Input k)) : Syntax.eexpr.eexpr var func (M.Shares k) :=
  quartz_eexpr:(
    let i := #p .1 in let j := #p .2 .1 in let data := #p .2 .2 in
    let a := #data .1 in let b := #data .2 .1 in
    let c := #data .2 .2 .1 in let r := #data .2 .2 .2 in
    let ai := #a[#i] in let aj := #a[#j] in
    let bi := #b[#i] in let bj := #b[#j] in
    let u := {mul} ((#ai,#bj)) in let v := {mul} ((#aj,#bi)) in
    let cross := {add} ((#u,#v)) in let masked := {add} ((#r,#cross)) in
    let ci := #c[#i] in let ci := {sub} ((#ci,#r)) in
    let c <- #c[#i] = #ci in
    let cj := #c[#j] in let cj := {add} ((#cj,#masked)) in
    let c <- #c[#j] = #cj in return #c).

Definition helper {var} k : fn var (Input k) (M.Shares k) :=
  Fn (body k (Core.arithmetic Core.Add) (Core.arithmetic Core.Sub) (Core.arithmetic Core.Mul)).

Local Opaque Core.arithmetic.

Definition result k (i j : bits (M.index_width k)) a b c r :=
  let ii := Z.to_nat (Zmod.unsigned i) in
  let jj := Z.to_nat (Zmod.unsigned j) in
  let cross := fn.interp (Core.arithmetic Core.Add)
    (fn.interp (Core.arithmetic Core.Mul) (@M.read M.Word k a ii,@M.read M.Word k b jj),
     fn.interp (Core.arithmetic Core.Mul) (@M.read M.Word k a jj,@M.read M.Word k b ii)) in
  let masked := fn.interp (Core.arithmetic Core.Add) (r,cross) in
  let ci := fn.interp (Core.arithmetic Core.Sub) (@M.read M.Word k c ii,r) in
  let c := domain.Vector.upd c ii (fun _ => ci) in
  let cj := fn.interp (Core.arithmetic Core.Add) (@M.read M.Word k c jj,masked) in
  domain.Vector.upd c jj (fun _ => cj).

Lemma body_interp k i j a b c r :
  Syntax.eexpr.interp (body k (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub)) (fn.interp (Core.arithmetic Core.Mul))
    (i,(j,(a,(b,(c,r)))))) = result k i j a b c r.
Proof. reflexivity. Qed.

Lemma helper_interp k i j a b c r :
  fn.interp (helper k) (i,(j,(a,(b,(c,r))))) = result k i j a b c r.
Proof. reflexivity. Qed.

Lemma result_indices k (i j : 'I_k) a b c r :
  result k (M.index_bits k i) (M.index_bits k j) a b c r =
  M.pair_result k i j a b c r.
Proof.
  unfold result, M.pair_result.
  rewrite !M.index_unsigned !Nat2Z.id !M.get_interp !M.put_interp.
  reflexivity.
Qed.

Theorem helper_correct k (i j : 'I_k) a b c r :
  fn.interp (helper k) (M.index_bits k i,(M.index_bits k j,(a,(b,(c,r))))) =
  fn.interp (M.pair_update k i j) (a,(b,(c,r))).
Proof. rewrite helper_interp result_indices M.pair_update_interp. reflexivity. Qed.

Corollary helper_alias k (i : 'I_k) a b c r :
  fn.interp (helper k) (M.index_bits k i,(M.index_bits k i,(a,(b,(c,r))))) =
  fn.interp (M.pair_update k i i) (a,(b,(c,r))).
Proof. apply helper_correct. Qed.

Fixpoint steps {var func} k (pairs : list ('I_k * 'I_k))
    (update : func (Input k) (M.Shares k))
    (a b c : var (M.Shares k)) (r : var (M.Masks k)) :
    Syntax.eexpr.eexpr var func (M.Shares k) :=
  match pairs with
  | nil => quartz_eexpr:(return #c)
  | (i,j) :: rest => eexpr.Bind "next" (quartz_eexpr:(
      let ii := $(expr.Const (t := Index k) (M.index_bits k i)) in
      let jj := $(expr.Const (t := Index k) (M.index_bits k j)) in
      let row := #r[#ii] in let mask := #row[#jj] in
      let c := {update} ((#ii,(#jj,(#a,(#b,(#c,#mask)))))) in
      return #c)) (fun next => steps k rest update a b next r)
  end.

Definition MulRequest k := Pair (M.Shares k) (Pair (M.Shares k) (M.Masks k)).

Fixpoint diagonal_steps {var func} k (indices : list 'I_k)
    (mul : func (Pair M.Word M.Word) M.Word)
    (a b c : var (M.Shares k)) : Syntax.eexpr.eexpr var func (M.Shares k) :=
  match indices with
  | nil => quartz_eexpr:(return #c)
  | i :: rest => eexpr.Bind "next" (quartz_eexpr:(
      let ii := $(expr.Const (t := Index k) (M.index_bits k i)) in
      let x := #a[#ii] in let y := #b[#ii] in
      let w := {mul} ((#x,#y)) in
      let c <- #c[#ii] = #w in
      return #c)) (fun next => diagonal_steps k rest mul a b next)
  end.

Definition diagonal_body {var func} k
    (mul : func (Pair M.Word M.Word) M.Word)
    (p : var (Pair (M.Shares k) (M.Shares k))) :=
  eexpr.Let "a" (quartz_expr:(#p .1)) (fun a =>
  eexpr.Let "b" (quartz_expr:(#p .2)) (fun b =>
  eexpr.Let "c" (expr.Const (t := M.Shares k) (type.default (M.Shares k))) (fun c =>
    diagonal_steps k (enum 'I_k) mul a b c))).

Lemma map_steps_correct op k indices a b c :
  Syntax.eexpr.interp (diagonal_steps k indices
    (fn.interp (Core.arithmetic op)) a b c) =
  fn.interp (M.map_steps op k indices) (a,(b,c)).
Proof.
  rewrite M.map_steps_interp.
  induction indices as [|i rest IH] in c |- *.
  - reflexivity.
  - change (Syntax.eexpr.interp (diagonal_steps k rest
      (fn.interp (Core.arithmetic op)) a b
      (domain.Vector.upd c (Z.to_nat (Zmod.unsigned (M.index_bits k i)))
        (fun _ => fn.interp (Core.arithmetic op)
          (@M.read M.Word k a (Z.to_nat (Zmod.unsigned (M.index_bits k i))),
           @M.read M.Word k b (Z.to_nat (Zmod.unsigned (M.index_bits k i))))))) =
      foldl (fun acc j => domain.Vector.upd acc (val j)
        (fun _ => fn.interp (Core.arithmetic op)
          (@M.read M.Word k a (val j), @M.read M.Word k b (val j)))) c (i :: rest)).
    rewrite !M.index_unsigned !Nat2Z.id.
    apply IH.
Qed.

Lemma map_body_correct op k a b :
  Syntax.eexpr.interp (diagonal_body k (fn.interp (Core.arithmetic op)) (a,b)) =
  fn.interp (M.share_map op k) (a,b).
Proof. apply map_steps_correct. Qed.

Corollary diagonal_steps_correct k indices a b c :
  Syntax.eexpr.interp (diagonal_steps k indices
    (fn.interp (Core.arithmetic Core.Mul)) a b c) =
  fn.interp (M.map_steps Core.Mul k indices) (a,(b,c)).
Proof. apply map_steps_correct. Qed.

Corollary diagonal_body_correct k a b :
  Syntax.eexpr.interp (diagonal_body k (fn.interp (Core.arithmetic Core.Mul)) (a,b)) =
  fn.interp (M.share_map Core.Mul k) (a,b).
Proof. apply map_body_correct. Qed.

Definition multiply_body {var func} k
    (diagonal : func (Pair (M.Shares k) (M.Shares k)) (M.Shares k))
    (update : func (Input k) (M.Shares k)) (p : var (MulRequest k)) :=
  eexpr.Let "a" (quartz_expr:(#p .1)) (fun a =>
  eexpr.Let "b" (quartz_expr:(#p .2 .1)) (fun b =>
  eexpr.Let "r" (quartz_expr:(#p .2 .2)) (fun r =>
  eexpr.Let "c" (quartz_expr:({diagonal} ((#a,#b)))) (fun c =>
    steps k (ArithmeticShares.pair_order k) update a b c r)))).

(* Arithmetic and diagonal helpers are supplied by the enclosing library. *)
Definition with_multiply {var func outin outout} k
    (add sub mul : func (Pair M.Word M.Word) M.Word)
    (diagonal : func (Pair (M.Shares k) (M.Shares k)) (M.Shares k))
    (continuation : func (MulRequest k) (M.Shares k) ->
      fns.fns var func outin outout) : fns.fns var func outin outout :=
  fns.Let "runtime_pair" "request" (body k add sub mul) (fun update =>
    fns.Let "masked_multiply" "request" (multiply_body k diagonal update) continuation).

Definition with_arithmetic {var func outin outout} k
    (add sub mul : func (Pair M.Word M.Word) M.Word)
    (continuation : func (MulRequest k) (M.Shares k) ->
      fns.fns var func outin outout) : fns.fns var func outin outout :=
  fns.Let "masked_diagonal" "request" (diagonal_body k mul) (fun diagonal =>
    with_multiply k add sub mul diagonal continuation).

Fixpoint ordered_result k (pairs : list ('I_k * 'I_k)) a b r c :=
  match pairs with
  | nil => c
  | (i,j) :: rest => ordered_result k rest a b r
      (M.pair_result k i j a b c
        (@M.read M.Word k (@M.read (M.Shares k) k r (val i)) (val j)))
  end.

Lemma steps_interp k pairs a b c r :
  Syntax.eexpr.interp (steps k pairs (fn.interp (helper k)) a b c r) =
  ordered_result k pairs a b r c.
Proof.
  induction pairs as [| [i j] rest IH] in c |- *.
  - reflexivity.
  - change (Syntax.eexpr.interp (steps k rest (fn.interp (helper k)) a b
      (fn.interp (helper k) (M.index_bits k i,(M.index_bits k j,
        (a,(b,(c,@M.read M.Word k
          (@M.read (M.Shares k) k r (Z.to_nat (Zmod.unsigned (M.index_bits k i))))
          (Z.to_nat (Zmod.unsigned (M.index_bits k j))))))))) r) =
      ordered_result k ((i,j) :: rest) a b r c).
    rewrite helper_interp result_indices !M.index_unsigned !Nat2Z.id.
    apply IH.
Qed.

Lemma ordered_result_correct k pairs a b r c :
  ordered_result k pairs a b r c =
  fn.interp (M.multiply_steps k pairs) (a,(b,(r,c))).
Proof.
  induction pairs as [| [i j] rest IH] in c |- *.
  - reflexivity.
  - change (ordered_result k rest a b r
      (M.pair_result k i j a b c
        (@M.read M.Word k (@M.read (M.Shares k) k r (val i)) (val j))) =
      fn.interp (M.multiply_steps k rest)
        (a,(b,(r,fn.interp (M.pair_update k i j)
          (a,(b,(c,fn.interp (M.get_mask k (i,j)) r))))))).
    rewrite M.get_mask_interp M.pair_update_interp.
    apply IH.
Qed.

Theorem multiply_body_correct k a b r :
  Syntax.eexpr.interp (multiply_body k
    (fn.interp (M.share_map Core.Mul k)) (fn.interp (helper k)) (a,(b,r))) =
  fn.interp (M.multiply k) (a,(b,r)).
Proof.
  change (Syntax.eexpr.interp (steps k (ArithmeticShares.pair_order k)
    (fn.interp (helper k)) a b (fn.interp (M.share_map Core.Mul k) (a,b)) r) =
    fn.interp (M.multiply_steps k (ArithmeticShares.pair_order k))
      (a,(b,(r,fn.interp (M.share_map Core.Mul k) (a,b))))).
  rewrite steps_interp. apply ordered_result_correct.
Qed.

Definition library {var func} k
    (add sub mul : func (Pair M.Word M.Word) M.Word)
    (diagonal : func (Pair (M.Shares k) (M.Shares k)) (M.Shares k)) :
    fns.fns var func (MulRequest k) (M.Shares k) :=
  with_multiply k add sub mul diagonal (fun multiply =>
    fns.Ret "entry" "request" (fun p => quartz_eexpr:(return {multiply} (#p)))).

Theorem library_correct k a b r :
  fns.interp (library k (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub)) (fn.interp (Core.arithmetic Core.Mul))
    (fn.interp (M.share_map Core.Mul k))) (a,(b,r)) =
  fn.interp (M.multiply k) (a,(b,r)).
Proof. exact (multiply_body_correct k a b r). Qed.

Definition arithmetic_library {var func} k
    (add sub mul : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (MulRequest k) (M.Shares k) :=
  with_arithmetic k add sub mul (fun multiply =>
    fns.Ret "entry" "request" (fun p => quartz_eexpr:(return {multiply} (#p)))).

Theorem arithmetic_library_correct k a b r :
  fns.interp (arithmetic_library k (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub)) (fn.interp (Core.arithmetic Core.Mul)))
      (a,(b,r)) = fn.interp (M.multiply k) (a,(b,r)).
Proof.
  change (Syntax.eexpr.interp (steps k (ArithmeticShares.pair_order k)
    (fn.interp (helper k)) a b
    (Syntax.eexpr.interp (diagonal_body k (fn.interp (Core.arithmetic Core.Mul)) (a,b))) r) =
    fn.interp (M.multiply k) (a,(b,r))).
  rewrite diagonal_body_correct steps_interp ordered_result_correct.
  reflexivity.
Qed.

End RuntimePair.
Print Assumptions RuntimePair.helper_correct.
Print Assumptions RuntimePair.helper_alias.
Print Assumptions RuntimePair.library_correct.
Print Assumptions RuntimePair.arithmetic_library_correct.

Module RuntimeRefresh.
Module M := MaskedArithmetic.
Module Core := M.Core.
Definition Request n := Pair (M.Shares (S n)) (M.Shares n).

Fixpoint anchor {var func} n (indices : list 'I_n)
    (sub : func (Pair M.Word M.Word) M.Word)
    (h : var M.Word) (r : var (M.Shares n)) : eexpr.eexpr var func M.Word :=
  match indices with
  | nil => quartz_eexpr:(return #h)
  | i :: rest => eexpr.Bind "head" (quartz_eexpr:(
      let ii := $(expr.Const (t := Bits (M.index_width n)) (M.index_bits n i)) in
      let coin := #r[#ii] in return {sub} ((#h,#coin))))
      (fun next => anchor n rest sub next r)
  end.

Fixpoint tail {var func} n (indices : list 'I_n)
    (add : func (Pair M.Word M.Word) M.Word)
    (a c : var (M.Shares (S n))) (r : var (M.Shares n)) :
    eexpr.eexpr var func (M.Shares (S n)) :=
  match indices with
  | nil => quartz_eexpr:(return #c)
  | i :: rest => eexpr.Bind "tail" (quartz_eexpr:(
      let ii := $(expr.Const (t := Bits (M.index_width n)) (M.index_bits n i)) in
      let jj := $(expr.Const (t := Bits (M.index_width (S n)))
        (M.index_bits (S n) (lift ord0 i))) in
      let x := #a[#jj] in let coin := #r[#ii] in
      let w := {add} ((#x,#coin)) in
      let c <- #c[#jj] = #w in return #c))
      (fun next => tail n rest add a next r)
  end.

Definition body {var func} n
    (add sub : func (Pair M.Word M.Word) M.Word) (p : var (Request n)) :=
  eexpr.Let "a" (quartz_expr:(#p .1)) (fun a =>
  eexpr.Let "r" (quartz_expr:(#p .2)) (fun r =>
  eexpr.Let "zero" (expr.Const (t := Bits (M.index_width (S n)))
    (M.index_bits (S n) ord0)) (fun zero =>
  eexpr.Let "head" (quartz_expr:(#a[#zero])) (fun h =>
  eexpr.Bind "head" (anchor n (enum 'I_n) sub h r) (fun head =>
  eexpr.Bind "tail" (tail n (enum 'I_n) add a a r) (fun c =>
    quartz_eexpr:(let c <- #c[#zero] = #head in return #c))))))).

Definition library {var func} n
    (add sub : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (Request n) (M.Shares (S n)) :=
  fns.Ret "masked_refresh" "request" (body n add sub).

Local Opaque Core.arithmetic.
Local Opaque M.index_bits M.index_width M.get M.put.

Lemma anchor_correct n indices h r :
  eexpr.interp (anchor n indices (fn.interp (Core.arithmetic Core.Sub)) h r) =
  fn.interp (M.refresh_anchor n indices) (h,r).
Proof.
  unfold M.refresh_anchor.
  generalize (@Core.arithmetic type.interp Core.Sub) as subtract.
  intro subtract.
  induction indices as [|i rest IH] in h |- *.
  - reflexivity.
  - rewrite M.anchor_steps_cons M.get_interp.
    cbn [anchor eexpr.interp eexpr.LetBlock expr.interp expr.tt
      binop.interp typeWithHole.get].
    rewrite M.index_unsigned Nat2Z.id.
    apply IH.
Qed.

Lemma tail_correct n indices a c r :
  eexpr.interp (tail n indices (fn.interp (Core.arithmetic Core.Add)) a c r) =
  fn.interp (M.refresh_tail n indices) (a,(r,c)).
Proof.
  induction indices as [|i rest IH] in c |- *.
  - unfold M.refresh_tail. reflexivity.
  - rewrite M.refresh_tail_cons !M.get_interp M.put_interp.
    cbn [tail eexpr.interp eexpr.LetBlock expr.interp expr.tt
      binop.interp typeWithHole.get typeWithHole.upd].
    rewrite !M.index_unsigned !Nat2Z.id.
    apply IH.
Qed.

Theorem library_correct n a r :
  fns.interp (library n (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub))) (a,r) =
  fn.interp (M.refresh n) (a,r).
Proof.
  cbn [library fns.interp body eexpr.interp eexpr.LetBlock expr.interp expr.tt
    binop.interp typeWithHole.get typeWithHole.upd].
  rewrite tail_correct anchor_correct !M.index_unsigned !Nat2Z.id.
  change (domain.Vector.upd
    (fn.interp (M.refresh_tail n (enum 'I_n)) (a,(r,a))) (val (@ord0 n))
    (fun _ => fn.interp (M.refresh_anchor n (enum 'I_n))
      (@M.read M.Word (S n) a (val (@ord0 n)),r)) =
    fn.interp (M.put (S n) ord0)
      (fn.interp (M.refresh_tail n (enum 'I_n)) (a,(r,a)),
       fn.interp (M.refresh_anchor n (enum 'I_n))
         (fn.interp (M.get (S n) ord0) a,r))).
  rewrite M.put_interp M.get_interp. reflexivity.
Qed.

End RuntimeRefresh.
Print Assumptions RuntimeRefresh.library_correct.

Module RuntimeStaticLibraries.
Module P := RuntimePair.
Module RR := RuntimeRefresh.
Module A := MaskedArithmeticRTL.
Module M := P.M.
Module Core := M.Core.

Definition diagonal_body {var func} k
    (mul : func (Pair M.Word M.Word) M.Word)
    (p : var (Pair (M.Shares k) (M.Shares k))) :=
  eexpr.Let "a" (quartz_expr:(#p .1)) (fun a =>
  eexpr.Let "b" (quartz_expr:(#p .2)) (fun b =>
  eexpr.Let "c" (expr.Const (t := M.Shares k) (type.default (M.Shares k))) (fun c =>
    P.diagonal_steps k (A.indices k) mul a b c))).

Definition multiply_body {var func} k
    (diagonal : func (Pair (M.Shares k) (M.Shares k)) (M.Shares k))
    (update : func (P.Input k) (M.Shares k)) (p : var (P.MulRequest k)) :=
  eexpr.Let "a" (quartz_expr:(#p .1)) (fun a =>
  eexpr.Let "b" (quartz_expr:(#p .2 .1)) (fun b =>
  eexpr.Let "r" (quartz_expr:(#p .2 .2)) (fun r =>
  eexpr.Let "c" (quartz_expr:({diagonal} ((#a,#b)))) (fun c =>
    P.steps k (A.pairs k) update a b c r)))).

Definition arithmetic_library {var func} k
    (add sub mul : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (P.MulRequest k) (M.Shares k) :=
  fns.Let "masked_diagonal" "request" (diagonal_body k mul) (fun diagonal =>
  fns.Let "runtime_pair" "request" (P.body k add sub mul) (fun update =>
  fns.Let "masked_multiply" "request" (multiply_body k diagonal update) (fun multiply =>
    fns.Ret "entry" "request" (fun p => quartz_eexpr:(return {multiply} (#p)))))).

Definition refresh_body {var func} n
    (add sub : func (Pair M.Word M.Word) M.Word) (p : var (RR.Request n)) :=
  eexpr.Let "a" (quartz_expr:(#p .1)) (fun a =>
  eexpr.Let "r" (quartz_expr:(#p .2)) (fun r =>
  eexpr.Let "zero" (expr.Const (t := Bits (M.index_width (S n)))
    (M.index_bits (S n) ord0)) (fun zero =>
  eexpr.Let "head" (quartz_expr:(#a[#zero])) (fun h =>
  eexpr.Bind "head" (RR.anchor n (A.indices n) sub h r) (fun head =>
  eexpr.Bind "tail" (RR.tail n (A.indices n) add a a r) (fun c =>
    quartz_eexpr:(let c <- #c[#zero] = #head in return #c))))))).

Definition refresh_library {var func} n
    (add sub : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (RR.Request n) (M.Shares (S n)) :=
  fns.Ret "masked_refresh" "request" (refresh_body n add sub).

Lemma diagonal_body_exact {var func} k mul :
  @diagonal_body var func k mul = @P.diagonal_body var func k mul.
Proof. unfold diagonal_body, P.diagonal_body. rewrite A.indices_correct. reflexivity. Qed.

Lemma multiply_body_exact {var func} k diagonal update :
  @multiply_body var func k diagonal update = @P.multiply_body var func k diagonal update.
Proof. unfold multiply_body, P.multiply_body. rewrite A.pairs_correct. reflexivity. Qed.

Theorem arithmetic_library_exact {var func} k add sub mul :
  @arithmetic_library var func k add sub mul = @P.arithmetic_library var func k add sub mul.
Proof.
  unfold arithmetic_library, P.arithmetic_library, P.with_arithmetic, P.with_multiply,
    diagonal_body, P.diagonal_body, multiply_body, P.multiply_body.
  rewrite A.indices_correct A.pairs_correct. reflexivity.
Qed.

Lemma refresh_body_exact {var func} n add sub :
  @refresh_body var func n add sub = @RR.body var func n add sub.
Proof. unfold refresh_body, RR.body. rewrite A.indices_correct. reflexivity. Qed.

Theorem refresh_library_exact {var func} n add sub :
  @refresh_library var func n add sub = @RR.library var func n add sub.
Proof. unfold refresh_library, RR.library. rewrite refresh_body_exact. reflexivity. Qed.

Theorem map_body_correct op k a b :
  eexpr.interp (diagonal_body k (fn.interp (Core.arithmetic op)) (a,b)) =
  fn.interp (M.share_map op k) (a,b).
Proof. rewrite diagonal_body_exact. exact (P.map_body_correct op k a b). Qed.

Theorem arithmetic_library_correct k a b r :
  fns.interp (arithmetic_library k (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub)) (fn.interp (Core.arithmetic Core.Mul))) (a,(b,r)) =
  fn.interp (M.multiply k) (a,(b,r)).
Proof. rewrite arithmetic_library_exact. exact (P.arithmetic_library_correct k a b r). Qed.

Theorem refresh_library_correct n a r :
  fns.interp (refresh_library n (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub))) (a,r) = fn.interp (M.refresh n) (a,r).
Proof. rewrite refresh_library_exact. exact (RR.library_correct n a r). Qed.

End RuntimeStaticLibraries.
Print Assumptions RuntimeStaticLibraries.arithmetic_library_exact.
Print Assumptions RuntimeStaticLibraries.refresh_library_exact.
Print Assumptions RuntimeStaticLibraries.arithmetic_library_correct.
Print Assumptions RuntimeStaticLibraries.refresh_library_correct.

Module RuntimeSafeLibraries.
Module P := RuntimePair.
Module RR := RuntimeRefresh.
Module S := RuntimeStaticLibraries.
Module A := MaskedArithmeticRTL.
Module M := P.M.
Module Core := M.Core.

Local Opaque Core.arithmetic M.index_bits M.index_width type.default.

Lemma pair_body_correct k add sub mul
    (Ha : forall p, add p = fn.interp (Core.arithmetic Core.Add) p)
    (Hs : forall p, sub p = fn.interp (Core.arithmetic Core.Sub) p)
    (Hm : forall p, mul p = fn.interp (Core.arithmetic Core.Mul) p) p :
  eexpr.interp (P.body k add sub mul p) = fn.interp (P.helper k) p.
Proof.
  destruct p as [i [j [a [b [c r]]]]].
  cbn [P.body eexpr.interp eexpr.LetBlock expr.interp].
  rewrite !Ha !Hs !Hm. reflexivity.
Qed.

Lemma pair_steps_congruent k indices f g
    (H : forall p, f p = g p) a b c r :
  eexpr.interp (P.steps k indices f a b c r) =
  eexpr.interp (P.steps k indices g a b c r).
Proof.
  induction indices as [|[i j] rest IH] in c |- *.
  - reflexivity.
  - cbn [P.steps eexpr.interp eexpr.LetBlock expr.interp].
    rewrite H. apply IH.
Qed.

Lemma map_steps_congruent k indices f g
    (H : forall p, f p = g p) a b c :
  eexpr.interp (P.diagonal_steps k indices f a b c) =
  eexpr.interp (P.diagonal_steps k indices g a b c).
Proof.
  induction indices as [|i rest IH] in c |- *.
  - reflexivity.
  - cbn [P.diagonal_steps eexpr.interp eexpr.LetBlock expr.interp].
    rewrite H. apply IH.
Qed.

Definition diagonal_body {var func} k
    (op : func (Pair M.Word M.Word) M.Word)
    (p : var (Pair (M.Shares k) (M.Shares k))) :=
  A.safe_locals (S.diagonal_body k op p).

Lemma map_body_correct op k f
    (H : forall p, f p = fn.interp (Core.arithmetic op) p) p :
  eexpr.interp (diagonal_body k f p) = fn.interp (M.share_map op k) p.
Proof.
  destruct p as [a b]. unfold diagonal_body.
  rewrite A.safe_locals_correct S.diagonal_body_exact.
  transitivity (eexpr.interp (P.diagonal_body k (fn.interp (Core.arithmetic op)) (a,b))).
  - cbn [P.diagonal_body eexpr.interp eexpr.LetBlock expr.interp].
    apply map_steps_congruent. exact H.
  - exact (P.map_body_correct op k a b).
Qed.

Definition pair_body {var func} k
    (add sub mul : func (Pair M.Word M.Word) M.Word) (p : var (P.Input k)) :=
  A.safe_locals (P.body k add sub mul p).

Lemma safe_pair_body_correct k add sub mul
    (Ha : forall p, add p = fn.interp (Core.arithmetic Core.Add) p)
    (Hs : forall p, sub p = fn.interp (Core.arithmetic Core.Sub) p)
    (Hm : forall p, mul p = fn.interp (Core.arithmetic Core.Mul) p) p :
  eexpr.interp (pair_body k add sub mul p) = fn.interp (P.helper k) p.
Proof.
  unfold pair_body. rewrite A.safe_locals_correct.
  exact (pair_body_correct k add sub mul Ha Hs Hm p).
Qed.

Definition multiply_body {var func} k
    (diagonal : func (Pair (M.Shares k) (M.Shares k)) (M.Shares k))
    (update : func (P.Input k) (M.Shares k)) (p : var (P.MulRequest k)) :=
  A.safe_locals (S.multiply_body k diagonal update p).

Lemma multiply_body_correct k diagonal update
    (Hd : forall p, diagonal p = fn.interp (M.share_map Core.Mul k) p)
    (Hu : forall p, update p = fn.interp (P.helper k) p) p :
  eexpr.interp (multiply_body k diagonal update p) = fn.interp (M.multiply k) p.
Proof.
  destruct p as [a [b r]]. unfold multiply_body.
  rewrite A.safe_locals_correct S.multiply_body_exact.
  transitivity (eexpr.interp (P.multiply_body k (fn.interp (M.share_map Core.Mul k))
    (fn.interp (P.helper k)) (a,(b,r)))).
  - cbn [P.multiply_body eexpr.interp eexpr.LetBlock expr.interp].
    rewrite Hd. apply pair_steps_congruent. exact Hu.
  - exact (P.multiply_body_correct k a b r).
Qed.

Definition arithmetic_library {var func} k
    (add sub mul : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (P.MulRequest k) (M.Shares k) :=
  fns.Let "masked_diagonal" "request" (diagonal_body k mul) (fun diagonal =>
  fns.Let "runtime_pair" "request" (pair_body k add sub mul) (fun update =>
    fns.Ret "masked_multiply" "request" (multiply_body k diagonal update))).

Theorem arithmetic_library_contract k add sub mul
    (Ha : forall p, add p = fn.interp (Core.arithmetic Core.Add) p)
    (Hs : forall p, sub p = fn.interp (Core.arithmetic Core.Sub) p)
    (Hm : forall p, mul p = fn.interp (Core.arithmetic Core.Mul) p) p :
  fns.interp (arithmetic_library k add sub mul) p = fn.interp (M.multiply k) p.
Proof.
  cbn [arithmetic_library fns.interp].
  apply multiply_body_correct.
  - intro x. exact (map_body_correct Core.Mul k mul Hm x).
  - intro x. exact (safe_pair_body_correct k add sub mul Ha Hs Hm x).
Qed.

Corollary arithmetic_library_correct k a b r :
  fns.interp (arithmetic_library k (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub)) (fn.interp (Core.arithmetic Core.Mul))) (a,(b,r)) =
  fn.interp (M.multiply k) (a,(b,r)).
Proof. apply arithmetic_library_contract; intro x; reflexivity. Qed.

Lemma anchor_congruent n indices f g
    (H : forall p, f p = g p) h r :
  eexpr.interp (RR.anchor n indices f h r) = eexpr.interp (RR.anchor n indices g h r).
Proof.
  induction indices as [|i rest IH] in h |- *.
  - reflexivity.
  - cbn [RR.anchor eexpr.interp eexpr.LetBlock expr.interp]. rewrite H. apply IH.
Qed.

Lemma tail_congruent n indices f g
    (H : forall p, f p = g p) a c r :
  eexpr.interp (RR.tail n indices f a c r) = eexpr.interp (RR.tail n indices g a c r).
Proof.
  induction indices as [|i rest IH] in c |- *.
  - reflexivity.
  - cbn [RR.tail eexpr.interp eexpr.LetBlock expr.interp]. rewrite H. apply IH.
Qed.

Definition refresh_body {var func} n
    (add sub : func (Pair M.Word M.Word) M.Word) (p : var (RR.Request n)) :=
  A.safe_locals (S.refresh_body n add sub p).

Lemma refresh_body_correct n add sub
    (Ha : forall p, add p = fn.interp (Core.arithmetic Core.Add) p)
    (Hs : forall p, sub p = fn.interp (Core.arithmetic Core.Sub) p) p :
  eexpr.interp (refresh_body n add sub p) = fn.interp (M.refresh n) p.
Proof.
  destruct p as [a r]. unfold refresh_body.
  rewrite A.safe_locals_correct S.refresh_body_exact.
  transitivity (fns.interp (RR.library n (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub))) (a,r)).
  - cbn [RR.library fns.interp RR.body eexpr.interp eexpr.LetBlock expr.interp].
    rewrite (tail_congruent n _ add (fn.interp (Core.arithmetic Core.Add)) Ha).
    rewrite (anchor_congruent n _ sub (fn.interp (Core.arithmetic Core.Sub)) Hs).
    reflexivity.
  - exact (RR.library_correct n a r).
Qed.

Definition refresh_library {var func} n
    (add sub : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (RR.Request n) (M.Shares (S n)) :=
  fns.Ret "masked_refresh" "request" (refresh_body n add sub).

Theorem refresh_library_contract n add sub
    (Ha : forall p, add p = fn.interp (Core.arithmetic Core.Add) p)
    (Hs : forall p, sub p = fn.interp (Core.arithmetic Core.Sub) p) p :
  fns.interp (refresh_library n add sub) p = fn.interp (M.refresh n) p.
Proof. exact (refresh_body_correct n add sub Ha Hs p). Qed.

Corollary refresh_library_correct n a r :
  fns.interp (refresh_library n (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub))) (a,r) = fn.interp (M.refresh n) (a,r).
Proof. apply refresh_library_contract; intro x; reflexivity. Qed.

End RuntimeSafeLibraries.
Print Assumptions RuntimeSafeLibraries.arithmetic_library_contract.
Print Assumptions RuntimeSafeLibraries.refresh_library_contract.
Print Assumptions RuntimeSafeLibraries.arithmetic_library_correct.
Print Assumptions RuntimeSafeLibraries.refresh_library_correct.

Module MaskedArithmeticHierarchy.
Module A := MaskedArithmeticRTL.
Module M := A.M.
Module Core := M.Core.
Local Open Scope string_scope.

Ltac2 Type counter := { mutable used : Fresh.Free.t; mutable seed : ident }.
Ltac2 rec name_functions counter c :=
  let c := Constr.Unsafe.map (name_functions counter) c in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App head args =>
    if Constr.equal head '(@fn.Fn) then
      let used := counter.(used) in
      let seed := counter.(seed) in
      let (name, used) := Fresh.next used seed in
      counter.(used) := used;
      counter.(seed) := name;
      let ty := Constr.Unsafe.make (Constr.Unsafe.App '(@fn.fn)
        [| Array.get args 0; Array.get args 1; Array.get args 2 |]) in
      let binder := Constr.Binder.unsafe_make (Some name) Constr.Binder.Relevant ty in
      Constr.Unsafe.make (Constr.Unsafe.LetIn binder c (Constr.Unsafe.make (Constr.Unsafe.Rel 1)))
    else c
  | _ => c
  end.

Definition field_add {var} : fn var (Pair M.Word M.Word) M.Word :=
  ltac2:(let c := eval cbv beta iota zeta delta -[Zmod.of_Z] in (@Core.arithmetic var Core.Add) in
    let c := name_functions {used := Fresh.Free.empty; seed := @shared_field_add_helper} c in exact $c).
Definition field_sub {var} : fn var (Pair M.Word M.Word) M.Word :=
  ltac2:(let c := eval cbv beta iota zeta delta -[Zmod.of_Z] in (@Core.arithmetic var Core.Sub) in
    let c := name_functions {used := Fresh.Free.empty; seed := @shared_field_sub_helper} c in exact $c).
Definition field_mul {var} : fn var (Pair M.Word M.Word) M.Word :=
  ltac2:(let c := eval cbv beta iota zeta delta -[Zmod.of_Z] in (@Core.arithmetic var Core.Mul) in
    let c := name_functions {used := Fresh.Free.empty; seed := @shared_field_mul_helper} c in exact $c).

Lemma field_add_correct {var} : @field_add var = Core.arithmetic Core.Add.
Proof. reflexivity. Qed.
Lemma field_sub_correct {var} : @field_sub var = Core.arithmetic Core.Sub.
Proof. reflexivity. Qed.
Lemma field_mul_correct {var} : @field_mul var = Core.arithmetic Core.Mul.
Proof. reflexivity. Qed.

Ltac2 rec field_calls c :=
  let c := Constr.Unsafe.map field_calls c in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App head args =>
    if Constr.equal head '(@Core.arithmetic) then
      let op := Array.get args 1 in
      let v := Array.get args 0 in
      if Constr.equal op 'Core.Add then constr:(@field_add $v) else
      if Constr.equal op 'Core.Sub then constr:(@field_sub $v) else
      if Constr.equal op 'Core.Mul then constr:(@field_mul $v) else c
    else c
  | _ => c
  end.

Definition pair_update {var} k (i j : 'I_k) : fn var (M.PairInput k) (M.Shares k) :=
  ltac2:(let c := eval cbv beta iota zeta delta
    -[Zmod.of_Z M.index_bits M.index_width Core.arithmetic M.get M.put]
      in (@M.pair_update var k i j) in
    let c := field_calls c in
    let c := name_functions {used := Fresh.Free.empty; seed := @shared_pair_helper} c in exact $c).

Lemma pair_update_correct {var} k i j : @pair_update var k i j = M.pair_update k i j.
Proof. reflexivity. Qed.

Ltac2 rec pair_calls c :=
  let c := Constr.Unsafe.map pair_calls c in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App head args =>
    if Constr.equal head '(@M.pair_update) then
      let v := Array.get args 0 in
      let k := Array.get args 1 in
      let i := Array.get args 2 in
      let j := Array.get args 3 in
      constr:(@pair_update $v $k $i $j)
    else c
  | _ => c
  end.

Ltac2 hierarchical prefix c :=
  let c := field_calls c in
  let c := pair_calls c in
  let c := name_functions {used := Fresh.Free.empty; seed := prefix} c in
  c.

(* Monomorphization can clone hints; references remain bound through fns.Let. *)
Fixpoint unique_functions {var func a b} (index : N) (fs : fns.fns var func a b) :
    fns.fns var func a b :=
  match fs with
  | @fns.Let _ _ _ _ _ _ _ argument body continuation =>
      fns.Let ("quartz_shared_fn_" ++ HexString.of_Z (Z.of_N index)) argument body
        (fun f => unique_functions (N.succ index) (continuation f))
  | @fns.Ret _ _ _ _ name argument body => fns.Ret name argument body
  end.

Lemma unique_functions_correct a b (fs : fns.fns type.interp type.interpfn a b) index :
  fns.interp (unique_functions index fs) = fns.interp fs.
Proof. revert index. induction fs; intro index; cbn; auto. Qed.
End MaskedArithmeticHierarchy.

Print Assumptions MaskedArithmeticHierarchy.field_add_correct.
Print Assumptions MaskedArithmeticHierarchy.field_sub_correct.
Print Assumptions MaskedArithmeticHierarchy.field_mul_correct.
Print Assumptions MaskedArithmeticHierarchy.pair_update_correct.
Print Assumptions MaskedArithmeticHierarchy.unique_functions_correct.
