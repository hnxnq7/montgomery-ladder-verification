From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax transform pp sv.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import masked_arithmetic_native masked_controller_rtl_export
  masked_arithmetic_rtl_export masked_bank.
From mathcomp Require Import boot.
From Stdlib Require Import String ZArith Bits List.
Import Syntax.fn Syntax.type InterfaceExample.QStdlib.
Import (notations) Syntax.eexpr Syntax.expr.
Local Open Scope string_scope.
Set Default Timeout 10.

Module MaskedControllerNative.
Module R := MaskedControllerRTL.
Module C := R.C.
Module B := C.B.
Module M := C.M.
Module A := MaskedArithmeticRTL.

Fixpoint refresh_steps {var} n groups (indices : list 'I_groups) :
    fn var (Pair (B.Bank n groups) (Pair (B.Coins n groups) (B.Bank n groups)))
      (B.Bank n groups) :=
  match indices with
  | List.nil => Fn (fun p => quartz_eexpr:(return #p .2 .2))
  | i :: rest => Fn (fun p => quartz_eexpr:(
      let a := #p .1 in let r := #p .2 .1 in let c := #p .2 .2 in
      let x := {B.get (M.Shares (S n)) groups i} (#a) in
      let coins := {B.get (M.Shares n) groups i} (#r) in
      let x := {A.static_refresh n} ((#x,#coins)) in
      let c := {B.put (M.Shares (S n)) groups i} ((#c,#x)) in
      let result := {refresh_steps n groups rest} ((#a,(#r,#c))) in
      return #result))
  end.

Lemma refresh_steps_correct {var} n groups indices :
  @refresh_steps var n groups indices = B.refresh_steps n groups indices.
Proof.
  induction indices as [|i rest IH]; simpl; [reflexivity|].
  rewrite A.static_refresh_correct IH. reflexivity.
Qed.

Definition refresh {var} n groups :
    fn var (Pair (B.Bank n groups) (B.Coins n groups)) (B.Bank n groups) :=
  Fn (fun p => quartz_eexpr:(
    let result := {refresh_steps n groups (A.indices groups)} ((#p .1,(#p .2,#p .1))) in
    return #result)).

Lemma refresh_correct {var} n groups : @refresh var n groups = B.refresh n groups.
Proof. unfold refresh. rewrite refresh_steps_correct A.indices_correct. reflexivity. Qed.

Ltac2 rec static_calls c :=
  let c := Constr.Unsafe.map static_calls c in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App head args =>
    if Constr.equal head '(@M.share_map) then
      let v := Array.get args 0 in let op := Array.get args 1 in let k := Array.get args 2 in
      constr:(@A.static_map $v $op $k)
    else if Constr.equal head '(@M.multiply) then
      let v := Array.get args 0 in let k := Array.get args 1 in constr:(@A.static_multiply $v $k)
    else if Constr.equal head '(@B.refresh) then
      let v := Array.get args 0 in let n := Array.get args 1 in let k := Array.get args 2 in
      constr:(@refresh $v $n $k)
    else c
  | _ => c
  end.

(* Only finite iteration changes; all state, commands, and coins stay runtime inputs. *)
Definition cycle {var} n : fn var (C.Input n) (R.Response n) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta
      [R.cycle C.tick C.prepare C.prepare_bank C.execute] in (@R.cycle var n) in
    let c := static_calls c in exact $c).

Theorem cycle_correct {var} n : @cycle var n = R.cycle n.
Proof.
  unfold cycle.
  rewrite !A.static_map_correct A.static_multiply_correct refresh_correct.
  reflexivity.
Qed.

Theorem cycle_interp n :
  fn.interp (@cycle type.interp n) = fn.interp (@R.cycle type.interp n).
Proof. rewrite cycle_correct. reflexivity. Qed.
End MaskedControllerNative.
Print Assumptions MaskedControllerNative.cycle_correct.
Print Assumptions MaskedControllerNative.cycle_interp.

Module ControllerNativeContexts.
Module R := MaskedControllerRTL.
Module C := R.C.
Module M := C.M.
Module B := C.B.
Module Core := M.Core.

Ltac2 rec find_call replacements c :=
  match replacements with
  | [] => None
  | pair :: rest =>
      let (original, replacement) := pair in
      if Constr.equal original c then Some replacement else find_call rest c
  end.

Ltac2 rec open_body original_family target_family replacements c :=
  match find_call replacements c with
  | Some replacement => replacement
  | None =>
      if Constr.equal c original_family then target_family else
      Constr.Unsafe.map (open_body original_family target_family replacements) c
  end.

Definition ExecuteInput n := Pair C.Instruction (Pair (C.Bank n) (M.Masks (S n))).
Definition SharePair n := Pair (M.Shares (S n)) (M.Shares (S n)).
Definition MulInput n := Pair (M.Shares (S n)) (Pair (M.Shares (S n)) (M.Masks (S n))).

Definition execute_body {var func} n
    (operand : func (Pair (C.Bank n) (Bits 9)) (M.Shares (S n)))
    (add sub : func (SharePair n) (M.Shares (S n)))
    (mul : func (MulInput n) (M.Shares (S n)))
    (p : var (ExecuteInput n)) : Syntax.eexpr.eexpr var func (C.Bank n) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta [C.execute fn.body] in (fn.body (@C.execute var n) p) in
    let c := open_body constr:(fn.fn var) constr:(func)
      [(constr:(@C.read_operand var n), constr:(operand));
       (constr:(@M.share_map var Core.Add (S n)), constr:(add));
       (constr:(@M.share_map var Core.Sub (S n)), constr:(sub));
       (constr:(@M.multiply var (S n)), Control.hyp @mul)] c in exact $c).

Lemma execute_body_actual n p :
  Syntax.eexpr.interp (execute_body n (fn.interp (C.read_operand n))
    (fn.interp (M.share_map Core.Add (S n))) (fn.interp (M.share_map Core.Sub (S n)))
    (fn.interp (M.multiply (S n))) p) = fn.interp (C.execute n) p.
Proof. reflexivity. Qed.

Lemma execute_body_correct n operand add sub mul
    (Hop : forall x, operand x = fn.interp (C.read_operand n) x)
    (Hadd : forall x, add x = fn.interp (M.share_map Core.Add (S n)) x)
    (Hsub : forall x, sub x = fn.interp (M.share_map Core.Sub (S n)) x)
    (Hmul : forall x, mul x = fn.interp (M.multiply (S n)) x) p :
  Syntax.eexpr.interp (execute_body n operand add sub mul p) = fn.interp (C.execute n) p.
Proof.
  cbn [execute_body Syntax.eexpr.interp Syntax.eexpr.LetBlock Syntax.expr.interp].
  rewrite !Hop. rewrite !Hadd. rewrite !Hsub. rewrite !Hmul. reflexivity.
Qed.

Definition prepare_bank_body {var func} n
    (load : func C.Load (C.Bank n))
    (decode : func C.Control C.Instruction)
    (execute : func (ExecuteInput n) (C.Bank n))
    (collect : func (C.Bank n) (C.Bank n))
    (p : var (C.PreparationInput n)) : Syntax.eexpr.eexpr var func (C.Bank n) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta [C.prepare_bank fn.body] in
      (fn.body (@C.prepare_bank var n) p) in
    let c := open_body constr:(fn.fn var) constr:(func)
      [(constr:(@C.load_bank var n), constr:(load));
       (constr:(@C.decode var), constr:(decode));
       (constr:(@C.execute var n), constr:(execute));
       (constr:(@C.collect var n), constr:(collect))] c in exact $c).

Local Opaque C.load_bank C.decode C.execute C.collect.

Lemma prepare_bank_body_actual n p :
  Syntax.eexpr.interp (prepare_bank_body n (fn.interp (C.load_bank n))
    (fn.interp C.decode) (fn.interp (C.execute n)) (fn.interp (C.collect n)) p) =
  fn.interp (C.prepare_bank n) p.
Proof. reflexivity. Qed.

Lemma prepare_bank_body_correct n load decode execute collect
    (Hl : forall x, load x = fn.interp (C.load_bank n) x)
    (Hd : forall x, decode x = fn.interp C.decode x)
    (He : forall x, execute x = fn.interp (C.execute n) x)
    (Hc : forall x, collect x = fn.interp (C.collect n) x) p :
  Syntax.eexpr.interp (prepare_bank_body n load decode execute collect p) =
  fn.interp (C.prepare_bank n) p.
Proof.
  rewrite <- prepare_bank_body_actual.
  cbn [prepare_bank_body Syntax.eexpr.interp Syntax.eexpr.LetBlock Syntax.expr.interp].
  rewrite !Hl. rewrite !Hd. rewrite !He. rewrite !Hc. reflexivity.
Qed.

Definition prepare_body {var func} n
    (control : func (Pair C.Control (Pair Bool Bool)) C.Control)
    (bank : func (C.PreparationInput n) (C.Bank n))
    (p : var (C.PreparationInput n)) : Syntax.eexpr.eexpr var func (C.State n) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta [C.prepare fn.body] in (fn.body (@C.prepare var n) p) in
    let c := open_body constr:(fn.fn var) constr:(func)
      [(constr:(@C.next_control var), constr:(control));
       (constr:(@C.prepare_bank var n), constr:(bank))] c in exact $c).

Local Opaque C.next_control C.prepare_bank.

Lemma prepare_body_actual n p :
  Syntax.eexpr.interp (prepare_body n (fn.interp C.next_control)
    (fn.interp (C.prepare_bank n)) p) = fn.interp (C.prepare n) p.
Proof. reflexivity. Qed.

Lemma prepare_body_correct n control bank
    (Hc : forall x, control x = fn.interp C.next_control x)
    (Hb : forall x, bank x = fn.interp (C.prepare_bank n) x) p :
  Syntax.eexpr.interp (prepare_body n control bank p) = fn.interp (C.prepare n) p.
Proof.
  rewrite <- prepare_body_actual.
  cbn [prepare_body Syntax.eexpr.interp Syntax.eexpr.LetBlock Syntax.expr.interp].
  rewrite Hc. rewrite Hb. reflexivity.
Qed.

Definition tick_body {var func} n
    (prepare : func (C.PreparationInput n) (C.State n))
    (refresh : func (Pair (C.Bank n) (C.Coins n)) (C.Bank n))
    (p : var (C.Input n)) : Syntax.eexpr.eexpr var func (C.State n) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta [C.tick fn.body] in (fn.body (@C.tick var n) p) in
    let c := open_body constr:(fn.fn var) constr:(func)
      [(constr:(@C.prepare var n), constr:(prepare));
       (constr:(@B.refresh var n C.groups), constr:(refresh))] c in exact $c).

Local Opaque C.prepare B.refresh.

Lemma tick_body_actual n p :
  Syntax.eexpr.interp (tick_body n (fn.interp (C.prepare n))
    (fn.interp (B.refresh n C.groups)) p) = fn.interp (C.tick n) p.
Proof. reflexivity. Qed.

Lemma tick_body_correct n prepare refresh
    (Hp : forall x, prepare x = fn.interp (C.prepare n) x)
    (Hr : forall x, refresh x = fn.interp (B.refresh n C.groups) x) p :
  Syntax.eexpr.interp (tick_body n prepare refresh p) = fn.interp (C.tick n) p.
Proof.
  rewrite <- tick_body_actual.
  cbn [tick_body Syntax.eexpr.interp Syntax.eexpr.LetBlock Syntax.expr.interp].
  rewrite Hp. rewrite Hr. reflexivity.
Qed.

Definition gated_output_body {var func} n
    (ready : func (C.State n) Bool)
    (output : func (C.State n) (M.Shares (S n)))
    (p : var (C.State n)) : Syntax.eexpr.eexpr var func (M.Shares (S n)) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta [R.gated_output fn.body] in
      (fn.body (@R.gated_output var n) p) in
    let c := open_body constr:(fn.fn var) constr:(func)
      [(constr:(@C.ready var n), constr:(ready));
       (constr:(@C.output var n), constr:(output))] c in exact $c).

Local Opaque C.ready C.output.

Lemma gated_output_body_actual n p :
  Syntax.eexpr.interp (gated_output_body n (fn.interp (C.ready n))
    (fn.interp (C.output n)) p) = fn.interp (R.gated_output n) p.
Proof. reflexivity. Qed.

Lemma gated_output_body_correct n ready output
    (Hr : forall x, ready x = fn.interp (C.ready n) x)
    (Ho : forall x, output x = fn.interp (C.output n) x) p :
  Syntax.eexpr.interp (gated_output_body n ready output p) = fn.interp (R.gated_output n) p.
Proof.
  rewrite <- gated_output_body_actual.
  cbn [gated_output_body Syntax.eexpr.interp Syntax.eexpr.LetBlock Syntax.expr.interp].
  rewrite Hr. rewrite Ho. reflexivity.
Qed.

Definition cycle_body {var func} n
    (tick : func (C.Input n) (C.State n))
    (ready : func (C.State n) Bool)
    (output : func (C.State n) (M.Shares (S n)))
    (p : var (C.Input n)) : Syntax.eexpr.eexpr var func (R.Response n) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta [R.cycle fn.body] in (fn.body (@R.cycle var n) p) in
    let c := open_body constr:(fn.fn var) constr:(func)
      [(constr:(@C.tick var n), constr:(tick));
       (constr:(@C.ready var n), constr:(ready));
       (constr:(@R.gated_output var n), constr:(output))] c in exact $c).

Local Opaque C.tick R.gated_output.

Lemma cycle_body_actual n p :
  Syntax.eexpr.interp (cycle_body n (fn.interp (C.tick n))
    (fn.interp (C.ready n)) (fn.interp (R.gated_output n)) p) = fn.interp (R.cycle n) p.
Proof. reflexivity. Qed.

Lemma cycle_body_correct n tick ready output
    (Ht : forall x, tick x = fn.interp (C.tick n) x)
    (Hr : forall x, ready x = fn.interp (C.ready n) x)
    (Ho : forall x, output x = fn.interp (R.gated_output n) x) p :
  Syntax.eexpr.interp (cycle_body n tick ready output p) = fn.interp (R.cycle n) p.
Proof.
  rewrite <- cycle_body_actual.
  cbn [cycle_body Syntax.eexpr.interp Syntax.eexpr.LetBlock Syntax.expr.interp].
  rewrite Ht. rewrite Hr. rewrite Ho. reflexivity.
Qed.

End ControllerNativeContexts.
Print Assumptions ControllerNativeContexts.execute_body_correct.
Print Assumptions ControllerNativeContexts.prepare_bank_body_correct.
Print Assumptions ControllerNativeContexts.prepare_bank_body_actual.
Print Assumptions ControllerNativeContexts.prepare_body_correct.
Print Assumptions ControllerNativeContexts.prepare_body_actual.
Print Assumptions ControllerNativeContexts.tick_body_correct.
Print Assumptions ControllerNativeContexts.tick_body_actual.
Print Assumptions ControllerNativeContexts.gated_output_body_correct.
Print Assumptions ControllerNativeContexts.gated_output_body_actual.
Print Assumptions ControllerNativeContexts.cycle_body_correct.
Print Assumptions ControllerNativeContexts.cycle_body_actual.

Module ControllerFnsLink.

Fixpoint link {var func a b c d} (library : fns.fns var func a b)
    (continuation : func a b -> fns.fns var func c d) : fns.fns var func c d :=
  match library with
  | @fns.Let _ _ _ _ _ _ name argument body rest =>
      fns.Let name argument body (fun f => link (rest f) continuation)
  | @fns.Ret _ _ _ _ name argument body => fns.Let name argument body continuation
  end.

Lemma link_interp a b c d (library : fns.fns type.interp type.interpfn a b)
    (continuation : type.interpfn a b -> fns.fns type.interp type.interpfn c d) x :
  fns.interp (link library continuation) x =
  fns.interp (continuation (fns.interp library)) x.
Proof. induction library; cbn [link fns.interp]; auto. Qed.

End ControllerFnsLink.
Print Assumptions ControllerFnsLink.link_interp.

Module RuntimeLoad.
Module X := ControllerNativeContexts.
Module C := X.C.
Module M := C.M.
Module Core := M.Core.
Definition BitsRequest n := Pair M.Word (C.Bank n).

Definition bit_body {var func} n i
    (anchor : func M.Word (M.Shares (S n)))
    (raw : var M.Word) (bank : var (C.Bank n)) : eexpr.eexpr var func (C.Bank n) :=
  quartz_eexpr:(
    let bit := $(expr.Unop (unop.Slice (Z.of_nat i) 1) (expr.Var raw)) in
    let word := $(expr.Unop (@unop.UnsignedResize 1 255) (expr.Var bit)) in
    let shared := {anchor} (#word) in
    let address := $(expr.Const (t := Bits 9) (bits.of_Z 9 (Z.of_nat i))) in
    let bank <- #bank[#address] = #shared in return #bank).

Fixpoint steps {var func} n (positions : list nat)
    (anchor : func M.Word (M.Shares (S n)))
    (raw : var M.Word) (bank : var (C.Bank n)) : eexpr.eexpr var func (C.Bank n) :=
  match positions with
  | nil => quartz_eexpr:(return #bank)
  | i :: rest => eexpr.Bind "bank" (bit_body n i anchor raw bank)
      (fun next => steps n rest anchor raw next)
  end.

Definition bits_body {var func} n
    (anchor : func M.Word (M.Shares (S n))) (p : var (BitsRequest n)) :=
  eexpr.Let "raw" (quartz_expr:(#p .1)) (fun raw =>
  eexpr.Let "bank" (quartz_expr:(#p .2)) (fun bank =>
    steps n (iota 0 255) anchor raw bank)).

Definition body {var func} n
    (add : func (Pair M.Word M.Word) M.Word)
    (anchor : func M.Word (M.Shares (S n)))
    (load_bits : func (BitsRequest n) (C.Bank n))
    (p : var C.Load) : eexpr.eexpr var func (C.Bank n) :=
  ltac2:(
    let c := eval cbv beta iota zeta delta [C.load_bank fn.body] in
      (fn.body (@C.load_bank var n) p) in
    let c := X.open_body constr:(fn.fn var) constr:(func)
      [(constr:(@Core.arithmetic var Core.Add), constr:(add));
       (constr:(@C.anchor var n), constr:(anchor));
       (constr:(@C.load_bits var n (iota 0 255)), constr:(load_bits))] c in exact $c).

Definition library {var func} n
    (add : func (Pair M.Word M.Word) M.Word)
    (anchor : func M.Word (M.Shares (S n))) :
    fns.fns var func C.Load (C.Bank n) :=
  fns.Let "scalar_load_bits" "request" (bits_body n anchor) (fun load_bits =>
    fns.Ret "controller_load" "request" (body n add anchor load_bits)).

Lemma load_bits_cons n i rest raw bank :
  fn.interp (C.load_bits n (i :: rest)) (raw,bank) =
  fn.interp (C.load_bits n rest)
    (raw,fn.interp (C.load_bits n (i :: nil)) (raw,bank)).
Proof. reflexivity. Qed.

Local Opaque C.anchor Core.arithmetic type.default.

Lemma bit_body_correct n i anchor
    (Ha : forall w, anchor w = fn.interp (C.anchor n) w) raw bank :
  eexpr.interp (bit_body n i anchor raw bank) =
  fn.interp (C.load_bits n (i :: nil)) (raw,bank).
Proof.
  cbn [bit_body eexpr.interp eexpr.LetBlock expr.interp].
  rewrite Ha. reflexivity.
Qed.

Lemma steps_correct n positions anchor
    (Ha : forall w, anchor w = fn.interp (C.anchor n) w) raw bank :
  eexpr.interp (steps n positions anchor raw bank) =
  fn.interp (C.load_bits n positions) (raw,bank).
Proof.
  induction positions as [|i rest IH] in bank |- *.
  - reflexivity.
  - cbn [steps eexpr.interp eexpr.LetBlock].
    rewrite (bit_body_correct n i anchor Ha) load_bits_cons.
    exact (IH (fn.interp (C.load_bits n (i :: nil)) (raw,bank))).
Qed.

Lemma bits_body_correct n anchor
    (Ha : forall w, anchor w = fn.interp (C.anchor n) w) p :
  eexpr.interp (bits_body n anchor p) =
  fn.interp (C.load_bits n (iota 0 255)) p.
Proof.
  destruct p as [raw bank].
  exact (steps_correct n (iota 0 255) anchor Ha raw bank).
Qed.

Local Opaque C.load_bits.

Lemma body_actual n p :
  eexpr.interp (body n (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (C.anchor n)) (fn.interp (C.load_bits n (iota 0 255))) p) =
  fn.interp (C.load_bank n) p.
Proof. reflexivity. Qed.

Lemma body_correct n add anchor load_bits
    (Hadd : forall p, add p = fn.interp (Core.arithmetic Core.Add) p)
    (Ha : forall w, anchor w = fn.interp (C.anchor n) w)
    (Hb : forall p, load_bits p = fn.interp (C.load_bits n (iota 0 255)) p) p :
  eexpr.interp (body n add anchor load_bits p) = fn.interp (C.load_bank n) p.
Proof.
  rewrite <- (body_actual n p).
  cbn [body eexpr.interp eexpr.LetBlock expr.interp].
  rewrite Hadd !Ha Hb. reflexivity.
Qed.

Theorem library_correct n p :
  fns.interp (library n (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (C.anchor n))) p = fn.interp (C.load_bank n) p.
Proof.
  cbn [library fns.interp].
  apply body_correct; try (intro x; reflexivity).
Qed.

End RuntimeLoad.
Print Assumptions RuntimeLoad.library_correct.

Module ControllerNativeAssembly.
Module X := ControllerNativeContexts.
Module C := X.C.
Module R := X.R.
Module M := X.M.
Module B := X.B.
Module Core := X.Core.
Module P := RuntimePair.

Definition assemble {var func} n
    (operand : func (Pair (C.Bank n) (Bits 9)) (M.Shares (S n)))
    (load : func C.Load (C.Bank n))
    (decode : func C.Control C.Instruction)
    (collect : func (C.Bank n) (C.Bank n))
    (control : func (Pair C.Control (Pair Bool Bool)) C.Control)
    (refresh : func (Pair (C.Bank n) (C.Coins n)) (C.Bank n))
    (ready : func (C.State n) Bool)
    (output : func (C.State n) (M.Shares (S n)))
    (add sub : func (X.SharePair n) (M.Shares (S n)))
    (mul : func (X.MulInput n) (M.Shares (S n))) :
    fns.fns var func (C.Input n) (R.Response n) :=
  fns.Let "controller_execute" "request" (X.execute_body n operand add sub mul) (fun execute =>
  fns.Let "controller_prepare_bank" "request"
    (X.prepare_bank_body n load decode execute collect) (fun bank =>
  fns.Let "controller_prepare" "request" (X.prepare_body n control bank) (fun prepare =>
  fns.Let "controller_tick" "request" (X.tick_body n prepare refresh) (fun tick =>
  fns.Let "controller_gated_output" "state" (X.gated_output_body n ready output) (fun gated =>
  fns.Ret "cycle" "request" (X.cycle_body n tick ready gated)))))).

Lemma assemble_correct n operand load decode collect control refresh ready output add sub mul
    (Hop : forall x, operand x = fn.interp (C.read_operand n) x)
    (Hl : forall x, load x = fn.interp (C.load_bank n) x)
    (Hd : forall x, decode x = fn.interp C.decode x)
    (Hc : forall x, collect x = fn.interp (C.collect n) x)
    (Hctl : forall x, control x = fn.interp C.next_control x)
    (Hrefresh : forall x, refresh x = fn.interp (B.refresh n C.groups) x)
    (Hr : forall x, ready x = fn.interp (C.ready n) x)
    (Ho : forall x, output x = fn.interp (C.output n) x)
    (Ha : forall x, add x = fn.interp (M.share_map Core.Add (S n)) x)
    (Hs : forall x, sub x = fn.interp (M.share_map Core.Sub (S n)) x)
    (Hm : forall x, mul x = fn.interp (M.multiply (S n)) x) p :
  fns.interp (assemble n operand load decode collect control refresh ready output add sub mul) p =
  fn.interp (R.cycle n) p.
Proof.
  cbn [assemble fns.interp].
  apply X.cycle_body_correct.
  - intro x. apply X.tick_body_correct; [|exact Hrefresh].
    intro y. apply X.prepare_body_correct; [exact Hctl|].
    intro z. apply X.prepare_bank_body_correct; try assumption.
    intro u. apply X.execute_body_correct; assumption.
  - exact Hr.
  - intro x. apply X.gated_output_body_correct; assumption.
Qed.

Definition with_maps {var func} n
    (operand : func (Pair (C.Bank n) (Bits 9)) (M.Shares (S n)))
    (load : func C.Load (C.Bank n))
    (decode : func C.Control C.Instruction)
    (collect : func (C.Bank n) (C.Bank n))
    (control : func (Pair C.Control (Pair Bool Bool)) C.Control)
    (refresh : func (Pair (C.Bank n) (C.Coins n)) (C.Bank n))
    (ready : func (C.State n) Bool)
    (output : func (C.State n) (M.Shares (S n)))
    (field_add field_sub : func (Pair M.Word M.Word) M.Word)
    (mul : func (X.MulInput n) (M.Shares (S n))) :
    fns.fns var func (C.Input n) (R.Response n) :=
  fns.Let "shared_add" "request" (P.diagonal_body (S n) field_add) (fun add =>
  fns.Let "shared_sub" "request" (P.diagonal_body (S n) field_sub) (fun sub =>
    assemble n operand load decode collect control refresh ready output add sub mul)).

Lemma with_maps_actual n mul
    (Hm : forall x, mul x = fn.interp (M.multiply (S n)) x) p :
  fns.interp (with_maps n (fn.interp (C.read_operand n)) (fn.interp (C.load_bank n))
    (fn.interp C.decode) (fn.interp (C.collect n)) (fn.interp C.next_control)
    (fn.interp (B.refresh n C.groups)) (fn.interp (C.ready n)) (fn.interp (C.output n))
    (fn.interp (Core.arithmetic Core.Add)) (fn.interp (Core.arithmetic Core.Sub)) mul) p =
  fn.interp (R.cycle n) p.
Proof.
  cbn [with_maps fns.interp].
  apply assemble_correct; try (intro x; reflexivity).
  - intros [a b]. apply P.map_body_correct.
  - intros [a b]. apply P.map_body_correct.
  - exact Hm.
Qed.

End ControllerNativeAssembly.
Print Assumptions ControllerNativeAssembly.assemble_correct.
Print Assumptions ControllerNativeAssembly.with_maps_actual.

Module ControllerNativeBank.
Module B := MaskedBank.
Module M := B.M.
Module Core := M.Core.
Module RR := RuntimeRefresh.
Module Link := ControllerFnsLink.
Module S := ControllerNativeAssembly.
Module C := S.C.
Module R := S.R.

Definition Request n groups := Pair (B.Bank n groups) (B.Coins n groups).

Fixpoint steps {var func} n groups (indices : list 'I_groups)
    (refresh : func (RR.Request n) (M.Shares (S n)))
    (a : var (B.Bank n groups)) (r : var (B.Coins n groups))
    (c : var (B.Bank n groups)) : eexpr.eexpr var func (B.Bank n groups) :=
  match indices with
  | nil => quartz_eexpr:(return #c)
  | i :: rest => eexpr.Bind "bank" (quartz_eexpr:(
      let index := $(expr.Const (t := Bits (M.index_width groups)) (M.index_bits groups i)) in
      let shares := #a[#index] in
      let coins := #r[#index] in
      let value := {refresh} ((#shares,#coins)) in
      let bank <- #c[#index] = #value in return #bank))
      (fun next => steps n groups rest refresh a r next)
  end.

Definition body {var func} n groups
    (refresh : func (RR.Request n) (M.Shares (S n)))
    (p : var (Request n groups)) : eexpr.eexpr var func (B.Bank n groups) :=
  eexpr.Let "bank" (quartz_expr:(#p .1)) (fun a =>
  eexpr.Let "coins" (quartz_expr:(#p .2)) (fun r =>
    steps n groups (enum 'I_groups) refresh a r a)).

Local Opaque M.refresh M.index_bits B.get B.put.

Lemma steps_cons_interp n groups i rest refresh a r c :
  eexpr.interp (steps n groups (i :: rest) refresh a r c) =
  eexpr.interp (steps n groups rest refresh a r
    (domain.Vector.upd c (val i) (fun _ => refresh
      (@M.read (M.Shares (S n)) groups a (val i),
       @M.read (M.Shares n) groups r (val i))))).
Proof.
  cbn [steps eexpr.interp eexpr.LetBlock expr.interp expr.tt
    binop.interp typeWithHole.get typeWithHole.upd].
  rewrite !M.index_unsigned !Nat2Z.id. reflexivity.
Qed.

Lemma steps_correct n groups indices refresh
    (Hrefresh : forall p, refresh p = fn.interp (M.refresh n) p) a r c :
  eexpr.interp (steps n groups indices refresh a r c) =
  fn.interp (B.refresh_steps n groups indices) (a,(r,c)).
Proof.
  rewrite B.refresh_steps_interp.
  induction indices as [|i rest IH] in c |- *.
  - reflexivity.
  - rewrite steps_cons_interp Hrefresh. apply IH.
Qed.

Lemma body_correct n groups refresh
    (Hrefresh : forall p, refresh p = fn.interp (M.refresh n) p) a r :
  eexpr.interp (body n groups refresh (a,r)) = fn.interp (B.refresh n groups) (a,r).
Proof.
  change (eexpr.interp (steps n groups (enum 'I_groups) refresh a r a) =
    fn.interp (B.refresh_steps n groups (enum 'I_groups)) (a,(r,a))).
  apply steps_correct. exact Hrefresh.
Qed.

Definition library {var func} n groups
    (add sub : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (Request n groups) (B.Bank n groups) :=
  Link.link (RR.library n add sub) (fun refresh =>
    fns.Ret "bank_refresh" "request" (body n groups refresh)).

Theorem library_correct n groups a r :
  fns.interp (library n groups (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub))) (a,r) = fn.interp (B.refresh n groups) (a,r).
Proof.
  unfold library. rewrite Link.link_interp.
  change (eexpr.interp (body n groups
    (fns.interp (RR.library n (fn.interp (Core.arithmetic Core.Add))
      (fn.interp (Core.arithmetic Core.Sub)))) (a,r)) =
    fn.interp (B.refresh n groups) (a,r)).
  apply body_correct. intros [shares coins]. apply RR.library_correct.
Qed.

Lemma with_maps_refresh_correct n refresh mul
    (Hr : forall p, refresh p = fn.interp (B.refresh n C.groups) p)
    (Hm : forall p, mul p = fn.interp (M.multiply (S n)) p) p :
  fns.interp (S.with_maps n (fn.interp (C.read_operand n)) (fn.interp (C.load_bank n))
    (fn.interp C.decode) (fn.interp (C.collect n)) (fn.interp C.next_control)
    refresh (fn.interp (C.ready n)) (fn.interp (C.output n))
    (fn.interp (Core.arithmetic Core.Add)) (fn.interp (Core.arithmetic Core.Sub)) mul) p =
  fn.interp (R.cycle n) p.
Proof.
  cbn [S.with_maps fns.interp].
  apply S.assemble_correct; try (intro x; reflexivity).
  - exact Hr.
  - intros [a b]. apply S.P.map_body_correct.
  - intros [a b]. apply S.P.map_body_correct.
  - exact Hm.
Qed.

End ControllerNativeBank.
Print Assumptions ControllerNativeBank.library_correct.
Print Assumptions ControllerNativeBank.with_maps_refresh_correct.

Module ControllerNativeStatic.
Module A := MaskedArithmeticRTL.
Module D := ControllerNativeBank.
Module S := ControllerNativeAssembly.
Module T := RuntimeStaticLibraries.
Module C := S.C.
Module M := S.M.
Module B := S.B.
Module X := S.X.
Module R := S.R.
Module Link := D.Link.

Definition bank_body {var func} n groups
    (refresh : func (D.RR.Request n) (M.Shares (S n)))
    (p : var (D.Request n groups)) : eexpr.eexpr var func (B.Bank n groups) :=
  eexpr.Let "bank" (quartz_expr:(#p .1)) (fun a =>
  eexpr.Let "coins" (quartz_expr:(#p .2)) (fun r =>
    D.steps n groups (A.indices groups) refresh a r a)).

Lemma bank_body_exact {var func} n groups refresh :
  @bank_body var func n groups refresh = D.body n groups refresh.
Proof. unfold bank_body, D.body. rewrite A.indices_correct. reflexivity. Qed.

Definition bank_library {var func} n groups
    (add sub : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (D.Request n groups) (B.Bank n groups) :=
  Link.link (T.refresh_library n add sub) (fun refresh =>
    fns.Ret "bank_refresh" "request" (bank_body n groups refresh)).

Lemma bank_library_exact {var func} n groups add sub :
  @bank_library var func n groups add sub = D.library n groups add sub.
Proof.
  unfold bank_library, D.library.
  rewrite T.refresh_library_exact. unfold bank_body, D.body.
  rewrite A.indices_correct. reflexivity.
Qed.

Definition with_maps {var func} n
    (operand : func (Pair (C.Bank n) (Bits 9)) (M.Shares (S n)))
    (load : func C.Load (C.Bank n))
    (decode : func C.Control C.Instruction)
    (collect : func (C.Bank n) (C.Bank n))
    (control : func (Pair C.Control (Pair Bool Bool)) C.Control)
    (refresh : func (Pair (C.Bank n) (C.Coins n)) (C.Bank n))
    (ready : func (C.State n) Bool)
    (output : func (C.State n) (M.Shares (S n)))
    (field_add field_sub : func (Pair M.Word M.Word) M.Word)
    (mul : func (X.MulInput n) (M.Shares (S n))) :
    fns.fns var func (C.Input n) (R.Response n) :=
  fns.Let "shared_add" "request" (T.diagonal_body (S n) field_add) (fun add =>
  fns.Let "shared_sub" "request" (T.diagonal_body (S n) field_sub) (fun sub =>
    S.assemble n operand load decode collect control refresh ready output add sub mul)).

Lemma with_maps_exact {var func} n operand load decode collect control refresh ready output
    field_add field_sub mul :
  @with_maps var func n operand load decode collect control refresh ready output
    field_add field_sub mul =
  S.with_maps n operand load decode collect control refresh ready output field_add field_sub mul.
Proof.
  unfold with_maps, S.with_maps.
  rewrite !T.diagonal_body_exact. reflexivity.
Qed.

End ControllerNativeStatic.
Print Assumptions ControllerNativeStatic.bank_body_exact.
Print Assumptions ControllerNativeStatic.bank_library_exact.
Print Assumptions ControllerNativeStatic.with_maps_exact.

Module ControllerNativeSafe.
Module A := MaskedArithmeticRTL.
Module X := ControllerNativeContexts.
Module C := X.C.
Module M := X.M.
Module B := X.B.
Module Core := X.Core.
Module R := X.R.

Definition bank_library {var func} n groups
    (refresh : func (Pair (M.Shares (S n)) (M.Shares n)) (M.Shares (S n))) :
    fns.fns var func (ControllerNativeBank.Request n groups) (B.Bank n groups) :=
  fns.Ret "bank_refresh" "request" (fun p =>
    A.safe_locals (ControllerNativeStatic.bank_body n groups refresh p)).

Lemma bank_library_correct n groups refresh
    (Hr : forall p, refresh p = fn.interp (M.refresh n) p) a r :
  fns.interp (bank_library n groups refresh) (a,r) = fn.interp (B.refresh n groups) (a,r).
Proof.
  change (eexpr.interp (A.safe_locals
    (ControllerNativeStatic.bank_body n groups refresh (a,r))) =
    fn.interp (B.refresh n groups) (a,r)).
  rewrite A.safe_locals_correct. rewrite ControllerNativeStatic.bank_body_exact.
  apply ControllerNativeBank.body_correct. exact Hr.
Qed.

Definition assemble {var func} n
    (operand : func (Pair (C.Bank n) (Bits 9)) (M.Shares (S n)))
    (load : func C.Load (C.Bank n))
    (decode : func C.Control C.Instruction)
    (collect : func (C.Bank n) (C.Bank n))
    (control : func (Pair C.Control (Pair Bool Bool)) C.Control)
    (refresh : func (Pair (C.Bank n) (C.Coins n)) (C.Bank n))
    (ready : func (C.State n) Bool)
    (output : func (C.State n) (M.Shares (S n)))
    (add sub : func (X.SharePair n) (M.Shares (S n)))
    (mul : func (X.MulInput n) (M.Shares (S n))) :
    fns.fns var func (C.Input n) (R.Response n) :=
  fns.Let "controller_execute" "request"
    (fun p => A.safe_locals (X.execute_body n operand add sub mul p)) (fun execute =>
  fns.Let "controller_prepare_bank" "request"
    (fun p => A.safe_locals (X.prepare_bank_body n load decode execute collect p)) (fun bank =>
  fns.Let "controller_prepare" "request"
    (fun p => A.safe_locals (X.prepare_body n control bank p)) (fun prepare =>
  fns.Let "controller_tick" "request"
    (fun p => A.safe_locals (X.tick_body n prepare refresh p)) (fun tick =>
  fns.Let "controller_gated_output" "state"
    (fun p => A.safe_locals (X.gated_output_body n ready output p)) (fun gated =>
  fns.Ret "cycle" "request" (fun p => A.safe_locals (X.cycle_body n tick ready gated p))))))).

Theorem assemble_correct n operand load decode collect control refresh ready output add sub mul
    (Hop : forall x, operand x = fn.interp (C.read_operand n) x)
    (Hl : forall x, load x = fn.interp (C.load_bank n) x)
    (Hd : forall x, decode x = fn.interp C.decode x)
    (Hc : forall x, collect x = fn.interp (C.collect n) x)
    (Hctl : forall x, control x = fn.interp C.next_control x)
    (Hrefresh : forall x, refresh x = fn.interp (B.refresh n C.groups) x)
    (Hr : forall x, ready x = fn.interp (C.ready n) x)
    (Ho : forall x, output x = fn.interp (C.output n) x)
    (Ha : forall x, add x = fn.interp (M.share_map Core.Add (S n)) x)
    (Hs : forall x, sub x = fn.interp (M.share_map Core.Sub (S n)) x)
    (Hm : forall x, mul x = fn.interp (M.multiply (S n)) x) p :
  fns.interp (assemble n operand load decode collect control refresh ready output add sub mul) p =
  fn.interp (R.cycle n) p.
Proof.
  cbn [assemble fns.interp].
  rewrite A.safe_locals_correct. apply X.cycle_body_correct.
  - intro x. rewrite A.safe_locals_correct. apply X.tick_body_correct; [|exact Hrefresh].
    intro y. rewrite A.safe_locals_correct. apply X.prepare_body_correct; [exact Hctl|].
    intro z. rewrite A.safe_locals_correct. apply X.prepare_bank_body_correct; try assumption.
    intro u. rewrite A.safe_locals_correct. apply X.execute_body_correct; assumption.
  - exact Hr.
  - intro x. rewrite A.safe_locals_correct. apply X.gated_output_body_correct; assumption.
Qed.

End ControllerNativeSafe.
Print Assumptions ControllerNativeSafe.bank_library_correct.
Print Assumptions ControllerNativeSafe.assemble_correct.

Module RuntimeSafeLoad.
Module RL := RuntimeLoad.
Module C := RL.C.
Module M := RL.M.
Module Core := M.Core.
Module A := MaskedArithmeticRTL.

Definition load_bits_body {var func} n
    (anchor : func M.Word (M.Shares (S n))) (p : var (RL.BitsRequest n)) :=
  A.safe_locals (RL.bits_body n anchor p).

Definition load_body {var func} n
    (add : func (Pair M.Word M.Word) M.Word)
    (anchor : func M.Word (M.Shares (S n)))
    (bits : func (RL.BitsRequest n) (C.Bank n)) (p : var C.Load) :=
  A.safe_locals (RL.body n add anchor bits p).

Definition load_library {var func} n
    (add : func (Pair M.Word M.Word) M.Word)
    (anchor : func M.Word (M.Shares (S n))) : fns.fns var func C.Load (C.Bank n) :=
  fns.Let "scalar_load_bits" "request" (load_bits_body n anchor) (fun bits =>
    fns.Ret "controller_load" "request" (load_body n add anchor bits)).

Theorem load_library_contract n add anchor
    (Ha : forall p, add p = fn.interp (Core.arithmetic Core.Add) p)
    (Hanchor : forall w, anchor w = fn.interp (C.anchor n) w) p :
  fns.interp (load_library n add anchor) p = fn.interp (C.load_bank n) p.
Proof.
  cbn [load_library fns.interp]. unfold load_body.
  rewrite A.safe_locals_correct. apply RL.body_correct; try assumption.
  intro x. unfold load_bits_body. rewrite A.safe_locals_correct.
  exact (RL.bits_body_correct n anchor Hanchor x).
Qed.

Corollary load_library_correct n p :
  fns.interp (load_library n (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (C.anchor n))) p = fn.interp (C.load_bank n) p.
Proof. apply load_library_contract; intro x; reflexivity. Qed.

End RuntimeSafeLoad.
Print Assumptions RuntimeSafeLoad.load_library_contract.
Print Assumptions RuntimeSafeLoad.load_library_correct.
