From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From Stdlib Require Import BinInt Bits List Vector.
Import InterfaceExample fn type ListNotations.
Import QStdlib.
Import (coercions) domain.Zmod.
Open Scope Z_scope.

Module LadderAccelerator.
  Definition prime : Z := 2^255 - 19.
  Import (notations) eexpr expr.
  Local Open Scope string_scope.

  (* Three folds reduce any 512-bit input to below 2p. *)
  Definition fold255 {var} : fn var (Bits 512) (Bits 512) :=
    Fn (fun x => quartz_eexpr:(
      let lo := $(expr.Unop unop.UnsignedResize (expr.Unop (unop.Slice 0 255) (expr.Var x))) in
      let hi := #x >> (512 'd 255) in
      let scaled := $(expr.Binop binop.Mul (expr.Var hi) (expr.Const (t := Bits 512) (bits.of_Z 512 19))) in
      return #lo + #scaled)).

  Definition reduce {var} : fn var (Bits 512) (Bits 255) :=
    Fn (fun x => quartz_eexpr:(
      let a := fold255 (#x) in
      let b := fold255 (#a) in
      let c := fold255 (#b) in
      let r := $(expr.If (expr.Binop (binop.Compare false binop.cGe)
        (expr.Var c) (expr.Const (t := Bits 512) (bits.of_Z 512 prime)))
        (expr.Binop binop.Sub (expr.Var c) (expr.Const (t := Bits 512) (bits.of_Z 512 prime))) (expr.Var c)) in
      return $(expr.Unop unop.UnsignedResize (expr.Var r)))).

  Inductive operation := Add | Sub | Mul.
  Definition arithmetic {var} (op : operation) : fn var (Pair (Bits 255) (Bits 255)) (Bits 255) :=
    Fn (fun p => quartz_eexpr:(
      let pa := #p .1 in
      let pb := #p .2 in
      let a := $(expr.Unop (@unop.UnsignedResize 255 512) (expr.Var pa)) in
      let b := $(expr.Unop (@unop.UnsignedResize 255 512) (expr.Var pb)) in
      let raw := $(match op with
        | Add => expr.Binop binop.Add (expr.Var a) (expr.Var b)
        | Sub => expr.Binop binop.Sub
            (expr.Binop binop.Add (expr.Var a) (expr.Const (t := Bits 512) (bits.of_Z 512 (2*prime)))) (expr.Var b)
        | Mul => expr.Binop binop.Mul (expr.Var a) (expr.Var b)
        end) in
      return reduce (#raw))).

  Record state := { phase : Bits 5; bank : Vector.t (bits 255) 32 }.
  Definition State := type.reify'' state.
  Coercion rep (s : state) : State :=
    ltac2:(let t := struct.rep &s in exact $t).

  Record inputs := { in_x1 : Bits 255; in_x2 : Bits 255; in_z2 : Bits 255;
                     in_x3 : Bits 255; in_z3 : Bits 255 }.
  Definition Inputs := type.reify'' inputs.
  Coercion input_rep (s : inputs) : Inputs :=
    ltac2:(let t := struct.rep &s in exact $t).

  (* Starting a request clears all scratch values and replaces any active request. *)
  Definition start {var} : fn var Inputs State :=
    Fn (fun input => quartz_eexpr:(
      let s := $(expr.Const (t := State) (type.default State)) in
      let regs <- (#s..bank)[5 'd 0] = #input..in_x1 in
      let regs <- #regs[5 'd 1] = #input..in_x2 in
      let regs <- #regs[5 'd 2] = #input..in_z2 in
      let regs <- #regs[5 'd 3] = #input..in_x3 in
      let regs <- #regs[5 'd 4] = #input..in_z3 in
      let regs <- #regs[5 'd 5] = (255 'd 121666) in
      let s <- #s..bank = #regs in
      return #s)).

  (* Phase 31 is idle, distinct from completed phase 18. *)
  Definition reset {var} : fn var State State :=
    Fn (fun old => quartz_eexpr:(
      let s := $(expr.Const (t := State) (type.default State)) in
      let s <- #s..phase = (5 'd 31) in
      return #s)).

  Definition instruction := (operation * Z * Z * Z)%type.
  Definition schedule : list instruction :=
    [(Add,6,1,2); (Sub,7,1,2); (Add,8,3,4); (Sub,9,3,4);
     (Mul,10,6,6); (Mul,11,7,7); (Mul,12,6,9); (Mul,13,7,8);
     (Add,14,12,13); (Sub,15,12,13); (Mul,16,14,14); (Mul,17,15,15);
     (Mul,18,17,0); (Mul,19,10,11); (Sub,20,10,11); (Mul,21,5,20);
     (Add,22,11,21); (Mul,23,20,22)].

  Definition execute {var} (i : instruction) : fn var State State :=
    let '(op,rd,ra,rb) := i in
    Fn (fun s => quartz_eexpr:(
      let a := #s..bank[$(expr.Const (t := Bits 5) (bits.of_Z 5 ra))] in
      let b := #s..bank[$(expr.Const (t := Bits 5) (bits.of_Z 5 rb))] in
      let result := {arithmetic op} ((#a, #b)) in
      let regs <- (#s..bank)[$(expr.Const (t := Bits 5) (bits.of_Z 5 rd))] = #result in
      let next <- #s..bank = #regs in
      let next <- #next..phase = #s..phase + (5 'd 1) in
      return #next)).

  Fixpoint dispatch {var} (pc : Z) (code : list instruction) : fn var State State :=
    match code with
    | [] => Fn (fun s => quartz_eexpr:(return #s))
    | i :: rest => Fn (fun s => quartz_eexpr:(
        if #s..phase == $(expr.Const (t := Bits 5) (bits.of_Z 5 pc)) then
          return {execute i} (#s)
        else return {dispatch (pc+1) rest} (#s)))
    end.
  Definition tick {var} : fn var State State := dispatch 0 schedule.
  Definition phase_value {var} : fn var State (Bits 5) :=
    Fn (fun s => quartz_eexpr:(return #s..phase)).
  Definition ready {var} : fn var State Bool :=
    Fn (fun s => quartz_eexpr:(return #s..phase == (5 'd 18))).

  Lemma execute_phase i s :
    fn.interp phase_value (fn.interp (execute i) s) =
    Zmod.add (fn.interp phase_value s) (bits.of_Z 5 1).
  Proof.
    destruct i as [[[op rd] ra] rb]. reflexivity.
  Qed.

  Lemma dispatch_phase_independent code pc s1 s2 :
    fn.interp phase_value s1 = fn.interp phase_value s2 ->
    fn.interp phase_value (fn.interp (dispatch pc code) s1) =
    fn.interp phase_value (fn.interp (dispatch pc code) s2).
  Proof.
    revert pc s1 s2. induction code as [|i rest IH]; intros pc s1 s2 H.
    - exact H.
    - change (fn.interp phase_value
        (if Zmod.nonzero (Zmod.embed_bool (Zmod.eqb (fn.interp phase_value s1) (bits.of_Z 5 pc)))
         then fn.interp (execute i) s1 else fn.interp (dispatch (pc+1) rest) s1) =
        fn.interp phase_value
        (if Zmod.nonzero (Zmod.embed_bool (Zmod.eqb (fn.interp phase_value s2) (bits.of_Z 5 pc)))
         then fn.interp (execute i) s2 else fn.interp (dispatch (pc+1) rest) s2)).
      rewrite H. destruct (Zmod.nonzero (Zmod.embed_bool
        (Zmod.eqb (fn.interp phase_value s2) (bits.of_Z 5 pc)))).
      + rewrite !execute_phase, H. reflexivity.
      + apply IH, H.
  Qed.

  Theorem tick_phase_independent s1 s2 :
    fn.interp phase_value s1 = fn.interp phase_value s2 ->
    fn.interp phase_value (fn.interp tick s1) = fn.interp phase_value (fn.interp tick s2).
  Proof. apply dispatch_phase_independent. Qed.

  Definition initial (x1 x2 z2 x3 z3 : Z) : State :=
    rep {| phase := bits.of_Z 5 0;
      bank := Vector.of_list
        (List.map (fun x => bits.of_Z 255 x) [x1;x2;z2;x3;z3;121666] ++ List.repeat (bits.of_Z 255 0) 26) |}.

  Lemma start_initial x1 x2 z2 x3 z3 :
    fn.interp start (input_rep {|in_x1 := bits.of_Z 255 x1; in_x2 := bits.of_Z 255 x2;
      in_z2 := bits.of_Z 255 z2; in_x3 := bits.of_Z 255 x3; in_z3 := bits.of_Z 255 z3|}) =
    initial x1 x2 z2 x3 z3.
  Proof. reflexivity. Qed.

  Lemma reset_clears s :
    fn.interp reset s = rep {|phase := bits.of_Z 5 31; bank := Vector.const (bits.of_Z 255 0) 32|}.
  Proof. reflexivity. Qed.
  Fixpoint run (cycles : nat) (s : State) : State :=
    match cycles with O => s | S rest => run rest (fn.interp tick s) end.

  Theorem run_phase_independent cycles s1 s2 :
    fn.interp phase_value s1 = fn.interp phase_value s2 ->
    fn.interp phase_value (run cycles s1) = fn.interp phase_value (run cycles s2).
  Proof.
    revert s1 s2. induction cycles; intros s1 s2 H.
    - exact H.
    - apply IHcycles, tick_phase_independent, H.
  Qed.

  Theorem ready_after_step x1 x2 z2 x3 z3 :
    fn.interp ready (run 18 (initial x1 x2 z2 x3 z3)) = true.
  Proof.
    assert (Hready : forall s, fn.interp ready s =
      Zmod.embed_bool (Zmod.eqb (fn.interp phase_value s) (bits.of_Z 5 18))) by reflexivity.
    rewrite Hready.
    rewrite (run_phase_independent 18 (initial x1 x2 z2 x3 z3) (initial 0 0 0 0 0))
      by reflexivity.
    vm_compute. reflexivity.
  Qed.
  Definition output {var} : fn var State (Pair (Pair (Bits 255) (Bits 255)) (Pair (Bits 255) (Bits 255))) :=
    Fn (fun s => quartz_eexpr:(return ((#s..bank[5 'd 19], #s..bank[5 'd 23]),
      (#s..bank[5 'd 16], #s..bank[5 'd 18])))).
End LadderAccelerator.
