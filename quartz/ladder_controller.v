From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import accelerator accelerator_correctness accelerator_ladder_bridge.
From Stdlib Require Import ZArith Bits Lia.
Require Import ladder_math.
Import fn type InterfaceExample.QStdlib.
Import (coercions) domain.Zmod.
Open Scope Z_scope.

Module LadderController.
  Module Core := LadderAccelerator.
  Import (notations) eexpr expr.
  Local Open Scope string_scope.

  (* Prep(0), Work(1), Collect(2), FinalSwap(3), Square(4), Multiply(5), Finish(6), Done(7).
     5101 projective ticks and 511 affine ticks; every arithmetic operation is clocked.
     Scalar, prev, coordinates, accumulator, and core storage are unprotected here. *)
  Record control := {
    stage : Bits 4; index : Bits 8; elapsed : Bits 5;
    x1 : Bits 255; scalar : Bits 255; prev : Bool;
    x2 : Bits 255; z2 : Bits 255; x3 : Bits 255; z3 : Bits 255; acc : Bits 255
  }.
  Definition Control := type.reify'' control.
  Coercion rep (s : control) : Control :=
    ltac2:(let t := struct.rep &s in exact $t).
  Definition State := Pair Control Core.State.
  Definition Inputs := Pair (Bits 255) (Bits 255).

  Definition init {var} : fn var Inputs State :=
    Fn (fun input => quartz_eexpr:(
      let c := $(expr.Const (t := Control) (type.default Control)) in
      let c <- #c..index = (8 'd 254) in
      let c <- #c..acc = (255 'd 1) in
      let c <- #c..x1 = #input .1 in
      let c <- #c..scalar = #input .2 in
      let c <- #c..x2 = (255 'd 1) in
      let c <- #c..x3 = #input .1 in
      let c <- #c..z3 = (255 'd 1) in
      let engine := Core.reset ($(expr.Const (t := Core.State) (type.default Core.State))) in
      return (#c, #engine))).

  Definition prep {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let c := #s .1 in
      let pos := #c..index in
      let shifted := #c..scalar >> $(expr.Unop (@unop.UnsignedResize 8 255) (expr.Var pos)) in
      let bit := $(expr.Unop (unop.Slice 0 1) (expr.Var shifted)) in
      let swap := #c..prev ^ #bit in
      let cx2 := #c..x2 in let cz2 := #c..z2 in
      let cx3 := #c..x3 in let cz3 := #c..z3 in
      let a := $(expr.If (expr.Var swap) (expr.Var cx3) (expr.Var cx2)) in
      let b := $(expr.If (expr.Var swap) (expr.Var cz3) (expr.Var cz2)) in
      let d := $(expr.If (expr.Var swap) (expr.Var cx2) (expr.Var cx3)) in
      let e := $(expr.If (expr.Var swap) (expr.Var cz2) (expr.Var cz3)) in
      let input := $(expr.Const (t := Core.Inputs) (type.default Core.Inputs)) in
      let input <- #input..Core.in_x1 = #c..x1 in
      let input <- #input..Core.in_x2 = #a in
      let input <- #input..Core.in_z2 = #b in
      let input <- #input..Core.in_x3 = #d in
      let input <- #input..Core.in_z3 = #e in
      let engine := Core.start (#input) in
      let c <- #c..prev = #bit in
      let c <- #c..elapsed = (5 'd 0) in
      let c <- #c..stage = (4 'd 1) in
      return (#c, #engine))).

  Definition work {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let c := #s .1 in
      let engine := Core.tick (#s .2) in
      let last := #c..elapsed == (5 'd 17) in
      let c <- #c..elapsed = #c..elapsed + (5 'd 1) in
      let c <- #c..stage = $(expr.If (expr.Var last)
        (expr.Const (t := Bits 4) (bits.of_Z 4 2)) (expr.Const (t := Bits 4) (bits.of_Z 4 1))) in
      return (#c, #engine))).

  Definition collect {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let c := #s .1 in
      let result := Core.output (#s .2) in
      let c <- #c..x2 = #result .1 .1 in
      let c <- #c..z2 = #result .1 .2 in
      let c <- #c..x3 = #result .2 .1 in
      let c <- #c..z3 = #result .2 .2 in
      let pos := #c..index in
      let last := #pos == (8 'd 0) in
      let next := #pos - (8 'd 1) in
      let c <- #c..index = $(expr.If (expr.Var last) (expr.Var pos) (expr.Var next)) in
      let c <- #c..stage = $(expr.If (expr.Var last)
        (expr.Const (t := Bits 4) (bits.of_Z 4 3)) (expr.Const (t := Bits 4) (bits.of_Z 4 0))) in
      return (#c, #s .2))).

  Definition final_swap {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let c := #s .1 in
      let swap := #c..prev in
      let a := #c..x2 in let b := #c..z2 in
      let d := #c..x3 in let e := #c..z3 in
      let c <- #c..x2 = $(expr.If (expr.Var swap) (expr.Var d) (expr.Var a)) in
      let c <- #c..z2 = $(expr.If (expr.Var swap) (expr.Var e) (expr.Var b)) in
      let c <- #c..x3 = $(expr.If (expr.Var swap) (expr.Var a) (expr.Var d)) in
      let c <- #c..z3 = $(expr.If (expr.Var swap) (expr.Var b) (expr.Var e)) in
      let c <- #c..stage = (4 'd 4) in
      let c <- #c..index = (8 'd 254) in
      let c <- #c..acc = (255 'd 1) in
      return (#c, #s .2))).

  Definition inverse_exponent : Z := Core.prime - 2.

  Definition affine_square {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let c := #s .1 in
      let value := {Core.arithmetic Core.Mul} ((#c..acc, #c..acc)) in
      let c <- #c..acc = #value in
      let c <- #c..stage = (4 'd 5) in
      return (#c, #s .2))).

  Definition affine_multiply {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let c := #s .1 in
      let pos := #c..index in
      let exponent := $(expr.Const (t := Bits 255) (bits.of_Z 255 inverse_exponent)) in
      let shifted := #exponent >> $(expr.Unop (@unop.UnsignedResize 8 255) (expr.Var pos)) in
      let bit := $(expr.Unop (unop.Slice 0 1) (expr.Var shifted)) in
      let denominator := #c..z2 in
      let factor := $(expr.If (expr.Var bit) (expr.Var denominator)
        (expr.Const (t := Bits 255) (bits.of_Z 255 1))) in
      let value := {Core.arithmetic Core.Mul} ((#c..acc, #factor)) in
      let last := #pos == (8 'd 0) in
      let next := #pos - (8 'd 1) in
      let c <- #c..acc = #value in
      let c <- #c..index = $(expr.If (expr.Var last) (expr.Var pos) (expr.Var next)) in
      let c <- #c..stage = $(expr.If (expr.Var last)
        (expr.Const (t := Bits 4) (bits.of_Z 4 6)) (expr.Const (t := Bits 4) (bits.of_Z 4 4))) in
      return (#c, #s .2))).

  Definition affine_finish {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let c := #s .1 in
      let value := {Core.arithmetic Core.Mul} ((#c..x2, #c..acc)) in
      let c <- #c..acc = #value in
      let c <- #c..stage = (4 'd 7) in
      return (#c, #s .2))).

  Definition ready {var} : fn var State Bool :=
    Fn (fun s => quartz_eexpr:(let c := #s .1 in return #c..stage == (4 'd 7))).

  Definition output {var} : fn var State (Bits 255) :=
    Fn (fun s => quartz_eexpr:(let c := #s .1 in return #c..acc)).

  Definition tick {var} : fn var State State :=
    Fn (fun s => quartz_eexpr:(
      let c := #s .1 in
      if #c..stage == (4 'd 0) then return prep (#s) else
      if #c..stage == (4 'd 1) then return work (#s) else
      if #c..stage == (4 'd 2) then return collect (#s) else
      if #c..stage == (4 'd 3) then return final_swap (#s) else
      if #c..stage == (4 'd 4) then return affine_square (#s) else
      if #c..stage == (4 'd 5) then return affine_multiply (#s) else
      if #c..stage == (4 'd 6) then return affine_finish (#s) else return #s)).

  Definition public_control {var} : fn var State (Pair (Bits 4) (Pair (Bits 8) (Bits 5))) :=
    Fn (fun s => quartz_eexpr:(let c := #s .1 in return (#c..stage, (#c..index, #c..elapsed)))).
  Definition persistent {var} : fn var State Inputs :=
    Fn (fun s => quartz_eexpr:(let c := #s .1 in return (#c..x1, #c..scalar))).
  Definition coordinates {var} : fn var State (Pair Inputs Inputs) :=
    Fn (fun s => quartz_eexpr:(let c := #s .1 in return ((#c..x2, #c..z2), (#c..x3, #c..z3)))).

  Fixpoint run (n : nat) (s : State) : State :=
    match n with O => s | S n => run n (fn.interp tick s) end.

  Lemma init_control input :
    fn.interp public_control (fn.interp init input) =
    (bits.of_Z 4 0, (bits.of_Z 8 254, bits.of_Z 5 0)).
  Proof. reflexivity. Qed.

  Lemma init_coordinates input :
    fn.interp coordinates (fn.interp init input) =
    ((bits.of_Z 255 1, bits.of_Z 255 0), (fst input, bits.of_Z 255 1)).
  Proof. reflexivity. Qed.

  Lemma init_persistent input : fn.interp persistent (fn.interp init input) = input.
  Proof. destruct input; reflexivity. Qed.

  Lemma work_core s : snd (fn.interp work s) = fn.interp Core.tick (snd s).
  Proof. reflexivity. Qed.

  Lemma collect_coordinates s :
    fn.interp coordinates (fn.interp collect s) = fn.interp Core.output (snd s).
  Proof. reflexivity. Qed.

  Lemma prep_persistent s : fn.interp persistent (fn.interp prep s) = fn.interp persistent s.
  Proof. reflexivity. Qed.
  Lemma work_persistent s : fn.interp persistent (fn.interp work s) = fn.interp persistent s.
  Proof. reflexivity. Qed.
  Lemma collect_persistent s : fn.interp persistent (fn.interp collect s) = fn.interp persistent s.
  Proof. reflexivity. Qed.

  Lemma final_swap_persistent s :
    fn.interp persistent (fn.interp final_swap s) = fn.interp persistent s.
  Proof. reflexivity. Qed.

  Definition branch (p : bits 4) (n : Z) : bool :=
    Zmod.nonzero (Zmod.embed_bool (Zmod.eqb p (bits.of_Z 4 n))).

  Lemma tick_interp s :
    fn.interp tick s =
    let p := fst (fn.interp public_control s) in
    if branch p 0 then fn.interp prep s else
    if branch p 1 then fn.interp work s else
    if branch p 2 then fn.interp collect s else
    if branch p 3 then fn.interp final_swap s else
    if branch p 4 then fn.interp affine_square s else
    if branch p 5 then fn.interp affine_multiply s else
    if branch p 6 then fn.interp affine_finish s else s.
  Proof. reflexivity. Qed.

  Theorem tick_persistent s : fn.interp persistent (fn.interp tick s) = fn.interp persistent s.
  Proof.
    rewrite tick_interp. cbv zeta.
    destruct (branch _ 0); [apply prep_persistent|].
    destruct (branch _ 1); [apply work_persistent|].
    destruct (branch _ 2); [apply collect_persistent|].
    destruct (branch _ 3); [apply final_swap_persistent|].
    destruct (branch _ 4); [reflexivity|].
    destruct (branch _ 5); [reflexivity|].
    destruct (branch _ 6); reflexivity.
  Qed.

  Theorem run_persistent n s : fn.interp persistent (run n s) = fn.interp persistent s.
  Proof.
    revert s. induction n; intros s; cbn [run]; [reflexivity|].
    rewrite IHn, tick_persistent. reflexivity.
  Qed.

  Definition next_control (c : bits 4 * (bits 8 * bits 5)) :=
    let '(p,(i,e)) := c in
    if branch p 0 then (bits.of_Z 4 1,(i,bits.of_Z 5 0)) else
    if branch p 1 then
      (if Zmod.nonzero (Zmod.embed_bool (Zmod.eqb e (bits.of_Z 5 17)))
       then bits.of_Z 4 2 else bits.of_Z 4 1, (i,Zmod.add e (bits.of_Z 5 1))) else
    if branch p 2 then
      let last := Zmod.nonzero (Zmod.embed_bool (Zmod.eqb i (bits.of_Z 8 0))) in
      (if last then bits.of_Z 4 3 else bits.of_Z 4 0,
       (if last then i else Zmod.sub i (bits.of_Z 8 1),e))
    else if branch p 3 then (bits.of_Z 4 4,(bits.of_Z 8 254,e))
    else if branch p 4 then (bits.of_Z 4 5,(i,e))
    else if branch p 5 then
      let last := Zmod.nonzero (Zmod.embed_bool (Zmod.eqb i (bits.of_Z 8 0))) in
      (if last then bits.of_Z 4 6 else bits.of_Z 4 4,
       (if last then i else Zmod.sub i (bits.of_Z 8 1),e))
    else if branch p 6 then (bits.of_Z 4 7,(i,e)) else c.

  Lemma tick_control s :
    fn.interp public_control (fn.interp tick s) = next_control (fn.interp public_control s).
  Proof.
    rewrite tick_interp. unfold next_control.
    destruct (fn.interp public_control s) as [p [i e]] eqn:E. cbn [fst snd].
    destruct (branch p 0); [|destruct (branch p 1)]; [| |destruct (branch p 2)];
      try (change (fn.interp public_control s = (p,(i,e))) in E; inversion E; reflexivity).
    destruct (branch p 3); [|destruct (branch p 4)]; [| |destruct (branch p 5)];
      try (change (fn.interp public_control s = (p,(i,e))) in E; inversion E; reflexivity).
    destruct (branch p 6);
      change (fn.interp public_control s = (p,(i,e))) in E;
      inversion E; reflexivity.
  Qed.

  Theorem tick_control_independent s t :
    fn.interp public_control s = fn.interp public_control t ->
    fn.interp public_control (fn.interp tick s) = fn.interp public_control (fn.interp tick t).
  Proof. intro H. rewrite !tick_control, H. reflexivity. Qed.

  Definition selected_bit (c : control) : bits 1 :=
    Zmod.firstn 1 (Zmod.skipn 0
      (Zmod.sru c.(scalar) (Zmod.unsigned (bits.of_Z 255 (Zmod.unsigned c.(index)))))).

  Definition prepared_input (c : control) : Core.Inputs :=
    let swap := Zmod.nonzero (Zmod.xor c.(prev) (selected_bit c)) in
    Core.input_rep {| Core.in_x1 := c.(x1);
      Core.in_x2 := if swap then c.(x3) else c.(x2);
      Core.in_z2 := if swap then c.(z3) else c.(z2);
      Core.in_x3 := if swap then c.(x2) else c.(x3);
      Core.in_z3 := if swap then c.(z2) else c.(z3) |}.

  Lemma prep_core c engine :
    snd (fn.interp prep (rep c, engine)) = fn.interp Core.start (prepared_input c).
  Proof. reflexivity. Qed.

  Definition previous {var} : fn var State Bool :=
    Fn (fun s => quartz_eexpr:(let c := #s .1 in return #c..prev)).

  Lemma prep_previous c engine :
    fn.interp previous (fn.interp prep (rep c,engine)) = selected_bit c.
  Proof. reflexivity. Qed.

  Theorem run_control_independent n s t :
    fn.interp public_control s = fn.interp public_control t ->
    fn.interp public_control (run n s) = fn.interp public_control (run n t).
  Proof.
    revert s t. induction n; intros s t H; cbn [run]; [exact H|].
    apply IHn, tick_control_independent, H.
  Qed.

  (* Opaque core functions keep schedule proofs separate from field arithmetic. *)
  Local Opaque Core.tick Core.start Core.output.

  Lemma eighteen_ticks_core s :
    snd (run 18 (fn.interp prep s)) = Core.run 18 (snd (fn.interp prep s)).
  Proof. reflexivity. Qed.

  Lemma eighteen_ticks_control s :
    fn.interp public_control (run 18 (fn.interp prep s)) =
    (bits.of_Z 4 2, (fst (snd (fn.interp public_control s)), bits.of_Z 5 18)).
  Proof. reflexivity. Qed.

  Lemma run_succ n s : run (S n) s = fn.interp tick (run n s).
  Proof. revert s. induction n; intros s; cbn [run]; [reflexivity|apply IHn]. Qed.

  Lemma collect_tick s :
    fst (fn.interp public_control s) = bits.of_Z 4 2 ->
    fn.interp tick s = fn.interp collect s.
  Proof. intro H. rewrite tick_interp, H. reflexivity. Qed.

  Theorem one_iteration_output s :
    fn.interp coordinates (run 19 (fn.interp prep s)) =
    fn.interp Core.output (Core.run 18 (snd (fn.interp prep s))).
  Proof.
    rewrite run_succ, collect_tick.
    - rewrite collect_coordinates, eighteen_ticks_core. reflexivity.
    - rewrite eighteen_ticks_control. reflexivity.
  Qed.

  Theorem one_iteration_control s :
    fn.interp public_control (run 19 (fn.interp prep s)) =
    next_control (bits.of_Z 4 2, (fst (snd (fn.interp public_control s)), bits.of_Z 5 18)).
  Proof.
    rewrite run_succ, tick_control, eighteen_ticks_control. reflexivity.
  Qed.

  Lemma init_tick input : fn.interp tick (fn.interp init input) = fn.interp prep (fn.interp init input).
  Proof. rewrite tick_interp, init_control. reflexivity. Qed.

  Lemma run_first n s : run (S n) s = run n (fn.interp tick s).
  Proof. reflexivity. Qed.

  Theorem initialized_twenty_ticks input :
    fn.interp public_control (run 20 (fn.interp init input)) =
    (bits.of_Z 4 0, (bits.of_Z 8 253, bits.of_Z 5 18)).
  Proof.
    rewrite (run_first 19).
    rewrite init_tick, one_iteration_control, init_control. reflexivity.
  Qed.

  Theorem done_stutters s :
    fst (fn.interp public_control s) = bits.of_Z 4 7 -> fn.interp tick s = s.
  Proof. intro H. rewrite tick_interp, H. reflexivity. Qed.

  (* The hypothesis identifies the prepared, swapped input. The existing
     arithmetic theorem then supplies the mathematical step without any new
     field implementation or an atomic run inside the DSL. *)
  Theorem one_iteration_refines_math s a b c d e :
    snd (fn.interp prep s) = Core.initial a b c d e ->
    0 <= a < Core.prime -> 0 <= b < Core.prime -> 0 <= c < Core.prime ->
    0 <= d < Core.prime -> 0 <= e < Core.prime ->
    (let '((x,z),(y,w)) := fn.interp coordinates (run 19 (fn.interp prep s)) in
     ((Zmod.unsigned x,Zmod.unsigned z),(Zmod.unsigned y,Zmod.unsigned w))) =
    AcceleratorLadderBridge.mathematical_step a b c d e.
  Proof.
    intros H Ha Hb Hc Hd He. rewrite one_iteration_output, H.
    apply AcceleratorLadderBridge.ladder_step_matches_math; assumption.
  Qed.
  Local Transparent Core.start Core.output.

  Definition completed_control (c : control) (out : (bits 255 * bits 255) * (bits 255 * bits 255)) :=
    let '((a,b),(d,e)) := out in
    let last := Zmod.nonzero (Zmod.embed_bool (Zmod.eqb c.(index) (bits.of_Z 8 0))) in
    {| stage := if last then bits.of_Z 4 3 else bits.of_Z 4 0;
       index := if last then c.(index) else Zmod.sub c.(index) (bits.of_Z 8 1);
       elapsed := bits.of_Z 5 18; x1 := c.(x1); scalar := c.(scalar);
       prev := selected_bit c; x2 := a; z2 := b; x3 := d; z3 := e; acc := c.(acc) |}.

  Lemma eighteen_ticks_state c engine :
    run 18 (fn.interp prep (rep c,engine)) =
    (rep {| stage := bits.of_Z 4 2; index := c.(index); elapsed := bits.of_Z 5 18;
      x1 := c.(x1); scalar := c.(scalar); prev := selected_bit c;
      x2 := c.(x2); z2 := c.(z2); x3 := c.(x3); z3 := c.(z3); acc := c.(acc) |},
      Core.run 18 (fn.interp Core.start (prepared_input c))).
  Proof. reflexivity. Qed.

  Lemma iteration_state c engine :
    c.(stage) = bits.of_Z 4 0 ->
    run 20 (rep c,engine) =
    let engine' := Core.run 18 (fn.interp Core.start (prepared_input c)) in
    (rep (completed_control c (fn.interp Core.output engine')),engine').
  Proof.
    intro H. rewrite (run_first 19), tick_interp.
    change (fst (fn.interp public_control (rep c,engine))) with c.(stage).
    rewrite H. change (run 19 (fn.interp prep (rep c,engine)) =
      let engine' := Core.run 18 (fn.interp Core.start (prepared_input c)) in
      (rep (completed_control c (fn.interp Core.output engine')),engine')).
    rewrite run_succ, collect_tick by (rewrite eighteen_ticks_control; reflexivity).
    rewrite eighteen_ticks_state. reflexivity.
  Qed.

  Definition regs := (Z * Z * Z * Z)%type.
  Definition canonical (r : regs) : Prop :=
    let '(a,b,c,d) := r in
    0 <= a < Core.prime /\ 0 <= b < Core.prime /\
    0 <= c < Core.prime /\ 0 <= d < Core.prime.

  Definition words (r : regs) : (bits 255 * bits 255) * (bits 255 * bits 255) :=
    let '(a,b,c,d) := r in
    ((bits.of_Z 255 a,bits.of_Z 255 b),(bits.of_Z 255 c,bits.of_Z 255 d)).

  Definition boundary (p i : Z) (e : bits 5) (u k : Z) (r : regs) (v : bool) : control :=
    let '(a,b,c,d) := r in
    {| stage := bits.of_Z 4 p; index := bits.of_Z 8 i; elapsed := e;
       x1 := bits.of_Z 255 u; scalar := bits.of_Z 255 k; prev := Zmod.embed_bool v;
       x2 := bits.of_Z 255 a; z2 := bits.of_Z 255 b;
       x3 := bits.of_Z 255 c; z3 := bits.of_Z 255 d; acc := bits.of_Z 255 1 |}.

  Lemma selected_bit_boundary p i e u k r v :
    0 <= i < 255 -> 0 <= k < 2^255 ->
    selected_bit (boundary p i e u k r v) = Zmod.embed_bool (Z.testbit k i).
  Proof.
    intros Hi Hk. destruct r as [[[a b] c] d]. unfold selected_bit, boundary.
    cbn [index scalar]. apply Zmod.unsigned_inj.
    rewrite bits.unsigned_firstn, bits.unsigned_skipn, Z.div_1_r by lia.
    rewrite (bits.unsigned_of_Z_small (n := 8) i) by lia.
    rewrite !bits.unsigned_of_Z_small by lia.
    rewrite Zmod.unsigned_sru, bits.unsigned_of_Z_small, Z.shiftr_div_pow2 by lia.
    change (k / 2^i mod 2 = Zmod.unsigned (Zmod.embed_bool (Z.testbit k i))).
    pose proof (Z.testbit_spec' k i ltac:(lia)) as H.
    destruct (Z.testbit k i); cbn in H |- *; lia.
  Qed.

  Lemma step_canonical u a b c d : canonical (LadderStep Core.prime 121666 u a b c d).
  Proof.
    unfold canonical, LadderStep.
    cbv zeta. unfold fsq, fmul. repeat split;
      apply Z.mod_pos_bound; exact AcceleratorCorrectness.prime_positive.
  Qed.

  Lemma cswap_step_canonical u bit v r :
    canonical (fst (MontLadderCSwap_step Core.prime 121666 u bit v r)).
  Proof.
    destruct r as [[[a b] c] d]. unfold MontLadderCSwap_step, CSwap.
    destruct (xorb bit v); apply step_canonical.
  Qed.

  Lemma core_words_correct u a b c d :
    0 <= u < Core.prime -> canonical (a,b,c,d) ->
    fn.interp Core.output (Core.run 18 (Core.initial u a b c d)) =
    words (LadderStep Core.prime 121666 u a b c d).
  Proof.
    intros Hu [Ha [Hb [Hc Hd]]].
    pose proof (AcceleratorLadderBridge.ladder_step_matches_math u a b c d Hu Ha Hb Hc Hd) as H.
    unfold AcceleratorCorrectness.output_Z, AcceleratorLadderBridge.mathematical_step in H.
    destruct (fn.interp Core.output (Core.run 18 (Core.initial u a b c d))) as [[wa wb] [wc wd]].
    destruct (LadderStep Core.prime 121666 u a b c d) as [[[a' b'] c'] d'].
    inversion H; subst. unfold words. rewrite !Zmod.of_Z_unsigned. reflexivity.
  Qed.

  Definition swapped (bit v : bool) (r : regs) : regs :=
    let '(a,b,c,d) := r in CSwap a b c d (xorb bit v).

  Lemma swapped_canonical bit v r : canonical r -> canonical (swapped bit v r).
  Proof.
    destruct r as [[[a b] c] d]. unfold swapped, CSwap, canonical.
    destruct (xorb bit v); intuition.
  Qed.

  Lemma prepared_boundary i e u k r v :
    0 <= i < 255 -> 0 <= k < 2^255 ->
    fn.interp Core.start (prepared_input (boundary 0 i e u k r v)) =
    let '(a,b,c,d) := swapped (Z.testbit k i) v r in Core.initial u a b c d.
  Proof.
    intros Hi Hk. unfold prepared_input.
    rewrite selected_bit_boundary by assumption.
    destruct r as [[[a b] c] d]. destruct v, (Z.testbit k i); reflexivity.
  Qed.

  Lemma index_zero_test m : (m < 255)%nat ->
    Zmod.nonzero (Zmod.embed_bool (Zmod.eqb (bits.of_Z 8 (Z.of_nat m)) (bits.of_Z 8 0))) =
    match m with O => true | S _ => false end.
  Proof.
    intro H. rewrite Zmod.nonzero_bool. unfold Zmod.eqb.
    rewrite !bits.unsigned_of_Z_small by lia.
    destruct m; [reflexivity|apply Z.eqb_neq; lia].
  Qed.

  Lemma index_predecessor m :
    Zmod.sub (bits.of_Z 8 (Z.of_nat (S m))) (bits.of_Z 8 1) = bits.of_Z 8 (Z.of_nat m).
  Proof.
    rewrite <- Zmod.of_Z_sub. f_equal. lia.
  Qed.

  Lemma completed_boundary m e u k r v r' :
    (m < 255)%nat -> 0 <= k < 2^255 ->
    completed_control (boundary 0 (Z.of_nat m) e u k r v) (words r') =
    boundary (match m with O => 3 | S _ => 0 end) (Z.of_nat (Nat.pred m))
      (bits.of_Z 5 18) u k r' (bit_i k m).
  Proof.
    intros Hm Hk. unfold completed_control.
    rewrite selected_bit_boundary by (try assumption; lia).
    destruct r as [[[a b] c] d], r' as [[[a' b'] c'] d'].
    cbn [words boundary index x1 scalar].
    rewrite index_zero_test by assumption.
    destruct m; [reflexivity|]. rewrite index_predecessor. reflexivity.
  Qed.

  Theorem twenty_ticks_recurrence m e u k r v engine :
    (m < 255)%nat -> 0 <= u < Core.prime -> 0 <= k < 2^255 -> canonical r ->
    let st' := MontLadderCSwap_step Core.prime 121666 u (bit_i k m) v r in
    canonical (fst st') /\ exists engine',
      run 20 (rep (boundary 0 (Z.of_nat m) e u k r v),engine) =
      (rep (boundary (match m with O => 3 | S _ => 0 end) (Z.of_nat (Nat.pred m))
        (bits.of_Z 5 18) u k (fst st') (snd st')),engine').
  Proof.
    intros Hm Hu Hk Hr. split; [apply cswap_step_canonical|].
    rewrite iteration_state by (destruct r as [[[a b] c] d]; reflexivity).
    rewrite prepared_boundary by (try assumption; lia).
    pose proof (swapped_canonical (bit_i k m) v r Hr) as Hswap.
    unfold MontLadderCSwap_step.
    destruct r as [[[a b] c] d].
    change (canonical (CSwap a b c d (xorb (bit_i k m) v))) in Hswap.
    unfold swapped. fold (bit_i k m).
    destruct (CSwap a b c d (xorb (bit_i k m) v)) as [[[a' b'] c'] d'].
    rewrite core_words_correct by assumption.
    eexists. rewrite completed_boundary by assumption.
    destruct (LadderStep Core.prime 121666 u a' b' c' d') as [[[w x] y] z].
    reflexivity.
  Qed.

  Lemma run_add n m s : run (n + m) s = run m (run n s).
  Proof.
    revert s. induction n; intros s; cbn [Nat.add run]; [reflexivity|apply IHn].
  Qed.

  Lemma math_loop_succ m u k r v :
    MontLadderCSwap_rec Core.prime 121666 (S m) u k (r,v) =
    MontLadderCSwap_rec Core.prime 121666 m u k
      (MontLadderCSwap_step Core.prime 121666 u (bit_i k m) v r).
  Proof. reflexivity. Qed.

  Theorem projective_loop m e u k r v engine :
    (m < 255)%nat -> 0 <= u < Core.prime -> 0 <= k < 2^255 -> canonical r ->
    let st' := MontLadderCSwap_rec Core.prime 121666 (S m) u k (r,v) in
    canonical (fst st') /\ exists engine',
      run (20 * S m) (rep (boundary 0 (Z.of_nat m) e u k r v),engine) =
      (rep (boundary 3 0 (bits.of_Z 5 18) u k (fst st') (snd st')),engine').
  Proof.
    revert e r v engine. induction m as [|m IH]; intros e r v engine Hm Hu Hk Hr.
    - exact (twenty_ticks_recurrence 0 e u k r v engine Hm Hu Hk Hr).
    - pose proof (twenty_ticks_recurrence (S m) e u k r v engine Hm Hu Hk Hr) as Hstep.
      destruct (MontLadderCSwap_step Core.prime 121666 u (bit_i k (S m)) v r)
        as [r' v'] eqn:E.
      destruct Hstep as [Hcan [engine' Hrun]]. cbn [fst snd Nat.pred] in Hrun, Hcan.
      pose proof (IH (bits.of_Z 5 18) r' v' engine' ltac:(lia) Hu Hk Hcan) as Hrest.
      rewrite (math_loop_succ (S m)), E.
      change (canonical (fst (MontLadderCSwap_rec Core.prime 121666 (S m) u k (r',v'))) /\
        exists engine'', run (20 * S (S m))
          (rep (boundary 0 (Z.of_nat (S m)) e u k r v),engine) =
          (rep (boundary 3 0 (bits.of_Z 5 18) u k
            (fst (MontLadderCSwap_rec Core.prime 121666 (S m) u k (r',v')))
            (snd (MontLadderCSwap_rec Core.prime 121666 (S m) u k (r',v')))),engine'')).
      replace (20 * S (S m))%nat with (20 + 20 * S m)%nat by lia.
      rewrite run_add, Hrun. exact Hrest.
  Qed.

  Lemma init_boundary u k :
    fn.interp init (bits.of_Z 255 u,bits.of_Z 255 k) =
    (rep (boundary 0 254 (bits.of_Z 5 0) u k (1,0,u,1) false),
      fn.interp Core.reset (type.default Core.State)).
  Proof. reflexivity. Qed.

  Theorem initialized_5100_ticks u k :
    0 <= u < Core.prime -> 0 <= k < 2^255 ->
    let st' := MontLadderCSwap_rec Core.prime 121666 255 u k ((1,0,u,1),false) in
    canonical (fst st') /\ exists engine',
      run 5100 (fn.interp init (bits.of_Z 255 u,bits.of_Z 255 k)) =
      (rep (boundary 3 0 (bits.of_Z 5 18) u k (fst st') (snd st')),engine').
  Proof.
    intros Hu Hk. rewrite init_boundary.
    apply (projective_loop 254); try assumption; try lia.
    unfold canonical, Core.prime in *. lia.
  Qed.

  Definition final_regs (st : regs * bool) : regs :=
    let '(r,v) := st in let '(a,b,c,d) := r in CSwap a b c d v.

  Lemma final_regs_canonical r v : canonical r -> canonical (final_regs (r,v)).
  Proof.
    destruct r as [[[a b] c] d]. destruct v; unfold canonical; cbn [final_regs CSwap]; intuition.
  Qed.

  Lemma final_swap_boundary p i e u k r v engine :
    fn.interp final_swap (rep (boundary p i e u k r v),engine) =
    (rep (boundary 4 254 e u k (final_regs (r,v)) v),engine).
  Proof. destruct r as [[[a b] c] d], v; reflexivity. Qed.

  Lemma final_swap_tick s :
    fst (fn.interp public_control s) = bits.of_Z 4 3 ->
    fn.interp tick s = fn.interp final_swap s.
  Proof. intro H. rewrite tick_interp, H. reflexivity. Qed.

  Theorem initialized_5101_ticks u k :
    0 <= u < Core.prime -> 0 <= k < 2^255 ->
    let st' := MontLadderCSwap_rec Core.prime 121666 255 u k ((1,0,u,1),false) in
    canonical (final_regs st') /\ exists engine',
      run 5101 (fn.interp init (bits.of_Z 255 u,bits.of_Z 255 k)) =
      (rep (boundary 4 254 (bits.of_Z 5 18) u k (final_regs st') (snd st')),engine').
  Proof.
    intros Hu Hk. pose proof (initialized_5100_ticks u k Hu Hk) as H.
    destruct (MontLadderCSwap_rec Core.prime 121666 255 u k ((1,0,u,1),false))
      as [r v] eqn:E.
    destruct H as [Hcan [engine Hrun]]. split; [apply final_regs_canonical, Hcan|].
    exists engine. rewrite (run_succ 5100), Hrun, final_swap_tick.
    - apply final_swap_boundary.
    - destruct r as [[[a b] c] d]. reflexivity.
  Qed.

  Definition coordinates_Z (s : State) : regs :=
    let '((a,b),(c,d)) := fn.interp coordinates s in
    (Zmod.unsigned a,Zmod.unsigned b,Zmod.unsigned c,Zmod.unsigned d).

  Lemma boundary_coordinates p i e u k r v engine :
    canonical r -> coordinates_Z (rep (boundary p i e u k r v),engine) = r.
  Proof.
    destruct r as [[[a b] c] d]. intros [Ha [Hb [Hc Hd]]].
    unfold coordinates_Z. change
      ((Zmod.unsigned (bits.of_Z 255 a),Zmod.unsigned (bits.of_Z 255 b),
        Zmod.unsigned (bits.of_Z 255 c),Zmod.unsigned (bits.of_Z 255 d)) = (a,b,c,d)).
    rewrite !bits.unsigned_of_Z_small by (unfold Core.prime in *; lia). reflexivity.
  Qed.

  Definition projective_output (s : State) : Z * Z :=
    let '(a,b,_,_) := coordinates_Z s in (a,b).

  Theorem projective_refines_cswap u k :
    0 <= u < Core.prime -> 0 <= k < 2^255 ->
    let s := run 5101 (fn.interp init (bits.of_Z 255 u,bits.of_Z 255 k)) in
    fn.interp public_control s = (bits.of_Z 4 4,(bits.of_Z 8 254,bits.of_Z 5 18)) /\
    canonical (coordinates_Z s) /\
    projective_output s = MontLadderCSwap Core.prime 121666 255 u k.
  Proof.
    intros Hu Hk. pose proof (initialized_5101_ticks u k Hu Hk) as H.
    destruct H as [Hcan [engine Hrun]]. cbv zeta. rewrite Hrun.
    unfold projective_output. rewrite boundary_coordinates by exact Hcan.
    split.
    - destruct (MontLadderCSwap_rec Core.prime 121666 255 u k ((1,0,u,1),false))
        as [[[[a b] c] d] v]. destruct v; reflexivity.
    - split; [exact Hcan|]. unfold MontLadderCSwap, final_regs.
      destruct (MontLadderCSwap_rec Core.prime 121666 255 u k ((1,0,u,1),false))
        as [[[[a b] c] d] v]. destruct v; reflexivity.
  Qed.

  Corollary projective_refines_ladder u k :
    0 <= u < Core.prime -> 0 <= k < 2^255 ->
    projective_output (run 5101 (fn.interp init (bits.of_Z 255 u,bits.of_Z 255 k))) =
    MontLadder Core.prime 121666 255 u k.
  Proof.
    intros Hu Hk. rewrite <- CSwap_eq.
    exact (proj2 (proj2 (projective_refines_cswap u k Hu Hk))).
  Qed.

  Theorem fixed_projective_control input :
    fn.interp public_control (run 5101 (fn.interp init input)) =
    (bits.of_Z 4 4,(bits.of_Z 8 254,bits.of_Z 5 18)).
  Proof.
    pose proof (projective_refines_cswap 9 0 ltac:(unfold Core.prime; lia) ltac:(lia)) as H.
    rewrite (run_control_independent 5101 (fn.interp init input)
      (fn.interp init (bits.of_Z 255 9,bits.of_Z 255 0))) by (rewrite !init_control; reflexivity).
    exact (proj1 H).
  Qed.

  Theorem projective_preserves_request input :
    fn.interp persistent (run 5101 (fn.interp init input)) = input.
  Proof. rewrite run_persistent, init_persistent. reflexivity. Qed.

  (* These tests keep all 255 scalar bits; no field execution is expanded. *)
  Example scalar_zero_full_width :
    projective_output (run 5101 (fn.interp init (bits.of_Z 255 9,bits.of_Z 255 0))) =
    MontLadderCSwap Core.prime 121666 255 9 0.
  Proof.
    exact (proj2 (proj2 (projective_refines_cswap 9 0 ltac:(unfold Core.prime; lia) ltac:(lia)))).
  Qed.

  Example scalar_one_full_width :
    projective_output (run 5101 (fn.interp init (bits.of_Z 255 9,bits.of_Z 255 1))) =
    MontLadderCSwap Core.prime 121666 255 9 1.
  Proof.
    exact (proj2 (proj2 (projective_refines_cswap 9 1 ltac:(unfold Core.prime; lia) ltac:(lia)))).
  Qed.

  Example scalar_one_msb :
    selected_bit (boundary 0 254 (bits.of_Z 5 0) 9 1 (1,0,9,1) false) = Zmod.embed_bool false.
  Proof. rewrite selected_bit_boundary by lia. reflexivity. Qed.

  Example scalar_one_lsb :
    selected_bit (boundary 0 0 (bits.of_Z 5 18) 9 1 (1,0,9,1) false) = Zmod.embed_bool true.
  Proof. rewrite selected_bit_boundary by lia. reflexivity. Qed.
  Definition affine_control (c : control) (p i : Z) (a : bits 255) : control :=
    {| stage := bits.of_Z 4 p; index := bits.of_Z 8 i; elapsed := c.(elapsed);
       x1 := c.(x1); scalar := c.(scalar); prev := c.(prev);
       x2 := c.(x2); z2 := c.(z2); x3 := c.(x3); z3 := c.(z3); acc := a |}.

  Definition mul_word (a b : bits 255) : bits 255 :=
    fn.interp (Core.arithmetic Core.Mul) (a,b).

  Definition exponent_bit (i : bits 8) : bits 1 :=
    Zmod.firstn 1 (Zmod.skipn 0 (Zmod.sru (bits.of_Z 255 inverse_exponent)
      (Zmod.unsigned (bits.of_Z 255 (Zmod.unsigned i))))).

  Lemma exponent_bit_correct i : 0 <= i < 255 ->
    exponent_bit (bits.of_Z 8 i) = Zmod.embed_bool (Z.testbit inverse_exponent i).
  Proof.
    intro Hi. change (selected_bit (boundary 0 i (bits.of_Z 5 0) 0 inverse_exponent
      (0,0,0,0) false) = Zmod.embed_bool (Z.testbit inverse_exponent i)).
    apply selected_bit_boundary; [exact Hi|unfold inverse_exponent, Core.prime; lia].
  Qed.

  Local Opaque Core.arithmetic.

  Lemma affine_square_interp c i a engine :
    fn.interp affine_square (rep (affine_control c 4 i a),engine) =
    (rep (affine_control c 5 i (mul_word a a)),engine).
  Proof. reflexivity. Qed.

  Lemma affine_multiply_interp c m a engine : (m < 255)%nat ->
    fn.interp affine_multiply (rep (affine_control c 5 (Z.of_nat m) a),engine) =
    (rep (affine_control c (match m with O => 6 | S _ => 4 end) (Z.of_nat (Nat.pred m))
      (mul_word a (if bit_i inverse_exponent m then c.(z2) else bits.of_Z 255 1))),engine).
  Proof.
    intro Hm.
    change (fn.interp affine_multiply (rep (affine_control c 5 (Z.of_nat m) a),engine)) with
      (rep {| stage := if Zmod.nonzero (Zmod.embed_bool
          (Zmod.eqb (bits.of_Z 8 (Z.of_nat m)) (bits.of_Z 8 0))) then bits.of_Z 4 6 else bits.of_Z 4 4;
        index := if Zmod.nonzero (Zmod.embed_bool
          (Zmod.eqb (bits.of_Z 8 (Z.of_nat m)) (bits.of_Z 8 0))) then bits.of_Z 8 (Z.of_nat m)
          else Zmod.sub (bits.of_Z 8 (Z.of_nat m)) (bits.of_Z 8 1);
        elapsed := c.(elapsed); x1 := c.(x1); scalar := c.(scalar); prev := c.(prev);
        x2 := c.(x2); z2 := c.(z2); x3 := c.(x3); z3 := c.(z3);
        acc := mul_word a (if Zmod.nonzero (exponent_bit (bits.of_Z 8 (Z.of_nat m)))
          then c.(z2) else bits.of_Z 255 1) |},engine).
    rewrite exponent_bit_correct by lia. rewrite index_zero_test by assumption.
    rewrite Zmod.nonzero_bool.
    destruct m; [reflexivity|]. rewrite index_predecessor. reflexivity.
  Qed.

  Lemma affine_finish_interp c a engine :
    fn.interp affine_finish (rep (affine_control c 6 0 a),engine) =
    (rep (affine_control c 7 0 (mul_word c.(x2) a)),engine).
  Proof. reflexivity. Qed.

  Lemma affine_square_tick s : fst (fn.interp public_control s) = bits.of_Z 4 4 ->
    fn.interp tick s = fn.interp affine_square s.
  Proof. intro H. rewrite tick_interp, H. reflexivity. Qed.

  Lemma affine_multiply_tick s : fst (fn.interp public_control s) = bits.of_Z 4 5 ->
    fn.interp tick s = fn.interp affine_multiply s.
  Proof. intro H. rewrite tick_interp, H. reflexivity. Qed.

  Lemma affine_finish_tick s : fst (fn.interp public_control s) = bits.of_Z 4 6 ->
    fn.interp tick s = fn.interp affine_finish s.
  Proof. intro H. rewrite tick_interp, H. reflexivity. Qed.

  Lemma affine_two_ticks c m a engine : (m < 255)%nat ->
    run 2 (rep (affine_control c 4 (Z.of_nat m) a),engine) =
    (rep (affine_control c (match m with O => 6 | S _ => 4 end) (Z.of_nat (Nat.pred m))
      (mul_word (mul_word a a) (if bit_i inverse_exponent m then c.(z2) else bits.of_Z 255 1))),engine).
  Proof.
    intro Hm. rewrite (run_first 1), affine_square_tick by reflexivity.
    rewrite affine_square_interp, (run_first 0). cbn [run].
    rewrite affine_multiply_tick by reflexivity. apply affine_multiply_interp, Hm.
  Qed.

  Definition exponent_step m (z a : bits 255) : bits 255 :=
    mul_word (mul_word a a) (if bit_i inverse_exponent m then z else bits.of_Z 255 1).

  Fixpoint descending {A : Type} (step : nat -> A -> A) (m : nat) (a : A) : A :=
    match m with O => a | S m => descending step m (step m a) end.

  Lemma descending_succ {A : Type} step m (a : A) :
    descending step (S m) a = descending step m (step m a).
  Proof. reflexivity. Qed.

  Definition exponent_words (m : nat) (z a : bits 255) : bits 255 :=
    descending (fun m a => exponent_step m z a) m a.

  Local Opaque mul_word inverse_exponent.

  Lemma exponent_words_succ m z a : exponent_words (S m) z a =
    exponent_words m z (exponent_step m z a).
  Proof. exact (descending_succ (fun m a => exponent_step m z a) m a). Qed.

  Theorem affine_word_loop m c a engine : (m < 255)%nat ->
    run (2 * S m) (rep (affine_control c 4 (Z.of_nat m) a),engine) =
    (rep (affine_control c 6 0 (exponent_words (S m) c.(z2) a)),engine).
  Proof.
    revert a. induction m as [|m IH]; intros a Hm.
    - apply affine_two_ticks, Hm.
    - replace (2 * S (S m))%nat with (2 + 2 * S m)%nat by lia.
      rewrite run_add, affine_two_ticks by exact Hm.
      cbn [Nat.pred]. rewrite IH by lia. rewrite (exponent_words_succ (S m)). reflexivity.
  Qed.

  Local Transparent mul_word.

  Lemma mul_word_unsigned a b :
    Zmod.unsigned (mul_word a b) = (Zmod.unsigned a * Zmod.unsigned b) mod Core.prime.
  Proof. unfold mul_word. apply AcceleratorCorrectness.arithmetic_correct. Qed.

  Lemma mul_word_canonical a b : 0 <= Zmod.unsigned (mul_word a b) < Core.prime.
  Proof. unfold mul_word. apply AcceleratorCorrectness.arithmetic_canonical. Qed.

  Local Opaque mul_word.

  Lemma mul_word_encode a b :
    0 <= a < Core.prime -> 0 <= b < Core.prime ->
    mul_word (bits.of_Z 255 a) (bits.of_Z 255 b) = bits.of_Z 255 ((a*b) mod Core.prime).
  Proof.
    intros Ha Hb. apply Zmod.unsigned_inj. rewrite mul_word_unsigned.
    rewrite !bits.unsigned_of_Z_small by
      (pose proof (Z.mod_pos_bound (a*b) Core.prime AcceleratorCorrectness.prime_positive);
       unfold Core.prime in *; lia).
    reflexivity.
  Qed.

  Lemma word_power_step z prefix (bit : bool) : 0 <= z < Core.prime -> 0 <= prefix ->
    mul_word (mul_word (bits.of_Z 255 (z^prefix mod Core.prime))
                      (bits.of_Z 255 (z^prefix mod Core.prime)))
      (if bit then bits.of_Z 255 z else bits.of_Z 255 1) =
    bits.of_Z 255 (z^(2*prefix + if bit then 1 else 0) mod Core.prime).
  Proof.
    intros Hz Hp.
    pose proof AcceleratorCorrectness.prime_positive as Hprime.
    pose proof (Z.mod_pos_bound (z^prefix) Core.prime Hprime) as Hpow.
    rewrite mul_word_encode by exact Hpow.
    assert (Esquare : ((z^prefix mod Core.prime)*(z^prefix mod Core.prime)) mod Core.prime =
      (z^prefix*z^prefix) mod Core.prime).
    { rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by lia. reflexivity. }
    rewrite Esquare. destruct bit.
    - rewrite mul_word_encode by (try exact Hz; apply Z.mod_pos_bound; exact Hprime).
      rewrite Z.mul_mod_idemp_l by lia. f_equal.
      replace (2*prefix+1) with ((prefix+prefix)+1) by ring.
      rewrite !Z.pow_add_r, Z.pow_1_r by lia. reflexivity.
    - rewrite mul_word_encode by
        (try (apply Z.mod_pos_bound; exact Hprime); unfold Core.prime; lia).
      rewrite Z.mul_1_r, Z.mod_mod by lia. f_equal.
      replace (2*prefix+0) with (prefix+prefix) by ring.
      rewrite Z.pow_add_r by lia. reflexivity.
  Qed.

  Theorem exponent_words_power m z prefix : 0 <= z < Core.prime -> 0 <= prefix ->
    exponent_words m (bits.of_Z 255 z) (bits.of_Z 255 (z^prefix mod Core.prime)) =
    bits.of_Z 255 (z^(ladder_index m inverse_exponent prefix) mod Core.prime).
  Proof.
    revert prefix. induction m as [|m IH]; intros prefix Hz Hp.
    - reflexivity.
    - rewrite exponent_words_succ. unfold exponent_step. cbn [ladder_index].
      rewrite word_power_step by assumption.
      apply IH; [exact Hz|destruct (bit_i inverse_exponent m); lia].
  Qed.

  Local Transparent inverse_exponent.

  Theorem exponent_words_255 z : 0 <= z < Core.prime ->
    exponent_words 255 (bits.of_Z 255 z) (bits.of_Z 255 1) =
    bits.of_Z 255 (z^inverse_exponent mod Core.prime).
  Proof.
    intro Hz.
    replace (bits.of_Z 255 1) with (bits.of_Z 255 (z^0 mod Core.prime)) by
      (rewrite Z.pow_0_r, Z.mod_small; [reflexivity|unfold Core.prime; lia]).
    rewrite exponent_words_power, ladder_index_value by lia.
    rewrite Z.mul_0_l, Z.add_0_l.
    rewrite (Z.mod_small inverse_exponent (2^Z.of_nat 255)) by
      (unfold inverse_exponent, Core.prime; lia). reflexivity.
  Qed.

  Local Opaque exponent_words.

  Theorem affine_511_ticks c engine : 0 <= Zmod.unsigned c.(z2) < Core.prime ->
    run 511 (rep (affine_control c 4 254 (bits.of_Z 255 1)),engine) =
    (rep (affine_control c 7 0
      (mul_word c.(x2) (bits.of_Z 255 (Zmod.unsigned c.(z2)^inverse_exponent mod Core.prime)))),engine).
  Proof.
    intro Hz. rewrite (run_succ 510), (affine_word_loop 254) by lia.
    rewrite affine_finish_tick by reflexivity. rewrite affine_finish_interp.
    replace (c.(z2)) with (bits.of_Z 255 (Zmod.unsigned c.(z2))) at 1 by apply Zmod.of_Z_unsigned.
    rewrite exponent_words_255 by exact Hz. reflexivity.
  Qed.

  Definition affine_mod (r : regs) : Z :=
    let '(x,z,_,_) := r in (x * (z^inverse_exponent mod Core.prime)) mod Core.prime.

  Lemma affine_output_interp c p i a engine :
    fn.interp output (rep (affine_control c p i a),engine) = a.
  Proof. reflexivity. Qed.

  Theorem affine_refines_power u k :
    0 <= u < Core.prime -> 0 <= k < 2^255 ->
    let s := run 5612 (fn.interp init (bits.of_Z 255 u,bits.of_Z 255 k)) in
    fn.interp ready s = Zmod.embed_bool true /\
    0 <= Zmod.unsigned (fn.interp output s) < Core.prime /\
    Zmod.unsigned (fn.interp output s) =
      let '(x,z) := MontLadderCSwap Core.prime 121666 255 u k in
      (x * (z^inverse_exponent mod Core.prime)) mod Core.prime.
  Proof.
    intros Hu Hk. pose proof (initialized_5101_ticks u k Hu Hk) as H.
    destruct H as [Hcan [engine Hrun]]. cbv zeta.
    replace 5612%nat with (5101 + 511)%nat by reflexivity. rewrite run_add, Hrun.
    set (r := final_regs (MontLadderCSwap_rec Core.prime 121666 255 u k ((1,0,u,1),false))) in *.
    set (v := snd (MontLadderCSwap_rec Core.prime 121666 255 u k ((1,0,u,1),false))).
    assert (E : boundary 4 254 (bits.of_Z 5 18) u k r v =
      affine_control (boundary 4 254 (bits.of_Z 5 18) u k r v) 4 254 (bits.of_Z 255 1)).
    { destruct r as [[[a b] c] d]. reflexivity. }
    rewrite E. rewrite affine_511_ticks.
    - split; [reflexivity|]. split; [apply mul_word_canonical|].
      rewrite affine_output_interp, mul_word_unsigned.
      assert (Eout : (let '(a,b,_,_) := r in (a,b)) = MontLadderCSwap Core.prime 121666 255 u k).
      { unfold r, final_regs, MontLadderCSwap.
        destruct (MontLadderCSwap_rec Core.prime 121666 255 u k ((1,0,u,1),false))
          as [[[[a b] c] d] w]. destruct w; reflexivity. }
      rewrite <- Eout. destruct r as [[[a b] c] d]. destruct Hcan as [Ha [Hb [Hc Hd]]].
      cbn [boundary x2 z2].
      rewrite (bits.unsigned_of_Z_small (n := 255) b) by (unfold Core.prime in *; lia).
      rewrite !bits.unsigned_of_Z_small by
        (try (pose proof (Z.mod_pos_bound (b^inverse_exponent) Core.prime
          AcceleratorCorrectness.prime_positive)); unfold Core.prime in *; lia).
      reflexivity.
    - destruct r as [[[a b] c] d]. destruct Hcan as [Ha [Hb [Hc Hd]]].
      cbn [boundary z2]. rewrite bits.unsigned_of_Z_small by (unfold Core.prime in *; lia). exact Hb.
  Qed.

  Lemma ready_public s :
    fn.interp ready s = Zmod.embed_bool (Zmod.eqb (fst (fn.interp public_control s)) (bits.of_Z 4 7)).
  Proof. reflexivity. Qed.

  Theorem ready_after_5612 input :
    fn.interp ready (run 5612 (fn.interp init input)) = Zmod.embed_bool true.
  Proof.
    pose proof (proj1 (affine_refines_power 9 0 ltac:(unfold Core.prime; lia) ltac:(lia))) as H.
    rewrite ready_public in H |- *.
    rewrite (run_control_independent 5612 (fn.interp init input)
      (fn.interp init (bits.of_Z 255 9,bits.of_Z 255 0))) by (rewrite !init_control; reflexivity).
    exact H.
  Qed.

  Theorem affine_preserves_request input :
    fn.interp persistent (run 5612 (fn.interp init input)) = input.
  Proof. rewrite run_persistent, init_persistent. reflexivity. Qed.

  Lemma projective_not_ready input :
    fn.interp ready (run 5101 (fn.interp init input)) = Zmod.embed_bool false.
  Proof. rewrite ready_public, fixed_projective_control. reflexivity. Qed.

  Lemma inverse_zero : 0^inverse_exponent mod Core.prime = 0.
  Proof. rewrite Z.pow_0_l, Z.mod_0_l by (unfold inverse_exponent, Core.prime; lia). reflexivity. Qed.

  Theorem affine_zero_denominator c engine : Zmod.unsigned c.(z2) = 0 ->
    Zmod.unsigned (fn.interp output
      (run 511 (rep (affine_control c 4 254 (bits.of_Z 255 1)),engine))) = 0.
  Proof.
    intro Hz. rewrite affine_511_ticks by (rewrite Hz; unfold Core.prime; lia).
    rewrite affine_output_interp, Hz, inverse_zero, mul_word_unsigned.
    change (Zmod.unsigned c.(x2) * 0 mod Core.prime = 0).
    rewrite Z.mul_0_r, Z.mod_0_l by (unfold Core.prime; lia). reflexivity.
  Qed.

  Example scalar_zero_affine_full_width :
    fn.interp ready (run 5612 (fn.interp init (bits.of_Z 255 9,bits.of_Z 255 0))) = Zmod.embed_bool true.
  Proof. apply ready_after_5612. Qed.

  Example scalar_one_affine_full_width :
    fn.interp ready (run 5612 (fn.interp init (bits.of_Z 255 9,bits.of_Z 255 1))) = Zmod.embed_bool true.
  Proof. apply ready_after_5612. Qed.
End LadderController.

From Crypto Require Import Spec.Curve25519 Arithmetic.PrimeFieldTheorems.
Require Import curve25519_math.

Module LadderControllerCurveBridge.
  Local Notation q := (2^255-19)%positive.

  Lemma inverse_to_Z z :
    F.to_Z (F.inv (F.of_Z q z)) = z^LadderController.inverse_exponent mod LadderAccelerator.prime.
  Proof.
    rewrite (@F.Fq_inv_fermat q Curve25519.prime_p ltac:(vm_compute; reflexivity)).
    rewrite F.of_Z_pow, F.to_Z_of_Z, Z2N.id, Z.mod_mod by (vm_compute; discriminate).
    reflexivity.
  Qed.

  Lemma affine_field_output x z :
    F.to_Z (F.mul (F.of_Z q x) (F.inv (F.of_Z q z))) =
    (x * (z^LadderController.inverse_exponent mod LadderAccelerator.prime)) mod LadderAccelerator.prime.
  Proof.
    rewrite F.to_Z_mul, F.to_Z_of_Z, inverse_to_Z.
    change (Z.pos q) with LadderAccelerator.prime.
    rewrite Z.mul_mod_idemp_l by (unfold LadderAccelerator.prime; lia). reflexivity.
  Qed.

  Theorem affine_refines_curve25519 u k :
    0 <= u < LadderAccelerator.prime -> 0 <= k < 2^255 ->
    Zmod.unsigned (fn.interp LadderController.output
      (LadderController.run 5612
        (fn.interp LadderController.init (bits.of_Z 255 u,bits.of_Z 255 k)))) =
    Curve25519Bridge.curve25519_cswap 255 u k.
  Proof.
    intros Hu Hk. pose proof (proj2 (proj2 (LadderController.affine_refines_power u k Hu Hk))) as H.
    unfold Curve25519Bridge.curve25519_cswap, Curve25519Bridge.affine_output.
    change (Z.pos q) with LadderAccelerator.prime.
    destruct (MontLadderCSwap LadderAccelerator.prime 121666 255 u k) as [x z].
    rewrite affine_field_output. exact H.
  Qed.

  Theorem controller_curve25519_correct k (P : Curve25519.M.point) :
    0 <= k < 2^255 ->
    Zmod.unsigned (fn.interp LadderController.output
      (LadderController.run 5612 (fn.interp LadderController.init
        (bits.of_Z 255 (F.to_Z (Curve25519.M.X0 P)),bits.of_Z 255 k)))) =
    F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult k P)).
  Proof.
    intro Hk. rewrite affine_refines_curve25519.
    - apply Curve25519Bridge.curve25519_cswap_correct. exact Hk.
    - change (0 <= F.to_Z (Curve25519.M.X0 P) < Z.pos q).
      apply F.to_Z_range. vm_compute. reflexivity.
    - exact Hk.
  Qed.
End LadderControllerCurveBridge.

Print Assumptions LadderController.one_iteration_refines_math.
Print Assumptions LadderController.tick_control_independent.
Print Assumptions LadderController.projective_refines_cswap.
Print Assumptions LadderController.twenty_ticks_recurrence.
Print Assumptions LadderController.fixed_projective_control.
Print Assumptions LadderController.affine_refines_power.
Print Assumptions LadderController.affine_zero_denominator.
Print Assumptions LadderController.ready_after_5612.
Print Assumptions LadderControllerCurveBridge.affine_field_output.
Print Assumptions LadderControllerCurveBridge.affine_refines_curve25519.
Print Assumptions LadderControllerCurveBridge.controller_curve25519_correct.
