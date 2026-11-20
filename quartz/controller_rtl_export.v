From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax transform pp sv.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import accelerator ladder_controller controller_protection.
From Stdlib Require Import String ZArith Bits.
Import fn Syntax.type InterfaceExample.QStdlib.
Import (coercions) domain.Zmod.
Open Scope Z_scope.

Module ControllerRTL.
  Module C := LadderController.
  Module P := ControllerProtection.
  Module A := LadderAccelerator.
  Record request := {
    device : P.State; operands : C.Inputs; reset_flag : Bool; start_flag : Bool
  }.
  Definition Request := type.reify'' request.
  Coercion request_rep (r : request) : Request :=
    ltac2:(let t := struct.rep &r in exact $t).
  Record response := {
    next_device : P.State; ready_flag : Bool; affine_value : Bits 255; stored_pack : Bits P.width
  }.
  Definition Response := type.reify'' response.
  Import (notations) Syntax.eexpr Syntax.expr.
  Local Open Scope string_scope.

  Definition idle : C.State :=
    (C.rep {| C.stage := bits.of_Z 4 15; C.index := bits.of_Z 8 0; C.elapsed := bits.of_Z 5 0;
      C.x1 := bits.of_Z 255 0; C.scalar := bits.of_Z 255 0; C.prev := Zmod.embed_bool false;
      C.x2 := bits.of_Z 255 0; C.z2 := bits.of_Z 255 0;
      C.x3 := bits.of_Z 255 0; C.z3 := bits.of_Z 255 0; C.acc := bits.of_Z 255 0 |},
      fn.interp A.reset (type.default A.State)).

  Definition reset {var} : fn var P.State P.State :=
    Fn (fun old => quartz_eexpr:(
      let c := $(Syntax.expr.Const (t := C.Control) (type.default C.Control)) in
      let c <- #c..C.stage = (4 'd 15) in
      let engine := A.reset ($(Syntax.expr.Const (t := A.State) (type.default A.State))) in
      return P.protect ((#c, #engine)))).

  Definition gated_output {var} : fn var P.State (Bits 255) :=
    Fn (fun s => quartz_eexpr:(
      let status := C.ready (#s .1) in
      let value := C.output (#s .1) in
      return $(Syntax.expr.If (Syntax.expr.Var status) (Syntax.expr.Var value)
        (Syntax.expr.Const (t := Bits 255) (bits.of_Z 255 0))))).

  Definition advance {var} : fn var Request P.State :=
    Fn (fun r => quartz_eexpr:(
      if #r..reset_flag then return reset (#r..device) else
      if #r..start_flag then return P.init (#r..operands) else return P.tick (#r..device))).

  (* Outputs describe the stored state, not the prospective next state. *)
  Definition cycle {var} : fn var Request Response :=
    Fn (fun r => quartz_eexpr:(
      let next := advance (#r) in
      let status := C.ready (#r..device .1) in
      let value := gated_output (#r..device) in
      let audit := P.pack_state (#r..device .1) in
      let result := $(Syntax.expr.Const (t := Response) (type.default Response)) in
      let result <- #result..next_device = #next in
      let result <- #result..ready_flag = #status in
      let result <- #result..affine_value = #value in
      let result <- #result..stored_pack = #audit in
      return #result)).

  Definition response_output {var} : fn var Response (Bits 255) :=
    Fn (fun r => quartz_eexpr:(return #r..affine_value)).
  Definition response_ready {var} : fn var Response Bool :=
    Fn (fun r => quartz_eexpr:(return #r..ready_flag)).
  Definition response_next {var} : fn var Response P.State :=
    Fn (fun r => quartz_eexpr:(return #r..next_device)).
  Definition response_pack {var} : fn var Response (Bits P.width) :=
    Fn (fun r => quartz_eexpr:(return #r..stored_pack)).

  Lemma reset_interp s : fn.interp reset s = fn.interp P.protect idle.
  Proof. reflexivity. Qed.

  Theorem reset_valid s : P.valid (fn.interp reset s).
  Proof. rewrite reset_interp. apply P.protect_valid. Qed.

  Lemma idle_stutters : fn.interp C.tick idle = idle.
  Proof. rewrite C.tick_interp. reflexivity. Qed.

  Theorem reset_hold s : fn.interp P.tick (fn.interp reset s) = fn.interp reset s.
  Proof.
    rewrite reset_interp, P.tick_interp, !P.protect_interp. cbn [fst].
    rewrite idle_stutters. reflexivity.
  Qed.

  Lemma gated_output_interp s :
    fn.interp gated_output s = if Zmod.nonzero (fn.interp C.ready (fst s))
      then fn.interp C.output (fst s) else bits.of_Z 255 0.
  Proof. reflexivity. Qed.

  Theorem output_before_ready s : fn.interp C.ready (fst s) = Zmod.embed_bool false ->
    fn.interp gated_output s = bits.of_Z 255 0.
  Proof.
    intro H.
    exact (f_equal (fun b : Bool => if Zmod.nonzero b
      then fn.interp C.output (fst s) else bits.of_Z 255 0) H).
  Qed.

  Theorem output_when_ready s : fn.interp C.ready (fst s) = Zmod.embed_bool true ->
    fn.interp gated_output s = fn.interp C.output (fst s).
  Proof.
    intro H.
    exact (f_equal (fun b : Bool => if Zmod.nonzero b
      then fn.interp C.output (fst s) else bits.of_Z 255 0) H).
  Qed.

  Lemma cycle_output r :
    fn.interp response_output (fn.interp cycle (request_rep r)) = fn.interp gated_output r.(device).
  Proof. reflexivity. Qed.

  Lemma cycle_ready r : fn.interp response_ready (fn.interp cycle (request_rep r)) =
    fn.interp C.ready (fst r.(device)).
  Proof. reflexivity. Qed.

  Lemma cycle_pack r : fn.interp response_pack (fn.interp cycle (request_rep r)) =
    @type.pack C.State (fst r.(device)).
  Proof. exact (P.pack_state_correct (fst r.(device))). Qed.

  Lemma cycle_next r : fn.interp response_next (fn.interp cycle (request_rep r)) =
    if Zmod.nonzero r.(reset_flag) then fn.interp reset r.(device) else
    if Zmod.nonzero r.(start_flag) then fn.interp P.init r.(operands) else fn.interp P.tick r.(device).
  Proof. reflexivity. Qed.

  Theorem cycle_valid r : P.valid (fn.interp response_next (fn.interp cycle (request_rep r))).
  Proof.
    rewrite cycle_next. destruct (Zmod.nonzero r.(reset_flag)); [apply reset_valid|].
    destruct (Zmod.nonzero r.(start_flag)); [apply P.init_valid|apply P.tick_valid].
  Qed.

  Theorem cycle_stored_HW r :
    P.state_HW (fn.interp response_next (fn.interp cycle (request_rep r))) = Z.to_nat P.width.
  Proof. apply P.protected_HW_constant, cycle_valid. Qed.

  Theorem completed_output input :
    fn.interp gated_output (P.run 5612 (fn.interp P.init input)) =
    fn.interp C.output (C.run 5612 (fn.interp C.init input)).
  Proof.
    rewrite output_when_ready, P.run_erasure; [reflexivity|].
    rewrite P.run_erasure. apply C.ready_after_5612.
  Qed.

  (* Name hints do not participate in interpretation. *)
  Fixpoint safe_locals {var func t} (e : Syntax.eexpr.eexpr var func t) : Syntax.eexpr.eexpr var func t :=
    match e with
    | @Syntax.eexpr.Ret _ _ _ e => Syntax.eexpr.Ret e
    | @Syntax.eexpr.Let _ _ _ _ e _ k => Syntax.eexpr.Let "v" e (fun x => safe_locals (k x))
    | @Syntax.eexpr.Bind _ _ _ _ e _ k => Syntax.eexpr.Bind "v" (safe_locals e) (fun x => safe_locals (k x))
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
    | @fns.Let _ _ _ _ _ _ name _ body rest =>
      fns.Let name "arg" (fun x => safe_locals (body x)) (fun f => safe_names (rest f))
    | @fns.Ret _ _ _ _ name _ body => fns.Ret name "arg" (fun x => safe_locals (body x))
    end.

  Ltac2 Type counter := { mutable names : ident list }.
  Ltac2 rec name_functions counter c :=
    let c := Constr.Unsafe.map (name_functions counter) c in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App head args =>
      if Constr.equal head '(@fn.Fn) then
        let used := counter.(names) in
        let name := Fresh.fresh (Fresh.Free.of_ids used) @unrolled in
        counter.(names) := name :: used;
        let ty := Constr.Unsafe.make (Constr.Unsafe.App '(@fn.fn)
          [| Array.get args 0; Array.get args 1; Array.get args 2 |]) in
        let binder := Constr.Binder.unsafe_make (Some name) Constr.Binder.Relevant ty in
        Constr.Unsafe.make (Constr.Unsafe.LetIn binder c (Constr.Unsafe.make (Constr.Unsafe.Rel 1)))
      else c
    | _ => c
    end.

  (* Only static syntax recursion is expanded; the controller remains sequential. *)
  Definition export_cycle {var} : fn var Request Response :=
    ltac2:(
      let c := eval cbv beta iota zeta delta
        [cycle advance reset gated_output P.init P.tick P.protect P.pack_state
         C.init C.tick C.prep C.work C.collect C.final_swap
         C.affine_square C.affine_multiply C.affine_finish C.ready C.output
         A.start A.reset A.tick A.dispatch A.schedule A.execute A.arithmetic]
        in (@cycle var) in
      let c := name_functions { names := [] } c in
      exact $c).

  Lemma export_cycle_correct : fn.interp (@export_cycle type.interp) = fn.interp (@cycle type.interp).
  Proof. reflexivity. Qed.

  Definition packaged_circuit {var : type -> Type} {func : type -> type -> Type} :
    fns.fns var func Request Response := fns.package_global_fns'' var func (@export_cycle).

  Lemma packaging_correct :
    fns.interp (@packaged_circuit type.interp type.interpfn) = fn.interp (@export_cycle type.interp).
  Proof. reflexivity. Qed.

  Definition native_circuit {var : type -> Type} {func : type -> type -> Type} :
    fns.fns var func Request Response := safe_names (@packaged_circuit var func).

  Lemma sanitization_correct :
    fns.interp (@native_circuit type.interp type.interpfn) =
    fns.interp (@packaged_circuit type.interp type.interpfn).
  Proof. reflexivity. Qed.

  Theorem native_circuit_correct :
    fns.interp (@native_circuit type.interp type.interpfn) = fn.interp (@cycle type.interp).
  Proof. rewrite sanitization_correct, packaging_correct, export_cycle_correct. reflexivity. Qed.

  Definition sequential_shell : string :=
    "
module protected_ladder_controller (
  input logic clk, reset, start,
  input logic [254:0] x1, scalar,
  output wire ready,
  output wire [254:0] out_affine
);
  timeunit 1ns;
  timeprecision 1ps;
  localparam int CORE_WIDTH = " ++ pp.Z P.width ++ ";
  // Preservation attributes are not a post-synthesis leakage guarantee.
  (* keep = ""true"", dont_touch = ""true"", preserve = ""true"" *)
  " ++ sv.pp_type P.State ++ " state_q;
  " ++ sv.pp_type Request ++ " request_d;
  " ++ sv.pp_type Response ++ " response_d;
  always_comb begin
    request_d.device = state_q;
    request_d.operands.fst = x1;
    request_d.operands.snd = scalar;
    request_d.reset_flag = reset;
    request_d.start_flag = start;
    response_d = export_cycle(request_d);
  end
  // Reset is synchronous, has priority over start, and installs protected idle.
  always_ff @(posedge clk) state_q <= response_d.next_device;
  assign ready = response_d.ready_flag;
  assign out_affine = response_d.affine_value;
endmodule
".

  Definition systemverilog (functions : string) : string := functions ++ sequential_shell.
End ControllerRTL.

Print Assumptions ControllerRTL.output_before_ready.
Print Assumptions ControllerRTL.completed_output.
Print Assumptions ControllerRTL.cycle_stored_HW.
Print Assumptions ControllerRTL.safe_locals_correct.
Print Assumptions ControllerRTL.native_circuit_correct.
