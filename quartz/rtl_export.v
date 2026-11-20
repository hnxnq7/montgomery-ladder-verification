From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import Syntax sv.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import accelerator protected_accelerator.
From Stdlib Require Import String ZArith.
Import fn type InterfaceExample.QStdlib.
Open Scope Z_scope.

Module AcceleratorRTL.
  Module P := ProtectedAccelerator.
  Module Core := LadderAccelerator.
  Record request := {
    device : P.State; operands : Core.Inputs; reset_flag : Bool; start_flag : Bool
  }.
  Definition Request := type.reify'' request.
  Record response := {
    next_device : P.State; ready_flag : Bool;
    coordinates : Pair (Pair (Bits 255) (Bits 255)) (Pair (Bits 255) (Bits 255))
  }.
  Definition Response := type.reify'' response.
  Import (notations) eexpr expr.
  Local Open Scope string_scope.

  Definition advance {var} : fn var Request P.State :=
    Fn (fun r => quartz_eexpr:(
      if #r..reset_flag then return P.reset (#r..device)
      else if #r..start_flag then return P.start (#r..operands)
      else return P.tick (#r..device))).

  Definition cycle {var} : fn var Request Response :=
    Fn (fun r => quartz_eexpr:(
      let next := advance (#r) in
      let status := P.ready (#r..device) in
      let coords := P.output (#r..device) in
      let result := $(expr.Const (t := Response) (type.default Response)) in
      let result <- #result..next_device = #next in
      let result <- #result..ready_flag = #status in
      let result <- #result..coordinates = #coords in
      return #result)).

  (* The upstream packager requires nested Fn nodes to be let-bound. *)
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
          Constr.Unsafe.make (Constr.Unsafe.LetIn binder c
            (Constr.Unsafe.make (Constr.Unsafe.Rel 1)))
        else c
    | _ => c
    end.

  Definition export_cycle {var} : fn var Request Response :=
    ltac2:(
      let c := eval cbv beta iota zeta delta
        [cycle advance P.tick P.protect P.copy_complements P.start P.reset
         Core.tick Core.dispatch Core.schedule Core.execute Core.arithmetic] in (@cycle var) in
      let c := name_functions { names := [] } c in
      exact $c).

  Lemma export_cycle_correct :
    fn.interp (@export_cycle type.interp) = fn.interp (@cycle type.interp).
  Proof. reflexivity. Qed.

  (* Argument names are printer hints, not Quartz semantics. *)
  Fixpoint safe_argument_names {var func a b} (fs : fns.fns var func a b) :
    fns.fns var func a b :=
    match fs with
    | fns.Let name _ body rest =>
        fns.Let name "arg" body (fun f => safe_argument_names (rest f))
    | fns.Ret name _ body => fns.Ret name "arg" body
    end.

  Definition native_circuit {var : type -> Type} {func : type -> type -> Type} :
    fns.fns var func Request Response :=
    safe_argument_names (fns.package_global_fns'' var func (@export_cycle)).

  Lemma native_circuit_correct :
    fns.interp (@native_circuit type.interp type.interpfn) = fn.interp (@cycle type.interp).
  Proof. reflexivity. Qed.

  (* The backend emits combinational functions; this shell stores only P.State. *)
  Definition sequential_shell : string :=
    "
module protected_ladder_accelerator (
  input logic clk, reset, start,
  input logic [254:0] x1, x2, z2, x3, z3,
  output wire ready,
  output wire [254:0] out_x2, out_z2, out_x3, out_z3
);
  timeunit 1ns;
  timeprecision 1ps;
  // Preservation directives require a separate post-synthesis audit.
  (* keep = ""true"", dont_touch = ""true"", preserve = ""true"" *)
  " ++ sv.pp_type P.State ++ " state_q;
  " ++ sv.pp_type Request ++ " request_d;
  " ++ sv.pp_type Response ++ " response_d;
  always_comb begin
    request_d.device = state_q;
    request_d.operands.in_x1 = x1;
    request_d.operands.in_x2 = x2;
    request_d.operands.in_z2 = z2;
    request_d.operands.in_x3 = x3;
    request_d.operands.in_z3 = z3;
    request_d.reset_flag = reset;
    request_d.start_flag = start;
    response_d = export_cycle(request_d);
  end
  // Reset is synchronous and has priority over start.
  always_ff @(posedge clk) state_q <= response_d.next_device;
  assign ready = response_d.ready_flag;
  assign out_x2 = response_d.coordinates.fst.fst;
  assign out_z2 = response_d.coordinates.fst.snd;
  assign out_x3 = response_d.coordinates.snd.fst;
  assign out_z3 = response_d.coordinates.snd.snd;
endmodule
".

  Definition systemverilog (generated_functions : string) : string :=
    generated_functions ++ sequential_shell.
End AcceleratorRTL.
