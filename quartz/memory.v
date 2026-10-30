From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From Stdlib Require Import BinInt Bits List.
Import InterfaceExample ListNotations.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module QuartzMemory.
  Definition no_mmio {var} : fn.fn var (type.Bits 32) type.Bool :=
    fn.Fn (fun (_ : var (type.Bits 32)) =>
      eexpr.Ret (expr.Const (t := type.Bool) (bits.of_Z 1 0))).

  Definition Core :=
    @cpu.State 2 1 1 1.

  Definition interface :=
    @cpu.impl 2 1 1 1 (@no_mmio) type.interp.

  Import (notations) eexpr expr.
  Local Open Scope string_scope.

  Definition request_address {var} : fn.fn var cpu.Mem_req_t (type.Bits 32) :=
    fn.Fn (fun r => quartz_eexpr:(return #r..cpu.mem_req_addr)).

  Definition request_data {var} : fn.fn var cpu.Mem_req_t (type.Bits 32) :=
    fn.Fn (fun r => quartz_eexpr:(return #r..cpu.mem_req_data)).

  Definition request_store {var} : fn.fn var cpu.Mem_req_t type.Bool :=
    fn.Fn (fun r => quartz_eexpr:(return #r..cpu.mem_req_is_store)).

  Definition read (memory : list (bits 32)) (address : bits 32) : bits 32 :=
    nth (Z.to_nat (Zmod.unsigned address / 4)) memory (bits.of_Z 32 0).

  Fixpoint write (memory : list (bits 32)) (index : nat) (value : bits 32) : list (bits 32) :=
    match memory, index with
    | [], _ => []
    | _ :: rest, O => value :: rest
    | x :: rest, S i => x :: write rest i value
    end.

  Definition response (address value : bits 32) : cpu.Mem_resp_t :=
    cpu.mem_resp_rep {| cpu.mem_resp_addr := address; cpu.mem_resp_data := value |}.

  Definition service_instruction (program : list (bits 32)) (s : Core) : Core :=
    if andb (Zmod.nonzero (fn.interp (CPU.canDeqReq Core interface CPU.IMEM) s))
        (Zmod.nonzero (fn.interp (CPU.canEnqResp Core interface CPU.IMEM) s)) then
      let request := fn.interp (CPU.peek Core interface CPU.IMEM) s in
      let address := fn.interp request_address request in
      let s := fn.interp (CPU.deqReq Core interface CPU.IMEM) s in
      fn.interp (CPU.enqResp Core interface CPU.IMEM) (s, response address (read program address))
    else s.

  Record state := { core : Core; scratch : list (bits 32) }.

  (* A fixed-latency environment for the processor's existing request/response queues. *)
  Definition service_data (s : state) : state :=
    if andb (Zmod.nonzero (fn.interp (CPU.canDeqReq Core interface CPU.DMEM) s.(core)))
        (Zmod.nonzero (fn.interp (CPU.canEnqResp Core interface CPU.DMEM) s.(core))) then
      let request := fn.interp (CPU.peek Core interface CPU.DMEM) s.(core) in
      let address := fn.interp request_address request in
      let store := Zmod.nonzero (fn.interp request_store request) in
      let memory := if store then
          write s.(scratch) (Z.to_nat (Zmod.unsigned address / 4)) (fn.interp request_data request)
        else s.(scratch) in
      let value := if store then bits.of_Z 32 0 else read memory address in
      let core := fn.interp (CPU.deqReq Core interface CPU.DMEM) s.(core) in
      {| core := fn.interp (CPU.enqResp Core interface CPU.DMEM) (core, response address value);
         scratch := memory |}
    else s.

  Definition tick (program : list (bits 32)) (s : state) : state :=
    let s := service_data s in
    let core := service_instruction program s.(core) in
    {| core := fn.interp (CPU.tick Core interface) core; scratch := s.(scratch) |}.

  Fixpoint run (program : list (bits 32)) (cycles : nat) (s : state) : state :=
    match cycles with O => s | S rest => run program rest (tick program s) end.

  Definition initial (words : nat) : state :=
    {| core := type.default Core; scratch := repeat (bits.of_Z 32 0) words |}.
End QuartzMemory.
