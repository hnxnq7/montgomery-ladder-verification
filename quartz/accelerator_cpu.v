From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import memory field_words accelerator.
From Stdlib Require Import BinInt Bits List.
Import InterfaceExample ListNotations.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module QuartzAcceleratorCPU.
  Import (notations) eexpr expr.
  Local Open Scope string_scope.

  (* A 512-byte MMIO window at 0x1000. *)
  Definition is_accelerator {var} : fn.fn var (type.Bits 32) type.Bool :=
    fn.Fn (fun address => quartz_eexpr:(return (#address >> (32 'd 9)) == (32 'd 8))).
  Definition Core := QuartzMemory.Core.
  Definition interface := @cpu.impl 2 1 1 1 (@is_accelerator) type.interp.

  Record state := {
    core : Core;
    scratch : list (bits 32);
    inputs : list (bits 32);
    device : LadderAccelerator.State;
    response_pending : option cpu.Mem_resp_t
  }.

  Definition input_field (words : list (bits 32)) (index : nat) : bits 255 :=
    bits.of_Z 255 (Curve25519Words.decode (firstn 8 (skipn (8*index) words))).

  Definition start_device (words : list (bits 32)) : LadderAccelerator.State :=
    fn.interp LadderAccelerator.start (LadderAccelerator.input_rep
      {| LadderAccelerator.in_x1 := input_field words 0;
         LadderAccelerator.in_x2 := input_field words 1;
         LadderAccelerator.in_z2 := input_field words 2;
         LadderAccelerator.in_x3 := input_field words 3;
         LadderAccelerator.in_z3 := input_field words 4 |}).

  Definition output_words (device : LadderAccelerator.State) : list (bits 32) :=
    let '((x2,z2),(x3,z3)) := fn.interp LadderAccelerator.output device in
    flat_map (fun x => Curve25519Words.encode 8 (Zmod.unsigned x)) [x2;z2;x3;z3].

  (* Input words 0..39; command 40; status 41; output words 42..73. *)
  Definition access (s : state) (address data : bits 32) (store : bool) : state * bits 32 :=
    let addr := Zmod.unsigned address in
    if andb (andb (4096 <=? addr) (addr <? 4608)) (addr mod 4 =? 0) then
      let index := Z.to_nat ((addr - 4096) / 4) in
      if store then
        let words := if Nat.ltb index 40 then QuartzMemory.write s.(inputs) index data
          else if andb (Nat.eqb index 40) (Zmod.unsigned data =? 0)
            then repeat (bits.of_Z 32 0) 40 else s.(inputs) in
        let dev := if Nat.eqb index 40 then
          if Zmod.unsigned data =? 1 then start_device words
          else if Zmod.unsigned data =? 0 then fn.interp LadderAccelerator.reset s.(device)
          else s.(device) else s.(device) in
        ({| core := s.(core); scratch := s.(scratch); inputs := words;
            device := dev; response_pending := s.(response_pending) |}, bits.of_Z 32 0)
      else
        let ready := Zmod.nonzero (fn.interp LadderAccelerator.ready s.(device)) in
        let value := if Nat.eqb index 41 then bits.of_Z 32 (if ready then 1 else 0)
          else if andb ready (andb (Nat.leb 42 index) (Nat.ltb index 74))
            then nth (index-42) (output_words s.(device)) (bits.of_Z 32 0)
            else bits.of_Z 32 0 in
        (s,value)
    else (s,bits.of_Z 32 0).

  (* Quartz accepts an MMIO response only after its request has been dequeued. *)
  Definition service_mmio (s : state) : state :=
    match s.(response_pending) with
    | Some response =>
      if Zmod.nonzero (fn.interp (CPU.canEnqResp Core interface CPU.MMIO) s.(core)) then
        {| core := fn.interp (CPU.enqResp Core interface CPU.MMIO) (s.(core),response);
           scratch := s.(scratch); inputs := s.(inputs); device := s.(device);
           response_pending := None |}
      else s
    | None =>
      if Zmod.nonzero (fn.interp (CPU.canDeqReq Core interface CPU.MMIO) s.(core)) then
        let request := fn.interp (CPU.peek Core interface CPU.MMIO) s.(core) in
        let address := fn.interp QuartzMemory.request_address request in
        let data := fn.interp QuartzMemory.request_data request in
        let store := Zmod.nonzero (fn.interp QuartzMemory.request_store request) in
        let '(next,value) := access s address data store in
        {| core := fn.interp (CPU.deqReq Core interface CPU.MMIO) s.(core);
           scratch := next.(scratch); inputs := next.(inputs); device := next.(device);
           response_pending := Some (QuartzMemory.response address value) |}
      else s
    end.

  Definition tick (program : list (bits 32)) (s : state) : state :=
    let s := service_mmio {| core := s.(core); scratch := s.(scratch); inputs := s.(inputs);
      device := fn.interp LadderAccelerator.tick s.(device); response_pending := s.(response_pending) |} in
    let memory := QuartzMemory.service_data
      {| QuartzMemory.core := s.(core); QuartzMemory.scratch := s.(scratch) |} in
    let core := QuartzMemory.service_instruction program memory.(QuartzMemory.core) in
    {| core := fn.interp (CPU.tick Core interface) core;
       scratch := memory.(QuartzMemory.scratch); inputs := s.(inputs); device := s.(device);
       response_pending := s.(response_pending) |}.

  Fixpoint run (program : list (bits 32)) (cycles : nat) (s : state) : state :=
    match cycles with O => s | S rest => run program rest (tick program s) end.

  Definition initial (words : nat) : state :=
    {| core := type.default Core; scratch := repeat (bits.of_Z 32 0) words;
       inputs := repeat (bits.of_Z 32 0) 40;
       device := fn.interp LadderAccelerator.reset (type.default LadderAccelerator.State);
       response_pending := None |}.
End QuartzAcceleratorCPU.
