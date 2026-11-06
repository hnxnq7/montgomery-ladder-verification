From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import field_words accelerator accelerator_cpu.
From Stdlib Require Import BinInt Bits List.
Import ListNotations QuartzAcceleratorCPU.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module QuartzAcceleratorCPUTests.
  Definition addi (rd immediate : Z) : bits 32 :=
    bits.of_Z 32 (immediate * 2^20 + rd * 2^7 + 0x13).
  Definition lw (rd base offset : Z) : bits 32 :=
    bits.of_Z 32 (offset * 2^20 + base * 2^15 + 0x2000 + rd * 2^7 + 0x03).
  Definition sw (source base offset : Z) : bits 32 :=
    bits.of_Z 32 ((offset / 32) * 2^25 + source * 2^20 + base * 2^15 +
      0x2000 + (offset mod 32) * 2^7 + 0x23).

  (* CPU writes (9,1,0,9,1), starts the device, then copies status/results to RAM. *)
  Definition program : list (bits 32) :=
    [bits.of_Z 32 0x000010b7; addi 2 9; sw 2 1 0; sw 2 1 96;
     addi 2 1; sw 2 1 32; sw 2 1 128; sw 2 1 160] ++
    repeat (addi 10 0) 16 ++
    [lw 3 1 164; sw 3 0 0; lw 3 1 168; sw 3 0 4; lw 3 1 200; sw 3 0 8;
     lw 3 1 232; sw 3 0 12; lw 3 1 264; sw 3 0 16; bits.of_Z 32 0x00000063].

  Example native_cpu_accelerator_step :
    map Zmod.unsigned (scratch (run program 300 (initial 5))) = [1;1;0;324;36].
  Proof. vm_compute. reflexivity. Qed.

  Example unaligned_access_ignored :
    access (initial 5) (bits.of_Z 32 4097) (bits.of_Z 32 99) true =
      (initial 5,bits.of_Z 32 0).
  Proof. vm_compute. reflexivity. Qed.

  Example outputs_hidden_until_ready :
    snd (access (initial 5) (bits.of_Z 32 4264) (bits.of_Z 32 0) false) = bits.of_Z 32 0.
  Proof. vm_compute. reflexivity. Qed.

  Example full_width_input_snapshot :
    start_device (flat_map (Curve25519Words.encode 8)
      [LadderAccelerator.prime-1; LadderAccelerator.prime-2; LadderAccelerator.prime-3;
       LadderAccelerator.prime-4; LadderAccelerator.prime-5]) =
    LadderAccelerator.initial (LadderAccelerator.prime-1) (LadderAccelerator.prime-2)
      (LadderAccelerator.prime-3) (LadderAccelerator.prime-4) (LadderAccelerator.prime-5).
  Proof. vm_compute. reflexivity. Qed.

  Example reset_discards_completed_output :
    fst (access {| core := (initial 5).(core); scratch := (initial 5).(scratch);
      inputs := repeat (bits.of_Z 32 99) 40;
      device := LadderAccelerator.run 18 (LadderAccelerator.initial 9 1 0 9 1);
      response_pending := None |} (bits.of_Z 32 4256) (bits.of_Z 32 0) true) = initial 5.
  Proof. vm_compute. reflexivity. Qed.

  Print Assumptions native_cpu_accelerator_step.
End QuartzAcceleratorCPUTests.
