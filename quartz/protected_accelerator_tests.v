From Stdlib Require Import ZArith Bits List.
From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import accelerator protected_accelerator protected_accelerator_security
  accelerator_cpu accelerator_cpu_security.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module ProtectedAcceleratorTests.
  Module P := ProtectedAccelerator.
  Module S := ProtectedAcceleratorSecurity.

  Example initial_bank_HW : S.bank_HW (P.initial 9 1 0 9 1) = 8160%nat.
  Proof. apply S.protected_bank_HW_constant, P.initial_valid. Qed.

  Example idle_register_HW s : S.register_HW (fn.interp P.reset s) = 8165%nat.
  Proof.
    unfold S.register_HW. rewrite S.protected_bank_HW_constant by apply P.reset_valid.
    rewrite P.reset_core. vm_compute. reflexivity.
  Qed.

  Example protected_input_traces :
    S.leakage_trace 18 (P.initial 9 0 1 9 1) = S.leakage_trace 18 (P.initial 9 1 1 9 1).
  Proof. apply S.initialized_trace_independent. Qed.

  Example nineteen_observations s : List.length (S.leakage_trace 18 s) = 19%nat.
  Proof. reflexivity. Qed.

  Example device_protection_survives_cpu program :
    S.bank_HW (QuartzAcceleratorCPU.device
      (QuartzAcceleratorCPU.run program 300 (QuartzAcceleratorCPU.initial 5))) = 8160%nat.
  Proof. apply QuartzAcceleratorCPUSecurity.device_bank_HW_constant. Qed.

  Print Assumptions S.ladder_step_correct_and_secure.
  Print Assumptions device_protection_survives_cpu.
End ProtectedAcceleratorTests.
