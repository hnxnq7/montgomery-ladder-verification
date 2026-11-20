From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import accelerator_cpu protected_accelerator protected_accelerator_security.
From Stdlib Require Import BinInt Bits List.
Import QuartzAcceleratorCPU InterfaceExample.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module QuartzAcceleratorCPUSecurity.
  Module P := ProtectedAccelerator.

  Definition device_valid (s : state) : Prop :=
    P.valid s.(device).

  Lemma access_preserves_device s address data store :
    device_valid s -> device_valid (fst (access s address data store)).
  Proof.
    intros H. unfold access.
    destruct (andb (andb (4096 <=? Zmod.unsigned address) (Zmod.unsigned address <? 4608))
      (Zmod.unsigned address mod 4 =? 0)); [|exact H].
    destruct store; [|exact H].
    unfold device_valid. cbn [fst device].
    destruct (Nat.eqb (Z.to_nat ((Zmod.unsigned address - 4096) / 4)) 40); [|exact H].
    destruct (Zmod.unsigned data =? 1).
    - unfold start_device. apply P.start_valid.
    - destruct (Zmod.unsigned data =? 0); [apply P.reset_valid|exact H].
  Qed.

  Lemma service_preserves_device s :
    device_valid s -> device_valid (service_mmio s).
  Proof.
    intros H. unfold service_mmio.
    destruct (response_pending s) as [response|].
    - destruct (Zmod.nonzero (fn.interp (CPU.canEnqResp Core interface CPU.MMIO) (core s)));
        exact H.
    - destruct (Zmod.nonzero (fn.interp (CPU.canDeqReq Core interface CPU.MMIO) (core s)));
        [|exact H].
      match goal with
      | |- context [access s ?a ?d ?b] =>
          pose proof (access_preserves_device s a d b H) as Hv;
          destruct (access s a d b) as [next value] eqn:E
      end.
      exact Hv.
  Qed.

  Theorem tick_device_valid program s : device_valid (tick program s).
  Proof.
    unfold tick.
    pose proof (service_preserves_device
      {| core := core s; scratch := scratch s; inputs := inputs s;
         device := fn.interp P.tick (device s); response_pending := response_pending s |}
      (P.tick_valid (device s))) as H.
    exact H.
  Qed.

  Theorem run_preserves_device program cycles s :
    device_valid s -> device_valid (run program cycles s).
  Proof.
    revert s. induction cycles; intros s H.
    - exact H.
    - apply IHcycles, tick_device_valid.
  Qed.

  Theorem initial_device_valid words : device_valid (initial words).
  Proof. apply P.reset_valid. Qed.

  (* Device storage only; CPU registers, staging RAM, and bus queues are not included. *)
  Theorem device_bank_HW_constant program cycles words :
    ProtectedAcceleratorSecurity.bank_HW (device (run program cycles (initial words))) = 8160%nat.
  Proof.
    apply ProtectedAcceleratorSecurity.protected_bank_HW_constant.
    apply run_preserves_device, initial_device_valid.
  Qed.

End QuartzAcceleratorCPUSecurity.

Print Assumptions QuartzAcceleratorCPUSecurity.device_bank_HW_constant.
