From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import memory.
From Stdlib Require Import BinInt Bits List.
Import InterfaceExample ListNotations.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module QuartzProcessorTests.
  Definition pending (a b : Z) : multiplier.state 2 :=
    {| multiplier.valid := true;
       multiplier.op1 := bits.of_Z 32 a;
       multiplier.op2 := bits.of_Z 32 b;
       multiplier.result := bits.of_Z 64 99;
       multiplier.nstep := bits.of_Z 2 0;
       multiplier.finished := false |}.

  Definition mul_tick :=
    fn.interp (multiplier.tick 2).

  Fixpoint run_mul (cycles : nat) (s : multiplier.State 2) : multiplier.State 2 :=
    match cycles with O => s | S rest => run_mul rest (mul_tick s) end.

  Definition ready (cycles : nat) (a b : Z) : Z :=
    Zmod.unsigned (fn.interp (multiplier.respReady 2) (run_mul cycles (multiplier.rep 2 (pending a b)))).

  Definition result (a b : Z) : Z :=
    Zmod.unsigned (fn.interp (multiplier.peek 2) (run_mul 4 (multiplier.rep 2 (pending a b)))).

  Lemma ready_tick_independent (s1 s2 : multiplier.state 2) :
    multiplier.valid 2 s1 = multiplier.valid 2 s2 ->
    multiplier.finished 2 s1 = multiplier.finished 2 s2 ->
    multiplier.nstep 2 s1 = multiplier.nstep 2 s2 ->
    fn.interp (multiplier.respReady 2) (mul_tick (multiplier.rep 2 s1)) =
    fn.interp (multiplier.respReady 2) (mul_tick (multiplier.rep 2 s2)).
  Proof.
    destruct s1, s2. cbn. intros Hvalid Hfinished Hstep. subst.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Example zero_waits_full_latency : map (fun n => ready n 0 7) [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] = [0; 0; 0; 0; 1].
  Proof. vm_compute. reflexivity. Qed.

  Example nonzero_waits_full_latency : map (fun n => ready n 3 7) [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] = [0; 0; 0; 0; 1].
  Proof. vm_compute. reflexivity. Qed.

  Example products : map (fun ab => result (fst ab) (snd ab)) [(0, 7); (3, 7); (4294967295, 4294967295)] =
    [0; 21; 18446744065119617025].
  Proof. vm_compute. reflexivity. Qed.

  (* ADDI x1,0,3; ADDI x2,0,7; MUL x3,x1,x2; SW; LW; SW; public self-loop. *)
  Definition smoke_program : list (bits 32) :=
    map (fun x => bits.of_Z 32 x) [0x00300093; 0x00700113; 0x022081b3; 0x00302023;
      0x00002203; 0x00402223; 0x00000063].

  Example native_cpu_multiply_store_load :
    map Zmod.unsigned (QuartzMemory.scratch
      (QuartzMemory.run smoke_program 60 (QuartzMemory.initial 2))) = [21; 21].
  Proof. vm_compute. reflexivity. Qed.

  Print Assumptions ready_tick_independent.
End QuartzProcessorTests.
