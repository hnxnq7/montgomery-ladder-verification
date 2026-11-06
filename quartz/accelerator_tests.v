From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import accelerator.
From Stdlib Require Import BinInt Bits List.
Import ListNotations LadderAccelerator.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module LadderAcceleratorTests.
  Definition calculate (op : operation) (a b : Z) : Z :=
    Zmod.unsigned (fn.interp (arithmetic op) (bits.of_Z 255 a, bits.of_Z 255 b)).

  Example field_boundaries :
    List.map (fun '(op,a,b) => calculate op a b)
      [(Add,prime-1,prime-1); (Sub,0,prime-1); (Mul,prime-1,prime-1);
       (Sub,0,2^255-1); (Mul,2^255-1,2^255-1)] =
    [prime-2;1;1;prime-18;324].
  Proof. vm_compute. reflexivity. Qed.

  Example reduction_boundaries :
    List.map (fun x => Zmod.unsigned (fn.interp reduce (bits.of_Z 512 x)))
      [0;prime;2*prime;2^255;2^510-1;2^512-1] =
    List.map (fun x => x mod prime) [0;prime;2*prime;2^255;2^510-1;2^512-1].
  Proof. vm_compute. reflexivity. Qed.

  Definition observed (s : State) : (Z*Z)*(Z*Z) :=
    let '((x2,z2),(x3,z3)) := fn.interp output s in
    ((Zmod.unsigned x2,Zmod.unsigned z2),(Zmod.unsigned x3,Zmod.unsigned z3)).

  Definition specification (x1 x2 z2 x3 z3 : Z) : (Z*Z)*(Z*Z) :=
    let u := x2+z2 in let v := x2-z2 in
    let w := x3+z3 in let t := x3-z3 in
    let d := u*u-v*v in
    (((u*u*v*v) mod prime, (d*(v*v+121666*d)) mod prime),
      (((u*t+v*w)^2) mod prime, ((u*t-v*w)^2*x1) mod prime)).

  Example ladder_step_vectors :
    List.map (fun '(x1,x2,z2,x3,z3) => observed (run 18 (initial x1 x2 z2 x3 z3)))
      [(9,1,0,9,1); (9,6400,157681440,324,36);
       (prime-1,prime-2,prime-3,prime-4,prime-5); (0,0,0,0,0)] =
    List.map (fun '(x1,x2,z2,x3,z3) => specification x1 x2 z2 x3 z3)
      [(9,1,0,9,1); (9,6400,157681440,324,36);
       (prime-1,prime-2,prime-3,prime-4,prime-5); (0,0,0,0,0)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma completed_state_stable regs :
    fn.interp tick (rep {|phase := bits.of_Z 5 18; bank := regs|}) =
    rep {|phase := bits.of_Z 5 18; bank := regs|}.
  Proof. reflexivity. Qed.

  Lemma reset_is_idle s :
    fn.interp tick (fn.interp reset s) = fn.interp reset s /\
    fn.interp ready (fn.interp reset s) = false.
  Proof. split; reflexivity. Qed.

  Example readiness_schedule :
    List.map (fun n => Zmod.unsigned (fn.interp ready (run n (initial 9 1 0 9 1))))
      [0%nat;1%nat;17%nat;18%nat;19%nat;32%nat] = [0;0;0;1;1;1].
  Proof. vm_compute. reflexivity. Qed.

  Print Assumptions tick_phase_independent.
  Print Assumptions run_phase_independent.
  Print Assumptions ready_after_step.
  Print Assumptions completed_state_stable.
  Print Assumptions start_initial.
  Print Assumptions reset_clears.
  Print Assumptions reset_is_idle.
End LadderAcceleratorTests.
