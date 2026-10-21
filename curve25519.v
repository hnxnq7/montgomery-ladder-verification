Require Import ladder_math.
Require Import ladder_machine.
From stdpp Require Import bitvector list.
From Crypto Require Import Spec.ModularArithmetic Arithmetic.ModularArithmeticTheorems Curves.Montgomery.XZ.
From Crypto Require Import Util.LetIn Util.Loops.
From Crypto Require Import Spec.Curve25519 Curves.Montgomery.XZProofs Arithmetic.PrimeFieldTheorems.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Module Curve25519Bridge.
Section FieldBridge.
  Variable q : positive.
  Variable a24 : Z.
  Local Notation encode := (F.of_Z q).
  Local Notation field := (F q).
  Add Ring bridge_field : (F.ring_theory q).

  Local Lemma encode_add x y : encode (fadd (Z.pos q) x y) = F.add (encode x) (encode y).
  Proof. unfold fadd. rewrite <- F.of_Z_mod. apply F.of_Z_add. Qed.

  Local Lemma encode_sub x y : encode (fsub (Z.pos q) x y) = F.sub (encode x) (encode y).
  Proof. unfold fsub. rewrite <- F.of_Z_mod. apply F.of_Z_sub. Qed.

  Local Lemma encode_mul x y : encode (fmul (Z.pos q) x y) = F.mul (encode x) (encode y).
  Proof. unfold fmul. rewrite <- F.of_Z_mod. apply F.of_Z_mul. Qed.

  Local Definition encode_regs (st : Z * Z * Z * Z) : field * field * field * field :=
    let '(X2, Z2, X3, Z3) := st in (encode X2, encode Z2, encode X3, encode Z3).

  (* V^2 + a24*d = U^2 + (a24-1)*d, where d = U^2 - V^2. *)
  Local Lemma step_to_field xP X2 Z2 X3 Z3 :
    let '(Xd, Zd, Xa, Za) := encode_regs (LadderStep (Z.pos q) a24 xP X2 Z2 X3 Z3) in
    ((Xd, Zd), (Xa, Za)) =
    XZ.M.xzladderstep (Fadd := F.add) (Fsub := F.sub) (Fmul := F.mul)
      (a24 := encode (a24 - 1)) (encode xP) (encode X2, encode Z2) (encode X3, encode Z3).
  Proof.
    unfold LadderStep, encode_regs, fsq, XZ.M.xzladderstep, Let_In.
    repeat rewrite ?encode_add, ?encode_sub, ?encode_mul.
    rewrite F.of_Z_sub. change (encode 1) with (@F.one q).
    f_equal; f_equal; try reflexivity; ring.
  Qed.

  Local Definition encode_state (st : (Z * Z * Z * Z) * bool) (i : Z)
      : field * field * field * field * bool * Z :=
    let '(regs, prev) := st in
    let '(X2, Z2, X3, Z3) := encode_regs regs in (X2, Z2, X3, Z3, prev, i).

  Local Definition fiat_body (n : Z) (xP : field) (st : field * field * field * field * bool * Z) :=
    let '(X2, Z2, X3, Z3, prev, i) := st in
    let bit := Z.testbit n i in
    let '(X2, X3) := XZ.M.cswap (xorb prev bit) X2 X3 in
    let '(Z2, Z3) := XZ.M.cswap (xorb prev bit) Z2 Z3 in
    let '((Xd, Zd), (Xa, Za)) :=
      XZ.M.xzladderstep (Fadd := F.add) (Fsub := F.sub) (Fmul := F.mul)
        (a24 := encode (a24 - 1)) xP (X2, Z2) (X3, Z3) in
    (Xd, Zd, Xa, Za, bit, Z.pred i).

  Local Lemma cswap_step_to_field n m xP regs prev :
    fiat_body n (encode xP) (encode_state (regs, prev) (Z.of_nat m)) =
    encode_state (MontLadderCSwap_step (Z.pos q) a24 xP (bit_i n m) prev regs)
      (Z.pred (Z.of_nat m)).
  Proof.
    destruct regs as [[[X2 Z2] X3] Z3].
    unfold fiat_body, encode_state, encode_regs, MontLadderCSwap_step, bit_i, CSwap, XZ.M.cswap.
    destruct prev, (Z.testbit n (Z.of_nat m)); cbn [xorb].
    all: rewrite <- step_to_field.
    all: reflexivity.
  Qed.

  Local Lemma loop_to_field m n xP st :
    while.while (fun '(_, i) => Z.geb i 0) (fiat_body n (encode xP)) m
      (encode_state st (Z.pred (Z.of_nat m))) =
    encode_state (MontLadderCSwap_rec (Z.pos q) a24 m xP n st) (-1).
  Proof.
    revert st. induction m as [|m IH]; intros [regs prev].
    - destruct regs as [[[X2 Z2] X3] Z3]. reflexivity.
    - destruct regs as [[[X2 Z2] X3] Z3].
      rewrite Nat2Z.inj_succ, Z.pred_succ.
      assert (Htest : Z.geb (Z.of_nat m) 0 = true) by (apply Z.geb_le; lia).
      change (let s := encode_state ((X2, Z2, X3, Z3), prev) (Z.of_nat m) in
        (if Z.geb (Z.of_nat m) 0 then
           while.while (fun '(_, i) => Z.geb i 0) (fiat_body n (encode xP)) m
             (fiat_body n (encode xP) s)
         else s) = encode_state
           (MontLadderCSwap_rec (Z.pos q) a24 (S m) xP n ((X2, Z2, X3, Z3), prev)) (-1)).
      cbv zeta. rewrite Htest, cswap_step_to_field, IH. reflexivity.
  Qed.

  Definition affine_output (coords : Z * Z) : field :=
    let '(X, Zc) := coords in F.mul (encode X) (F.inv (encode Zc)).

  Lemma cswap_matches_fiat m xP n :
    affine_output (MontLadderCSwap (Z.pos q) a24 m xP n) =
    XZ.M.montladder (Fadd := F.add) (Fsub := F.sub) (Fmul := F.mul)
      (Fzero := F.zero) (Fone := F.one) (Finv := F.inv)
      (a24 := encode (a24 - 1)) (Z.of_nat m) (Z.testbit n) (encode xP).
  Proof.
    unfold XZ.M.montladder. cbv beta zeta delta [Let_In].
    change (affine_output (MontLadderCSwap (Z.pos q) a24 m xP n) =
      let '(X2, Z2, X3, Z3, prev, _) :=
        while.while (fun '(_, i) => Z.geb i 0) (fiat_body n (encode xP))
          (Z.to_nat (Z.of_nat m)) (encode_state ((1, 0, xP, 1), false) (Z.pred (Z.of_nat m))) in
      let '(X2, _) := XZ.M.cswap prev X2 X3 in
      let '(Z2, _) := XZ.M.cswap prev Z2 Z3 in F.mul X2 (F.inv Z2)).
    rewrite Nat2Z.id, loop_to_field.
    unfold MontLadderCSwap.
    destruct (MontLadderCSwap_rec (Z.pos q) a24 m xP n ((1, 0, xP, 1), false))
      as [[[[X2 Z2] X3] Z3] prev].
    destruct prev; reflexivity.
  Qed.

  Lemma ladder_matches_fiat m xP n :
    affine_output (MontLadder (Z.pos q) a24 m xP n) =
    XZ.M.montladder (Fadd := F.add) (Fsub := F.sub) (Fmul := F.mul)
      (Fzero := F.zero) (Fone := F.one) (Finv := F.inv)
      (a24 := encode (a24 - 1)) (Z.of_nat m) (Z.testbit n) (encode xP).
  Proof. rewrite <- CSwap_eq. apply cswap_matches_fiat. Qed.
End FieldBridge.

Local Notation q25519 := (2^255-19)%positive.

Local Instance char_ge_28 :
    @Ring.char_ge (F q25519) eq F.zero F.one F.opp F.add F.sub F.mul 28.
Proof.
  eapply Hierarchy.char_ge_weaken; try apply F.char_gt. Decidable.vm_decide.
Qed.

Local Lemma curve_a24 :
  F.mul (F.add (F.add (F.add F.one F.one) F.one) F.one) (F.of_Z q25519 121665) =
  F.sub Curve25519.M.a (F.add F.one F.one).
Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

Local Lemma curve_nonsquare (r : F q25519) :
  F.mul r r <>
  F.sub (F.mul Curve25519.M.a Curve25519.M.a) (F.add (F.add (F.add F.one F.one) F.one) F.one).
Proof.
  intro Hsquare. apply Curve25519.M.a2m4_nonsq. exists r. exact Hsquare.
Qed.

Local Lemma fiat_curve25519_correct m n (P : Curve25519.M.point) :
  XZ.M.montladder (Fadd := F.add) (Fsub := F.sub) (Fmul := F.mul)
    (Fzero := F.zero) (Fone := F.one) (Finv := F.inv)
    (a24 := F.of_Z q25519 121665) (Z.of_nat m) (Z.testbit n) (Curve25519.M.X0 P) =
  Curve25519.M.X0 (Curve25519.M.scalarmult (n mod 2 ^ Z.of_nat m) P).
Proof.
  apply (XZProofs.M.montladder_correct
    (field := Curve25519.field) (char_ge_3 := Curve25519.char_ge_3)
    (char_ge_28 := char_ge_28) (a24_correct := curve_a24) (a2m4_nonsquare := curve_nonsquare)
    (b_nonzero := Curve25519.M.b_nonzero)).
  - apply F.inv_0.
  - lia.
Qed.

(* Affine x-coordinate output, with zero used for the point at infinity. *)
Definition curve25519_ladder (m : nat) (xP n : Z) : Z :=
  F.to_Z (affine_output q25519 (MontLadder (Z.pos q25519) 121666 m xP n)).

Definition curve25519_cswap (m : nat) (xP n : Z) : Z :=
  F.to_Z (affine_output q25519 (MontLadderCSwap (Z.pos q25519) 121666 m xP n)).

Theorem curve25519_ladder_correct_mod m n (P : Curve25519.M.point) :
  curve25519_ladder m (F.to_Z (Curve25519.M.X0 P)) n =
  F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult (n mod 2 ^ Z.of_nat m) P)).
Proof.
  unfold curve25519_ladder. rewrite ladder_matches_fiat, F.of_Z_to_Z.
  rewrite fiat_curve25519_correct. reflexivity.
Qed.

Theorem curve25519_ladder_correct m n (P : Curve25519.M.point) :
  0 <= n < 2 ^ Z.of_nat m ->
  curve25519_ladder m (F.to_Z (Curve25519.M.X0 P)) n =
  F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult n P)).
Proof.
  intro Hrange. rewrite curve25519_ladder_correct_mod, Z.mod_small by exact Hrange.
  reflexivity.
Qed.

Theorem curve25519_cswap_correct m n (P : Curve25519.M.point) :
  0 <= n < 2 ^ Z.of_nat m ->
  curve25519_cswap m (F.to_Z (Curve25519.M.X0 P)) n =
  F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult n P)).
Proof.
  unfold curve25519_cswap. rewrite CSwap_eq. apply curve25519_ladder_correct.
Qed.
End Curve25519Bridge.

Module Curve25519Machine.
  Local Notation q := (2^255-19)%positive.

  Definition modulus : bv 255 :=
    Z_to_bv 255 (Z.pos q).

  Definition inverse_exponent : positive :=
    (2^255-21)%positive.

  Definition program : list LadderMachine.instr :=
    LadderMachine.affine_program 255 inverse_exponent.

  Definition initial (x scalar : Z) : dual_circuit.state 255 :=
    LadderMachine.initial_state 255 (Z_to_bv 255 x) (Z_to_bv 255 121666) (Z_to_bv 255 scalar).

  Definition execute (x scalar : Z) :=
    LadderMachine.run 255 modulus (initial x scalar) program.

  Definition output (x scalar : Z) : Z :=
    LadderMachine.affine_result 255 (execute x scalar).1.

  Lemma modulus_unsigned : bv_unsigned modulus = Z.pos q.
  Proof. apply Z_to_bv_small. vm_compute. split; congruence. Qed.

  Local Lemma field_affine_power X Zc :
    F.to_Z (Curve25519Bridge.affine_output q (X, Zc)) = (X * Zc ^ Z.pos inverse_exponent) mod Z.pos q.
  Proof.
    unfold Curve25519Bridge.affine_output.
    rewrite (@F.Fq_inv_fermat q Curve25519.prime_p ltac:(vm_compute; reflexivity)).
    rewrite F.of_Z_pow, F.to_Z_mul, !F.to_Z_of_Z.
    repeat rewrite ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r, ?Z.mod_mod by (vm_compute; discriminate).
    reflexivity.
  Qed.

  Theorem program_correct (P : Curve25519.M.point) scalar :
    0 <= scalar < 2^255 ->
    output (F.to_Z (Curve25519.M.X0 P)) scalar = F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult scalar P)).
  Proof.
    intro Hscalar. unfold output, execute, initial, program.
    rewrite LadderMachine.affine_program_correct by (rewrite modulus_unsigned; vm_compute; reflexivity).
    rewrite modulus_unsigned.
    rewrite (Z_to_bv_small 255 scalar) by exact Hscalar.
    rewrite (Z_to_bv_small 255 121666) by (vm_compute; split; congruence).
    rewrite Z_to_bv_small.
    - rewrite <- Curve25519Bridge.curve25519_cswap_correct with (m := 255%nat) by exact Hscalar.
      unfold Curve25519Bridge.curve25519_cswap.
      destruct (ladder_math.MontLadderCSwap (Z.pos q) 121666 255 (F.to_Z (Curve25519.M.X0 P)) scalar).
      symmetry. apply field_affine_power.
    - pose proof (F.to_Z_range (Curve25519.M.X0 P) ltac:(vm_compute; reflexivity)) as H.
      change (0 <= F.to_Z (Curve25519.M.X0 P) < 2^255).
      change (0 <= F.to_Z (Curve25519.M.X0 P) < Z.pos q) in H.
      split; [lia |]. eapply Z.lt_trans; [exact (proj2 H) | vm_compute; reflexivity].
  Qed.

  Lemma program_length : length program = 7400%nat.
  Proof.
    unfold program, LadderMachine.affine_program. rewrite List.length_app, LadderMachine.projective_program_length.
    vm_compute. reflexivity.
  Qed.

  Lemma program_in_bounds : Forall (LadderMachine.in_bounds 28) program.
  Proof. apply LadderMachine.affine_program_in_bounds. Qed.

  Theorem program_secure x scalar :
    LadderMachine.hw_trace 255 modulus (initial x scalar) program = repeat 7140%nat 7401 /\
    (execute x scalar).2 = [] /\ dual_circuit.valid_state 255 (execute x scalar).1.
  Proof.
    pose proof (LadderMachine.affine_program_secure 255 modulus (Z_to_bv 255 x) (Z_to_bv 255 121666) (Z_to_bv 255 scalar) 255 inverse_exponent) as H.
    change (LadderMachine.hw_trace 255 modulus (initial x scalar) program = repeat 7140%nat (S (length program)) /\ (execute x scalar).2 = [] /\ dual_circuit.valid_state 255 (execute x scalar).1) in H.
    rewrite program_length in H. exact H.
  Qed.

  Theorem protected_ladder_correct_and_secure (P : Curve25519.M.point) scalar :
    0 <= scalar < 2^255 ->
    length program = 7400%nat /\
    Forall (LadderMachine.in_bounds 28) program /\
    output (F.to_Z (Curve25519.M.X0 P)) scalar = F.to_Z (Curve25519.M.X0 (Curve25519.M.scalarmult scalar P)) /\
    LadderMachine.hw_trace 255 modulus (initial (F.to_Z (Curve25519.M.X0 P)) scalar) program = repeat 7140%nat 7401 /\
    (execute (F.to_Z (Curve25519.M.X0 P)) scalar).2 = [] /\
    dual_circuit.valid_state 255 (execute (F.to_Z (Curve25519.M.X0 P)) scalar).1.
  Proof.
    intro Hscalar. split; [apply program_length |]. split; [apply program_in_bounds |].
    split; [apply program_correct; exact Hscalar | apply program_secure].
  Qed.

  Corollary power_trace_independent x scalar1 scalar2 :
    LadderMachine.hw_trace 255 modulus (initial x scalar1) program = LadderMachine.hw_trace 255 modulus (initial x scalar2) program.
  Proof. rewrite (proj1 (program_secure x scalar1)), (proj1 (program_secure x scalar2)). reflexivity. Qed.
End Curve25519Machine.
