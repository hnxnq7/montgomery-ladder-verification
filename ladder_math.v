Require Import ZArith.
Require Import Lia.
Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
From stdpp Require Import base.
From stdpp Require Import bitvector.
From stdpp Require Import list.
Open Scope Z_scope.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Record AffinePoint {p : Z} := {
  aX : Z;
  aY : Z;
  aX_range : 0 <= aX < p;
  aY_range : 0 <= aY < p
}.
Arguments AffinePoint : clear implicits.

(* A pair (pX, pZ) represents the affine value  pX * pZ^{-1} mod p.
   LadderStep works entirely in projective coords -> inversion happens once at the end via proj_to_affine. *)
Record ProjX (p : Z) := {
  pX : Z;
  pZ : Z
}.

Definition x_of {p : Z} (Q : AffinePoint p) : Z :=
  aX Q.


(* Math — integer-field LadderStep, conditional swap, and CSwap correctness *)
Section Montgomery.
  Variable p      : Z.             (* prime modulus *)
  Variable p_gt_0 : p > 0.
  Variable fp_inv : Z -> Z -> Z.   (* fp_inv p z = z^{-1} mod p *)
  Variable A24    : Z.             (* (A+2)/4 mod p precomputed from curve *)

  (* Field arithmetic *)
  Definition fadd (a b : Z) : Z :=
    (a + b) mod p.
  Definition fsub (a b : Z) : Z :=
    (a - b) mod p.
  Definition fmul (a b : Z) : Z :=
    (a * b) mod p.
  Definition fsq  (a : Z)   : Z :=
    fmul a a.

  Lemma fmul_bounded: forall (a b : Z), 0 <= fmul a b < p.
  Proof.
    intros. unfold fmul. apply Z.mod_pos_bound. lia.
  Qed.

  Create HintDb field.
  Hint Resolve fmul_bounded : field.

  Definition affine_to_proj (x : Z) : Z * Z :=
    (x, 1).
  Definition proj_to_affine (pX pZ : Z) : Z :=
    fmul pX (fp_inv p pZ).
  
  Parameter scalar_mul : Z -> AffinePoint p -> AffinePoint p.

  (* Doubling: given projective coords (X:Zc) for [k]P,
     the doubling formula outputs projective coords for [2k]P.
     Encodes: x(2P) = U²V² / ((U²-V²)(V²+A24(U²-V²)))
     where U=X+Z, V=X-Z *)
  Axiom doubling_formula : forall k (Q : AffinePoint p) (X Zc : Z), proj_to_affine X Zc = x_of (scalar_mul k Q) ->
    let U  := fadd X Zc in
    let V  := fsub X Zc in
    let U2 := fsq U in
    let V2 := fsq V in
    let d  := fsub U2 V2 in
    proj_to_affine (fmul U2 V2) (fmul d (fadd V2 (fmul A24 d))) = x_of (scalar_mul (2 * k) Q).
  
  (* Differential addition: given projective coords for [k]P and [k+1]P,
     and the affine x-coord of P, the formula outputs projective coords for [2k+1]P.
     Encodes: x(P+Q) = (UT+VW)² / (X1*(UT-VW)²)
     where U=X2+Z2, V=X2-Z2, W=X3+Z3, T=X3-Z3 *)
  Axiom diff_add_formula :
    forall k (Q : AffinePoint p) (X2 Z2 X3 Z3 X1 : Z),
    proj_to_affine X2 Z2 = x_of (scalar_mul k Q) ->
    proj_to_affine X3 Z3 = x_of (scalar_mul (k + 1) Q) ->
    X1 = x_of Q ->
    let U  := fadd X2 Z2 in
    let V  := fsub X2 Z2 in
    let W  := fadd X3 Z3 in
    let T  := fsub X3 Z3 in
    let Sp := fadd (fmul U T) (fmul V W) in
    let Sm := fsub (fmul U T) (fmul V W) in
    proj_to_affine (fsq Sp) (fmul (fsq Sm) X1) = x_of (scalar_mul (2 * k + 1) Q).

  (* LadderStep
     One iteration of the Montgomery differential-addition chain.
     Inputs:  X1 = x(P) (public base point, affine)
              (X2,Z2) = projective [k]P,  (X3,Z3) = projective [k+1]P
     Output: (X2',Z2',X3',Z3') = ([2k]P, [2k+1]P)                          *)
  Definition LadderStep (X1 X2 Z2 X3 Z3 : Z) : Z * Z * Z * Z :=
    let U  := fadd X2 Z2 in          (* U  = X2 + Z2  *)
    let V  := fsub X2 Z2 in          (* V  = X2 - Z2  *)
    let W  := fadd X3 Z3 in          (* W  = X3 + Z3  *)
    let T  := fsub X3 Z3 in          (* T  = X3 - Z3  *)

    let U2 := fsq U in               (* U^2            *)
    let V2 := fsq V in               (* V^2            *)

    let UT := fmul U T in            (* UT              *)
    let VW := fmul V W in            (* VW              *)
    let Sp := fadd UT VW in          (* UT + VW         *)
    let Sm := fsub UT VW in          (* UT - VW         *)

    let X3' := fsq Sp in             (* (UT + VW)^2           *)
    let Z3' := fmul (fsq Sm) X1 in  (* (UT - VW)^2 * X1      *)
    
    let X2'  := fmul U2 V2 in        (* U^2 * V^2                          *)
    let diff := fsub U2 V2 in        (* U^2 - V^2                           *)
    let Z2'  := fmul diff (fadd V2 (fmul A24 diff)) in (* (U^2-V^2)(V^2 + A24*(U^2-V^2))     *)
    (X2', Z2', X3', Z3').
  
  
  #[local] Hint Rewrite Zmult_mod_idemp_l Zmult_mod_idemp_r
    Zplus_mod_idemp_l Zplus_mod_idemp_r Zminus_mod_idemp_l Zminus_mod_idemp_r : ladder_mod.

  (* U²V² = (X²-Z²)²  i.e. the doubling numerator in its standard form.
     proof: (X+Z)²(X-Z)² = ((X+Z)(X-Z))² = (X²-Z²)²  by ring mod p *)
  Lemma doubling_num_algebra (X Zc : Z) : fmul (fsq (fadd X Zc)) (fsq (fsub X Zc)) = fsq (fsub (fsq X) (fsq Zc)).
  Proof.
    unfold fsq, fadd, fsub, fmul.
    rewrite_strat (bottomup (hints ladder_mod)).
    f_equal. ring.
  Qed.

  (* (UT+VW)² = 4(X₂X₃ - Z₂Z₃)²
     proof: UT+VW = 2(X₂X₃-Z₂Z₃)  by expanding, then square  *)
  Lemma diff_add_sum_algebra (X2 Z2 X3 Z3 : Z) :
    let U  := fadd X2 Z2 in let V := fsub X2 Z2 in
    let W  := fadd X3 Z3 in let T := fsub X3 Z3 in
    fsq (fadd (fmul U T) (fmul V W)) = fmul 4 (fsq (fsub (fmul X2 X3) (fmul Z2 Z3))).
  Proof.
    cbv zeta.
    unfold fsq, fadd, fsub, fmul.
    rewrite_strat (bottomup (hints ladder_mod)).
    f_equal. ring.
  Qed.

  (* (UT-VW)² = 4(X₂Z₃ - X₃Z₂)²
     proof: UT-VW = -2(X₂Z₃-X₃Z₂)  by expanding, then square *)
  Lemma diff_add_dif_algebra (X2 Z2 X3 Z3 : Z) :
    let U  := fadd X2 Z2 in let V := fsub X2 Z2 in
    let W  := fadd X3 Z3 in let T := fsub X3 Z3 in
    fsq (fsub (fmul U T) (fmul V W)) = fmul 4 (fsq (fsub (fmul X2 Z3) (fmul X3 Z2))).
  Proof.
    cbv zeta.
    unfold fsq, fadd, fsub, fmul.
    rewrite_strat (bottomup (hints ladder_mod)).
    f_equal. ring.
  Qed.

  Lemma LadderStep_correct (X1 X2 Z2 X3 Z3 k : Z) (P : AffinePoint p) :
    proj_to_affine X2 Z2 = x_of (scalar_mul k P) ->
    proj_to_affine X3 Z3 = x_of (scalar_mul (k + 1) P) ->
    X1 = x_of P ->
    let '(X2', Z2', X3', Z3') := LadderStep X1 X2 Z2 X3 Z3 in
    proj_to_affine X2' Z2' = x_of (scalar_mul (2 * k)     P) /\
    proj_to_affine X3' Z3' = x_of (scalar_mul (2 * k + 1) P).
  Proof.
    intros H_R0 H_R1 H_X1.
    unfold LadderStep. simpl.
    split.
    - exact (doubling_formula k P X2 Z2 H_R0).
    - exact (diff_add_formula k P X2 Z2 X3 Z3 X1 H_R0 H_R1 H_X1).
  Qed.

  
  (* algorithm 1 *)
  Definition MontLadder_step (X1 : Z) (bit : bool) (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
    let '(X2, Z2, X3, Z3) := st in
    if bit then
      let '(X3', Z3', X2', Z2') := LadderStep X1 X3 Z3 X2 Z2 in
      (X2', Z2', X3', Z3')
    else
      LadderStep X1 X2 Z2 X3 Z3.

  (* bit extraction *)
  Definition bit_i (n : Z) (i : nat) : bool :=
    Z.testbit n (Z.of_nat i).
  
  Fixpoint MontLadder_rec (m : nat) (X1 n : Z) (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
    match m with
    | O => st
    | S m' =>
        let bit := bit_i n m' in
        MontLadder_rec m' X1 n (MontLadder_step X1 bit st)
    end.

  Definition MontLadder (m : nat) (xP n : Z) : Z * Z :=
    let st0 := (1, 0, xP, 1) in
    let '(X2, Z2, _, _) := MontLadder_rec m xP n st0 in
    (X2, Z2).
  
  Tactic Notation "case_match_in" ident(H) "eqn" ":" ident(Hd) :=
    match type of H with
    | context [ match ?x with _ => _ end ] => destruct x eqn:Hd
    end.
  
  Tactic Notation "case_goal_match" "eqn" ":" ident(Hd) :=
    match goal with
    | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
    end.
  


  (* CSwap
     Algorithm 3: conditional swap of the (X2,Z2)/(X3,Z3) register pairs.
     The swap is controlled by bit b; when b=true the pairs are exchanged.  *)
  Definition CSwap (X2 Z2 X3 Z3 : Z) (b : bool) : Z * Z * Z * Z :=
    if b then (X3, Z3, X2, Z2) else (X2, Z2, X3, Z3).

  Definition MontLadderCSwap_step (X1 : Z) (bit prevbit : bool) (st : Z * Z * Z * Z) : (Z * Z * Z * Z) * bool :=
    let swap := xorb bit prevbit in
    let '(X2, Z2, X3, Z3) := st in
    let '(X2s, Z2s, X3s, Z3s) := CSwap X2 Z2 X3 Z3 swap in
    let '(X2', Z2', X3', Z3') := LadderStep X1 X2s Z2s X3s Z3s in
    ((X2', Z2', X3', Z3'), bit).
  
  Fixpoint MontLadderCSwap_rec (m : nat) (X1 n : Z) (st : (Z * Z * Z * Z) * bool) : (Z * Z * Z * Z) * bool :=
    match m with
    | O => st
    | S m' =>
        let '(regs, prevbit) := st in
        let bit := bit_i n m' in
        let st' := MontLadderCSwap_step X1 bit prevbit regs in
        MontLadderCSwap_rec m' X1 n st'
    end.

  Definition MontLadderCSwap (m : nat) (xP n : Z) : Z * Z :=
    let st0 := ((1, 0, xP, 1), false) in
    let '(regs, final_prev) := MontLadderCSwap_rec m xP n st0 in
    (* normalize: if final_prev=true the registers are still swapped *)
    let '(X2, Z2, X3, Z3) := regs in
    let '(X2f, Z2f, _, _) := CSwap X2 Z2 X3 Z3 final_prev in
    (X2f, Z2f).

  (* swap the two projective register pairs *)
  Definition swap_regs (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
    let '(X2, Z2, X3, Z3) := st in (X3, Z3, X2, Z2).

  (* undo the current logical swap: if swapped=true, flip back *)
  Definition norm_regs (st : Z * Z * Z * Z) (swapped : bool) : Z * Z * Z * Z :=
    if swapped then swap_regs st else st.
  
  (* One step of Algorithm 3, when normalized by its output swap bit,
   equals one step of Algorithm 1 starting from the normalized input. *)
  Lemma MontLadder_step_norm: forall X1 X2 Z2 X3 Z3 (prev bit : bool),
    let '(regs3, new_prev) := MontLadderCSwap_step X1 bit prev (X2, Z2, X3, Z3) in
    norm_regs regs3 new_prev = MontLadder_step X1 bit (norm_regs (X2, Z2, X3, Z3) prev).
  Proof.
    intros.
    unfold MontLadderCSwap_step, MontLadder_step, CSwap, norm_regs, swap_regs.
    (* case split on all four combinations of prev and bit *)
    destruct prev, bit; simpl; try reflexivity.
  Qed.

  Lemma simple_tuple_inversion: forall {A} {B} (a: A) (b: B) x y, (a,b) = (x,y) -> a = x /\ b = y.
  Proof.
    intros. inversion H. auto.
  Qed.

  Ltac simplify_tuples :=
    repeat match goal with
    | [ H: (_,_) = (_,_) |- _ ] =>
        let H1 := fresh H in
        let H2 := fresh H in
      apply simple_tuple_inversion in H; destruct H as [H1 H2]
    end.
  
  Ltac simplify_tupless :=
    simplify_tuples; subst.

  Lemma rec_eq : forall m xP n st st' st1 st1' prev new_prev,
    (* let '(regs3, new_prev) := MontLadderCSwap_rec m xP n (st, prev) in norm_regs regs3 new_prev
    = MontLadder_rec m xP n st. *)

    st1 = norm_regs st prev ->
    MontLadderCSwap_rec m xP n (st, prev) = (st', new_prev) ->
    MontLadder_rec m xP n st1 = st1' ->
    st1' = norm_regs st' new_prev.
  Proof.
    induction m.
    - simpl. intros. simplify_tupless. reflexivity.
    - intros xP n st st' st1 st1' prev new_prev H_norm H_cswap H_ladder.
      destruct st as [[[X2 Z2] X3] Z3].
      cbn [MontLadderCSwap_rec MontLadder_rec] in H_cswap, H_ladder.
      set (bit := bit_i n m) in *. (* name current bit *)
      remember (MontLadderCSwap_step xP bit prev (X2, Z2, X3, Z3)) as step_res eqn:H_step. (* freeze intermediate state/result *)
      destruct step_res as [st_mid bit_mid].
      pose proof (MontLadder_step_norm xP X2 Z2 X3 Z3 prev bit) as H_sn.
      rewrite <- H_step in H_sn.
      cbn in H_sn.
      rewrite <- H_norm in H_sn.
      apply (IHm xP n st_mid st' (MontLadder_step xP bit st1) st1' bit_mid new_prev).
      + symmetry. exact H_sn.
      + exact H_cswap.
      + exact H_ladder.
  Qed.

  (* CSwap_eq
     Correctness: Algorithm 1 (MontLadder) and Algorithm 3 (MontLadderCSwap)
     produce identical outputs for every input.                               *)
  Lemma CSwap_eq m xP n : MontLadderCSwap m xP n = MontLadder m xP n.
  Proof.
    unfold MontLadderCSwap, MontLadder.
    remember (MontLadderCSwap_rec m xP n ((1, 0, xP, 1), false)) as cswap_res eqn:HCSwap.
    destruct cswap_res as [st' final_prev].
    remember (MontLadder_rec m xP n (1, 0, xP, 1)) as ladder_res eqn:Hladder.
    assert (H_eq : ladder_res = norm_regs st' final_prev).
    { apply (rec_eq m xP n (1, 0, xP, 1) st' (1, 0, xP, 1) ladder_res false final_prev).
      (* (1,0,xP,1) = norm_regs (1,0,xP,1) false - trivially true since norm_regs _ false = id
          CSwap-rec output = (st', final_prev) -> HCSwap
          Ladder-rec output = ladder_res *)
      - reflexivity.        (* norm_regs (1,0,xP,1) false = (1,0,xP,1) *)
      - symmetry. exact HCSwap.
      - symmetry. exact Hladder. }
    destruct st' as [[[X2' Z2'] X3'] Z3'].
    rewrite H_eq.
    destruct final_prev; simpl; reflexivity.
  Qed.

  Definition xDBL (X Zc : Z) : Z * Z :=
    let U2 := fsq (fadd X Zc) in
    let V2 := fsq (fsub X Zc) in
    let d := fsub U2 V2 in
    (fmul U2 V2, fmul d (fadd V2 (fmul A24 d))).

  Definition xADD (xP X2 Z2 X3 Z3 : Z) : Z * Z :=
    let UT := fmul (fadd X2 Z2) (fsub X3 Z3) in
    let VW := fmul (fsub X2 Z2) (fadd X3 Z3) in
    (fsq (fadd UT VW), fmul (fsq (fsub UT VW)) xP).

  Lemma LadderStep_decompose xP X2 Z2 X3 Z3 :
    LadderStep xP X2 Z2 X3 Z3 =
    let '(Xd, Zd) := xDBL X2 Z2 in
    let '(Xa, Za) := xADD xP X2 Z2 X3 Z3 in
    (Xd, Zd, Xa, Za).
  Proof. reflexivity. Qed.

  Lemma xADD_symmetric xP X2 Z2 X3 Z3 :
    xADD xP X2 Z2 X3 Z3 = xADD xP X3 Z3 X2 Z2.
  Proof.
    unfold xADD.
    rewrite !diff_add_sum_algebra, !diff_add_dif_algebra.
    unfold fsq, fadd, fsub, fmul.
    rewrite_strat (bottomup (hints ladder_mod)).
    f_equal; f_equal; ring.
  Qed.

  (* The scalar obtained by appending the remaining m bits to prefix k. *)
  Fixpoint ladder_index (m : nat) (n k : Z) : Z :=
    match m with
    | O => k
    | S m' => ladder_index m' n (2 * k + if bit_i n m' then 1 else 0)
    end.

  Lemma ladder_index_value m n k :
    ladder_index m n k = k * 2 ^ Z.of_nat m + n mod 2 ^ Z.of_nat m.
  Proof.
    clear -m n k.
    revert k. induction m as [|m IH]; intro k.
    - change (k = k * 1 + n mod 1). rewrite Z.mod_1_r. ring.
    - cbn [ladder_index]. rewrite IH.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite Z.mul_comm with (n := 2) (m := 2 ^ Z.of_nat m).
      rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; lia).
      unfold bit_i.
      pose proof (Z.testbit_spec' n (Z.of_nat m) (Nat2Z.is_nonneg m)) as Hbit.
      destruct (Z.testbit n (Z.of_nat m)); cbn in Hbit; rewrite <- Hbit; ring.
  Qed.

  (* Loop correctness, conditional on a projective model of scalar multiples.
     Instantiating this contract for an actual curve remains to be proved. *)
  Section ProjectiveContract.
    Variable xP : Z.
    (* represents k X Zc means that (X:Zc) represents [k]P. *)
    Variable represents : Z -> Z -> Z -> Prop.
    Hypothesis represents_zero : represents 0 1 0.
    Hypothesis represents_one : represents 1 xP 1.
    Hypothesis xDBL_correct : forall k X Zc,
      represents k X Zc ->
      let '(Xd, Zd) := xDBL X Zc in represents (2 * k) Xd Zd.
    Hypothesis xADD_correct : forall k X2 Z2 X3 Z3,
      represents k X2 Z2 -> represents (k + 1) X3 Z3 ->
      let '(Xa, Za) := xADD xP X2 Z2 X3 Z3 in represents (2 * k + 1) Xa Za.

    Definition ladder_invariant (k : Z) (st : Z * Z * Z * Z) : Prop :=
      let '(X2, Z2, X3, Z3) := st in
      represents k X2 Z2 /\ represents (k + 1) X3 Z3.

    Lemma MontLadder_step_invariant k (bit : bool) st :
      ladder_invariant k st ->
      ladder_invariant (2 * k + if bit then 1 else 0) (MontLadder_step xP bit st).
    Proof.
      destruct st as [[[X2 Z2] X3] Z3]. intros [H0 H1].
      pose proof (xADD_correct k X2 Z2 X3 Z3 H0 H1) as Ha.
      destruct bit; cbn [MontLadder_step]; rewrite LadderStep_decompose.
      - pose proof (xDBL_correct (k + 1) X3 Z3 H1) as Hd.
        rewrite <- xADD_symmetric.
        destruct (xDBL X3 Z3) as [Xd Zd].
        destruct (xADD xP X2 Z2 X3 Z3) as [Xa Za].
        cbn [ladder_invariant]. split; [exact Ha|].
        replace (2 * k + 1 + 1) with (2 * (k + 1)) by ring. exact Hd.
      - pose proof (xDBL_correct k X2 Z2 H0) as Hd.
        destruct (xDBL X2 Z2) as [Xd Zd].
        destruct (xADD xP X2 Z2 X3 Z3) as [Xa Za].
        cbn [ladder_invariant]. rewrite Z.add_0_r. split; assumption.
    Qed.

    Lemma MontLadder_rec_invariant m n k st :
      ladder_invariant k st ->
      ladder_invariant (ladder_index m n k) (MontLadder_rec m xP n st).
    Proof.
      revert k st. induction m as [|m IH]; intros k st Hinv.
      - exact Hinv.
      - cbn [ladder_index MontLadder_rec]. apply IH.
        apply MontLadder_step_invariant. exact Hinv.
    Qed.

    (* Without a width bound the algorithm computes the low m bits of n. *)
    Theorem MontLadder_correct_mod m n :
      let '(X, Zc) := MontLadder m xP n in
      represents (n mod 2 ^ Z.of_nat m) X Zc.
    Proof.
      assert (Hinit : ladder_invariant 0 (1, 0, xP, 1)).
      { split; assumption. }
      pose proof (MontLadder_rec_invariant m n 0 _ Hinit) as Hrun.
      rewrite ladder_index_value, Z.mul_0_l, Z.add_0_l in Hrun.
      unfold MontLadder.
      destruct (MontLadder_rec m xP n (1, 0, xP, 1)) as [[[X Zc] Xnext] Znext].
      exact (proj1 Hrun).
    Qed.

    Theorem MontLadder_correct m n :
      0 <= n < 2 ^ Z.of_nat m ->
      let '(X, Zc) := MontLadder m xP n in represents n X Zc.
    Proof.
      intro Hrange. pose proof (MontLadder_correct_mod m n) as H.
      rewrite Z.mod_small in H by exact Hrange. exact H.
    Qed.

    Theorem MontLadderCSwap_correct m n :
      0 <= n < 2 ^ Z.of_nat m ->
      let '(X, Zc) := MontLadderCSwap m xP n in represents n X Zc.
    Proof.
      rewrite CSwap_eq. apply MontLadder_correct.
    Qed.
  End ProjectiveContract.

  (* 1. Define HW of a bv *)
  (* 2. Define operations given inputs associated with uniformly random vars *)
      (* HW of a + uniformly random var --> HW of something uniformly random var *)
  (* 3. start thinking of defining a language w/ only the field operations *)

  (* Definition masked_add_secure :=
  forall (a1 a2 b r : bv n),
  distribution of numOfOnes((a1 XOR r) + b) over uniform r
     = distribution of numOfOnes((a2 XOR r) + b) * *)
End Montgomery.

