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
   LadderStep works entirely in projective coords - inversion happens once at the end via proj_to_affine. *)
Record ProjX (p : Z) := {
  pX : Z;
  pZ : Z
}.

Definition x_of {p : Z} (Q : AffinePoint p) : Z := aX Q.

(* ══════════════════════════════════════════════════════════════════════════════
   Math — integer-field LadderStep, conditional swap, and CSwap correctness
   ══════════════════════════════════════════════════════════════════════════════ *)
Section Montgomery.
  Variable p      : Z.             (* prime modulus                          *)
  Variable p_gt_0 : p > 0.
  Variable fp_inv : Z -> Z -> Z.   (* fp_inv p z = z^{-1} mod p             *)
  Variable A24    : Z.             (* (A+2)/4 mod p precomputed from curve  *)

  (* ── Field arithmetic ───────────────────────────────────────────────────── *)
  Definition fadd (a b : Z) : Z := (a + b) mod p.
  Definition fsub (a b : Z) : Z := (a - b) mod p.
  Definition fmul (a b : Z) : Z := (a * b) mod p.
  Definition fsq  (a : Z)   : Z := fmul a a.

  Lemma fmul_bounded:
    forall (a b : Z),
    0 <= fmul a b < p.
  Proof.
    intros. unfold fmul. apply Z.mod_pos_bound. lia.
  Qed.

  Create HintDb field.
  Hint Resolve fmul_bounded : field.

  (* Definition scalar_mul (k : Z) (point : AffinePoint p) : AffinePoint p.
  Proof.
    refine {|
      aX := fmul point.(aX) k;
      aY := fmul point.(aY) k;
      aX_range := _;
      aY_range := _;
    |}.
    all: auto with field.
  Qed. *)

  Definition affine_to_proj (x : Z) : Z * Z := (x, 1).
  Definition proj_to_affine (pX pZ : Z) : Z :=
    fmul pX (fp_inv p pZ).
  
  Parameter scalar_mul : Z -> AffinePoint p -> AffinePoint p.

  (* Doubling: given projective coords (X:Zc) for [k]P,
     the doubling formula outputs projective coords for [2k]P.
     Encodes: x(2P) = U²V² / ((U²-V²)(V²+A24(U²-V²)))
     where U=X+Z, V=X-Z *)
  Axiom doubling_formula :
    forall k (Q : AffinePoint p) (X Zc : Z),
    proj_to_affine X Zc = x_of (scalar_mul k Q) ->
    let U  := fadd X Zc in
    let V  := fsub X Zc in
    let U2 := fsq U in
    let V2 := fsq V in
    let d  := fsub U2 V2 in
    proj_to_affine (fmul U2 V2) (fmul d (fadd V2 (fmul A24 d))) =
      x_of (scalar_mul (2 * k) Q).
  
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
    proj_to_affine (fsq Sp) (fmul (fsq Sm) X1) =
      x_of (scalar_mul (2 * k + 1) Q).

  (* ── LadderStep ────────────────────────────────────────────────────────────
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
    let Z2'  := fmul diff
                  (fadd V2 (fmul A24 diff)) in (* (U^2-V^2)(V^2 + A24*(U^2-V^2))     *)
    (X2', Z2', X3', Z3').
  
  
  (* U²V² = (X²-Z²)²  i.e. the doubling numerator in its standard form.
     proof: (X+Z)²(X-Z)² = ((X+Z)(X-Z))² = (X²-Z²)²  by ring mod p *)
  Lemma doubling_num_algebra (X Zc : Z) :
    fmul (fsq (fadd X Zc)) (fsq (fsub X Zc)) =
      fsq (fsub (fsq X) (fsq Zc)).
  Proof.
    unfold fsq, fadd, fsub, fmul.
    rewrite ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r,
            ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r.
    f_equal.
  Admitted.

  (* (UT+VW)² = 4(X₂X₃ - Z₂Z₃)²
     proof: UT+VW = 2(X₂X₃-Z₂Z₃)  by expanding, then square  *)
  Lemma diff_add_sum_algebra (X2 Z2 X3 Z3 : Z) :
    let U  := fadd X2 Z2 in let V := fsub X2 Z2 in
    let W  := fadd X3 Z3 in let T := fsub X3 Z3 in
    fsq (fadd (fmul U T) (fmul V W)) =
      fmul 4 (fsq (fsub (fmul X2 X3) (fmul Z2 Z3))).
  Admitted.

  (* (UT-VW)² = 4(X₂Z₃ - X₃Z₂)²
     proof: UT-VW = -2(X₂Z₃-X₃Z₂)  by expanding, then square *)
  Lemma diff_add_dif_algebra (X2 Z2 X3 Z3 : Z) :
    let U  := fadd X2 Z2 in let V := fsub X2 Z2 in
    let W  := fadd X3 Z3 in let T := fsub X3 Z3 in
    fsq (fsub (fmul U T) (fmul V W)) =
      fmul 4 (fsq (fsub (fmul X2 Z3) (fmul X3 Z2))).
  Admitted.

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
  Definition MontLadder_step
      (X1 : Z) (bit : bool) (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
    let '(X2, Z2, X3, Z3) := st in
    if bit then
      let '(X3', Z3', X2', Z2') := LadderStep X1 X3 Z3 X2 Z2 in
      (X2', Z2', X3', Z3')
    else
      LadderStep X1 X2 Z2 X3 Z3.

  (* bit extraction *)
  Definition bit_i (n : Z) (i : nat) : bool :=
    Z.testbit n (Z.of_nat i).
  
  Fixpoint MontLadder_rec
      (m : nat) (X1 n : Z) (st : Z * Z * Z * Z) : Z * Z * Z * Z :=
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
  
  (* Lemma MontLadder_rec_correct:
    forall m X1 n,
    MontLadder_rec m X1 N =  *)

  (* invariant proof *)
  (* for each st n+1 -> X3 *)
  (* given x-coord xP of a point P --> x-coord of nP *)
  (* Lemma MontLadder_correct:
    forall (m : nat) (xP n : Z) x' z',
    MontLadder m xP n = (x', z') -> x' = fmul n xP.
  Proof.
    intros. unfold MontLadder in *.
    case_match_in H eqn : Hrec. *)

  (* ── CSwap ─────────────────────────────────────────────────────────────────
     Algorithm 3: conditional swap of the (X2,Z2)/(X3,Z3) register pairs.
     The swap is controlled by bit b; when b=true the pairs are exchanged.  *)
  Definition CSwap
      (X2 Z2 X3 Z3 : Z) (b : bool) : Z * Z * Z * Z :=
    if b
    then (X3, Z3, X2, Z2)
    else (X2, Z2, X3, Z3).

  Definition MontLadderCSwap_step
      (X1 : Z) (bit prevbit : bool) (st : Z * Z * Z * Z)
      : (Z * Z * Z * Z) * bool :=
    let swap := xorb bit prevbit in
    let '(X2, Z2, X3, Z3) := st in
    let '(X2s, Z2s, X3s, Z3s) := CSwap X2 Z2 X3 Z3 swap in
    let '(X2', Z2', X3', Z3') := LadderStep X1 X2s Z2s X3s Z3s in
    ((X2', Z2', X3', Z3'), bit).
  
  Fixpoint MontLadderCSwap_rec
      (m : nat) (X1 n : Z)
      (st : (Z * Z * Z * Z) * bool)
      : (Z * Z * Z * Z) * bool :=
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
  Lemma MontLadder_step_norm:
    forall X1 X2 Z2 X3 Z3 (prev bit : bool),
    let '(regs3, new_prev) := MontLadderCSwap_step X1 bit prev (X2, Z2, X3, Z3) in
    norm_regs regs3 new_prev
    = MontLadder_step X1 bit (norm_regs (X2, Z2, X3, Z3) prev).
  Proof.
    intros.
    unfold MontLadderCSwap_step, MontLadder_step, CSwap, norm_regs, swap_regs.
    (* case split on all four combinations of prev and bit *)
    destruct prev, bit; simpl; try reflexivity.
  Qed.

  Lemma simple_tuple_inversion:
    forall {A} {B} (a: A) (b: B) x y,
    (a,b) = (x,y) ->
    a = x /\ b = y.
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
  
  Ltac simplify_tupless := simplify_tuples; subst.

  Lemma rec_eq : 
    forall m xP n st st' st1 st1' prev new_prev,
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

  (* ── CSwap_eq ───────────────────────────────────────────────────────────────
     Correctness: Algorithm 1 (MontLadder) and Algorithm 3 (MontLadderCSwap)
     produce identical outputs for every input.                               *)
  Lemma CSwap_eq m xP n :
    MontLadderCSwap m xP n = MontLadder m xP n.
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

  (* 1. Define HW of a bv *)
  (* 2. Define operations given inputs associated with uniformly random vars *)
      (* HW of a + uniformly random var --> HW of something uniformly random var *)
  (* 3. start thinking of defining a language w/ only the field operations *)

  (* Definition masked_add_secure :=
  forall (a1 a2 b r : bv n),
  distribution of numOfOnes((a1 XOR r) + b) over uniform r
     = distribution of numOfOnes((a2 XOR r) + b) * *)
End Montgomery.

Section HammingWeight.
  Variable n : N. (* width of bv *)
  Variable p : bv n.

  (* ══════════════════════════════════════════════════════════════════════════
     Field arithmetic — bitvector versions of fadd/fsub/fmul (reduction mod p)
     ══════════════════════════════════════════════════════════════════════════ *)
  Definition fadd_bv (a b : bv n) : bv n := bv_modu (bv_add a b) p .
  Definition fsub_bv (a b : bv n) : bv n := bv_modu (bv_sub a b) p.
  Definition fmul_bv (a b : bv n) : bv n := bv_modu (bv_mul a b) p.
  Definition fsq_bv  (a : bv n)   : bv n := fmul_bv a a.

  (* ══════════════════════════════════════════════════════════════════════════
     Probabilistic model — infrastructure for a future information-theoretic
     leakage argument (not yet connected to the main proof chain)
     ══════════════════════════════════════════════════════════════════════════ *)
  Inductive ProbType :=
    | Prob_concrete
    | Prob_random (* seed *)
    | Prob_unknown.
  
  Record ProbVar :=
  { Value : bv n;
    Ptype : ProbType
  }.

   (* ProbVar version *)
  Definition faddsub_prob (a b : ProbType) : ProbType := 
    match a, b with
    | Prob_unknown, _ => Prob_unknown
    | _, Prob_unknown => Prob_unknown
    | Prob_concrete, Prob_concrete => Prob_concrete
    | Prob_concrete, Prob_random => Prob_random
    | Prob_random, Prob_concrete => Prob_random
    | Prob_random, Prob_random => Prob_random
    end.

  Definition fmul_prob (a b : ProbType) : ProbType := 
    match a, b with
    | Prob_unknown, _ => Prob_unknown
    | _, Prob_unknown => Prob_unknown
    | Prob_concrete, Prob_concrete => Prob_concrete
    | Prob_concrete, Prob_random => Prob_random
    | Prob_random, Prob_concrete => Prob_random
    | Prob_random, Prob_random => Prob_unknown
    end.
  
  Definition fadd_probvar (a b : ProbVar) : ProbVar := {|
    Value := fadd_bv a.(Value) b.(Value);
    Ptype := faddsub_prob a.(Ptype) b.(Ptype)
  |}.

  (* NEW: sub and mul *)
  Definition fsub_probvar (a b : ProbVar) : ProbVar := {|
    Value := fsub_bv a.(Value) b.(Value);
    Ptype := faddsub_prob a.(Ptype) b.(Ptype)
  |}.

  Definition fmul_probvar (a b : ProbVar) : ProbVar := {|
    Value := fmul_bv a.(Value) b.(Value);
    Ptype := fmul_prob a.(Ptype) b.(Ptype)
  |}.

  (* another direction: duplicate circuit --> invert? --> HW same without masking *)
    (* would be cool *)

  Inductive ProbHW :=
    | ProbHW_concrete (n : N)
    | ProbHW_random
    | ProbHW_unknown.
  
  (* ══════════════════════════════════════════════════════════════════════════
     Register machine ISA — toy language used to model LadderStep execution
     ══════════════════════════════════════════════════════════════════════════ *)
  Definition var := nat.

  Inductive instr : Type :=
    (* | Constant (c : ProbVar)
    | Var      (i : nat) 
    | Add (a b : var)
    | Sub (a b : var)
    | Mul (a b : var). *)

    | IAdd (rd rs1 rs2 : var)
    | ISub (rd rs1 rs2 : var)
    | IMul (rd rs1 rs2 : var)
    | Observe (rd : var).
  
  Open Scope nat.

  Notation rX1  := 0  (only parsing).
  Notation rX2  := 1  (only parsing).
  Notation rZ2  := 2  (only parsing).
  Notation rX3  := 3  (only parsing).
  Notation rZ3  := 4  (only parsing).
  Notation rA24 := 5  (only parsing).
  Notation rU   := 6  (only parsing).   (* X2 + Z2 *)
  Notation rV   := 7  (only parsing).   (* X2 - Z2 *)
  Notation rW   := 8  (only parsing).   (* X3 + Z3 *)
  Notation rT   := 9  (only parsing).   (* X3 - Z3 *)
  Notation rU2  := 10 (only parsing).   (* U*U *)
  Notation rV2  := 11 (only parsing).   (* V*V *)
  Notation rUT  := 12 (only parsing).   (* U*T *)
  Notation rVW  := 13 (only parsing).   (* V*W *)
  Notation rSp  := 14 (only parsing).   (* UT + VW *)
  Notation rSm  := 15 (only parsing).   (* UT - VW *)
  Notation rX3' := 16 (only parsing).   (* Sp^2 *)
  Notation rSm2 := 17 (only parsing).   (* Sm^2 *)
  Notation rZ3' := 18 (only parsing).   (* Sm2 * X1 *)
  Notation rX2' := 19 (only parsing).   (* U2 * V2 *)
  Notation rD   := 20 (only parsing).   (* U2 - V2 *)
  Notation rAD  := 21 (only parsing).   (* A24 * D *)
  Notation rT2  := 22 (only parsing).   (* V2 + AD *)
  Notation rZ2' := 23 (only parsing).   (* D * T2 *)


  Definition program : list instr :=
    [ IAdd rU   rX2  rZ2    (* U   = X2 + Z2 *)
    ; ISub rV   rX2  rZ2    (* V   = X2 - Z2 *)
    ; IAdd rW   rX3  rZ3    (* W   = X3 + Z3 *)
    ; ISub rT   rX3  rZ3    (* T   = X3 - Z3 *)
    ; IMul rU2  rU   rU     (* U2  = U  * U *)
    ; IMul rV2  rV   rV     (* V2  = V  * V *)
    ; IMul rUT  rU   rT     (* UT  = U  * T *)
    ; IMul rVW  rV   rW     (* VW  = V  * W *)
    ; IAdd rSp  rUT  rVW    (* Sp  = UT + VW *)
    ; ISub rSm  rUT  rVW    (* Sm  = UT - VW *)
    ; IMul rX3' rSp  rSp    (* X3' = Sp^2 *)
    ; IMul rSm2 rSm  rSm    (* Sm2 = Sm^2 *)
    ; IMul rZ3' rSm2 rX1    (* Z3' = Sm2 * X1 *)
    ; IMul rX2' rU2  rV2    (* X2' = U2 * V2 *)
    ; ISub rD   rU2  rV2    (* D   = U2 - V2 *)
    ; IMul rAD  rA24 rD     (* AD  = A24 * D *)
    ; IAdd rT2  rV2  rAD    (* T2  = V2 + AD *)
    ; IMul rZ2' rD   rT2    (* Z2' = D * T2 *)
    ].
  
  (* todo: reuse registers --> use less regs *)
    (* program counter & fetch memory *)

  Definition ProbEnv := list ProbVar.

  Definition prob_default_var : ProbVar := {|
    Value := bv_0 n;
    Ptype := Prob_unknown
  |}.
  
  (* secret register & public register --> only do dual circuits on the secret *)

  Definition prob_read_register (env : ProbEnv) (i : var) : ProbVar := nth i env prob_default_var.
  Definition prob_write_register (env : ProbEnv) (i : var) (data : ProbVar) : ProbEnv := list_insert i data env.

  Definition num_true (bools : list bool) : nat :=
    fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) bools 0.

  Definition HW (a : bv n) : nat := num_true (bv_to_bits a).

  Definition num_1s (a : bv n) : nat :=
    num_true (bv_to_bits a).
  
  Definition num_1s_in_list (bvs : list (bv n)) : nat :=
    fold_left (fun acc pv => acc + HW pv) bvs 0.

  Definition num_1s_in_env (env : ProbEnv) : nat :=
    num_1s_in_list (map Value env).

  Inductive Observation :=
    | RegObservation (r : var) (val : (bv n)).

  Definition prob_interp_instr (env : ProbEnv) (e : instr) : ProbEnv * list Observation :=
    match e with
    (* | Constant c => c *)
    (* | Var i      => nth i env default_var *)
    | IAdd rd a b    => (prob_write_register env rd (fadd_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | ISub rd a b    => (prob_write_register env rd (fsub_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | IMul rd a b    => (prob_write_register env rd (fmul_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | Observe rd     => (env, [RegObservation rd (prob_read_register env rd).(Value)])
    end.
  
  
  (* ══════════════════════════════════════════════════════════════════════════
     Dual Circuit — side-channel security proof via complementary register bank
     ══════════════════════════════════════════════════════════════════════════ *)
  Section DualCircuit.

    (* ── Operational semantics ───────────────────────────────────────────── *)

    Definition Env := list (bv n).
    Record state := { env : Env; denv : Env }.

    Definition default_var : bv n := bv_0 n.
    Definition read_register  (env : Env) (i : var) : bv n      := nth i env default_var.
    Definition write_register (env : Env) (i : var) (data : bv n) : Env := list_insert i data env.

    Definition interp_instr (env : Env) (e : instr) : Env * list Observation :=
      match e with
      | IAdd rd a b => (write_register env rd (fadd_bv (read_register env a) (read_register env b)), [])
      | ISub rd a b => (write_register env rd (fsub_bv (read_register env a) (read_register env b)), [])
      | IMul rd a b => (write_register env rd (fmul_bv (read_register env a) (read_register env b)), [])
      | Observe rd  => (env, [RegObservation rd (read_register env rd)])
      end.

    (* dual circuit: env holds actual values, denv = map bv_not env *)
    Definition dual_interp_instr (s : state) (e : instr) : state * list Observation :=
      let '(env', obs) := interp_instr s.(env) e in
      ({| env := env'; denv := map bv_not env' |}, obs).

    (* run first [steps] instructions, accumulating observations *)
    Definition run (s : state) (prog : list instr) (steps : nat) : state * list Observation :=
      fold_left
        (fun '(s_acc, obs_acc) e =>
          let '(s', new_obs) := dual_interp_instr s_acc e in
          (s', obs_acc ++ new_obs))
        (firstn steps prog) (s, []).

      

    (* Security definitions *)

    (* invariant: denv is always the bitwise complement of env *)
    Definition valid_state (s : state) : Prop :=
      s.(denv) = map bv_not s.(env).

    Definition is_complement (e1 e2 : Env) : Prop :=
      forall i, read_register e2 i = bv_not (read_register e1 i).

    Definition num_1s_in_state (s : state) : nat :=
      num_1s_in_list s.(env) + num_1s_in_list s.(denv).

    (* security: total HW per cycle is constant regardless of secret *)
    Definition secure (prog : list instr) (s : state) :=
      exists c, forall steps, num_1s_in_state (run s prog steps).1 = c.



    (* ── Preservation lemmas ─────────────────────────────────────────────── *)

    Lemma write_register_length : forall (e : Env) (i : var) (v : bv n),
      length (write_register e i v) = length e.
    Proof. intros e i v. unfold write_register. apply length_insert. Qed.

    (* Reading back a register you just wrote returns the written value. *)
    Lemma read_register_write_same : forall (e : Env) (i : var) (v : bv n),
      i < length e ->
      read_register (write_register e i v) i = v.
    Proof.
      intros e. induction e as [| x xs IH]; intros i v Hi.
      - simpl in Hi. lia.
      - destruct i; simpl; [reflexivity | apply IH; simpl in Hi; lia].
    Qed.

    (* Reading a register other than the one written returns the original value. *)
    Lemma read_register_write_diff : forall (e : Env) (i j : var) (v : bv n),
      i <> j ->
      read_register (write_register e i v) j = read_register e j.
    Proof.
      intros e. induction e as [| x xs IH]; intros i j v Hij.
      - reflexivity.
      - destruct i as [| i'], j as [| j']; simpl.
        + contradiction.
        + reflexivity.
        + reflexivity.
        + apply IH. intro H. apply Hij. f_equal. exact H.
    Qed.

    Lemma interp_instr_preserves_length : forall (e : Env) (i : instr),
      length (interp_instr e i).1 = length e.
    Proof.
      intros e i. destruct i; simpl; rewrite ?write_register_length; reflexivity.
    Qed.

    (* Arithmetic ops only write to their destination rd.
       Reading any other register r from env' gives the same value as from env. *)
    Lemma interp_instr_read_other : forall (env0 : Env) (e : instr) (r : var),
      (match e with
       | IAdd rd _ _ | ISub rd _ _ | IMul rd _ _ => r <> rd
       | Observe _                                => True
       end) ->
      read_register (interp_instr env0 e).1 r = read_register env0 r.
    Proof.
      intros env0 e r He.
      destruct e as [rd rs1 rs2 | rd rs1 rs2 | rd rs1 rs2 | ro]; simpl in *.
      all: try (apply read_register_write_diff; intro H; exact (He (eq_sym H))).
      reflexivity.
    Qed.

    Lemma dual_interp_preserves_length : forall (s : state) (i : instr),
      length (env (dual_interp_instr s i).1) = length (env s).
    Proof.
      intros s i. unfold dual_interp_instr.
      destruct (interp_instr s.(env) i) as [env' obs] eqn:H.
      simpl. rewrite <- (interp_instr_preserves_length s.(env) i). rewrite H. reflexivity.
    Qed.

    Lemma fold_left_preserves_length : forall instrs s_init obs_init,
      length (env (fold_left
        (fun '(s_acc, obs_acc) e =>
          let '(s', new_obs) := dual_interp_instr s_acc e in
          (s', obs_acc ++ new_obs))
        instrs (s_init, obs_init)).1) = length (env s_init).
    Proof.
      induction instrs as [| i rest IH]; intros s_init obs_init.
      - simpl. reflexivity.
      - simpl. destruct (dual_interp_instr s_init i) as [s' new_obs] eqn:Hstep.
        rewrite IH. rewrite <- (dual_interp_preserves_length s_init i).
        rewrite Hstep. reflexivity.
    Qed.

    Lemma run_preserves_length : forall (s : state) (prog : list instr) (steps : nat),
      length (env (run s prog steps).1) = length (env s).
    Proof. intros s prog steps. unfold run. apply fold_left_preserves_length. Qed.

    
    
    (* Valid state preservation *)

    Lemma dual_interp_preserves_valid : forall (s : state) (e : instr),
      valid_state (dual_interp_instr s e).1.
    Proof.
      intros s e. unfold dual_interp_instr, valid_state.
      destruct (interp_instr s.(env) e) as [env' obs]. simpl. reflexivity.
    Qed.

    Lemma fold_left_run_valid : forall instrs s_init obs_init,
      valid_state s_init ->
      valid_state (fold_left
        (fun '(s_acc, obs_acc) e =>
          let '(s', new_obs) := dual_interp_instr s_acc e in
          (s', obs_acc ++ new_obs))
        instrs (s_init, obs_init)).1.
    Proof.
      induction instrs as [| e rest IH]; intros s_init obs_init Hvalid.
      - simpl. exact Hvalid.
      - simpl. destruct (dual_interp_instr s_init e) as [s' new_obs] eqn:Hstep.
        apply IH.
        assert (Hv := dual_interp_preserves_valid s_init e).
        rewrite Hstep in Hv. simpl in Hv. exact Hv.
    Qed.

    Lemma run_preserves_valid : forall (s : state) (prog : list instr) (steps : nat),
      valid_state s -> valid_state (run s prog steps).1.
    Proof. intros s prog steps H. unfold run. apply fold_left_run_valid. exact H. Qed.

    

    (* ── HW complement ──────────────────────────────────────────────────────── *)

    Lemma fold_left_plus : forall (rest : list bool) (acc : nat),
      fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) rest acc
      = fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) rest 0 + acc.
    Proof.
      induction rest. simpl. reflexivity.
      simpl. intros. destruct a; auto. rewrite IHrest. rewrite IHrest with (acc := 1). lia.
    Qed.

    Lemma num_true_complement : forall (bools : list bool),
      num_true bools + num_true (map negb bools) = length bools.
    Proof.
      induction bools as [| b rest IH]; simpl.
      - reflexivity.
      - unfold num_true in *. simpl filter.
        destruct b; simpl. rewrite fold_left_plus. lia. rewrite fold_left_plus with (acc := 1). lia.
    Qed.

    (* ── HW complement — the core bit-counting identity ─────────────────── *)

    Create HintDb List.
    Hint Rewrite length_map : List.
    Hint Rewrite @length_bv_to_bits : List.

    Lemma Some_ne_None' : forall A (opt : option A) a,
      opt = Some a -> opt <> None.
    Proof.
      destruct opt; auto.
    Qed.

    (* nth_error and stdpp's !! coincide; idx avoids clash with section variable n *)
    Lemma nth_error_lookup : forall A (xs : list A) (idx : nat) (d : A),
      nth_error xs idx = xs !! idx.
    Proof.
      intros.
      destruct (list_basics.list.nth_lookup_or_length xs idx d).
      { rewrite e.
        apply nth_error_nth'.
        eapply list_basics.list.lookup_lt_Some; eauto. }
      { destruct (nth_error _ _) eqn:?.
        { rewrite <- nth_error_None in l. congruence. }
        { symmetry. rewrite list_basics.list.lookup_ge_None. auto. } }
    Qed.

    Lemma bv_to_bits_not : forall (a : bv n),
      bv_to_bits (bv_not a) = map negb (bv_to_bits a).
    Proof.
      intros.
      apply nth_error_ext.
      intros. repeat rewrite nth_error_lookup by (try exact false).
      setoid_rewrite list_monad.list.list_lookup_fmap.
      destruct (decide (n0 < N.to_nat n)).
      { repeat match goal with
        | |- context[?x !! ?y] => destruct (x !! y) eqn:?
        | H: _ !! _ = None |- _ => rewrite list_basics.list.lookup_ge_None in H
        | |- Some _ = Some _ => f_equal
        | |- _ => autorewrite with List in *; auto; try lia; simpl in *
        end.
        rewrite bv_to_bits_lookup_Some in *.
        destruct_and !. subst.
        rewrite bv_not_unsigned.
        setoid_rewrite <- Z.lnot_spec; [ | lia].
        rewrite bv_wrap_spec_low; auto.
        lia. }
      { repeat rewrite list_basics.list.lookup_ge_None_2
          by (autorewrite with List; lia); done. }
    Qed.

    Lemma hw_complement : forall (a : bv n),
      HW a + HW (bv_not a) = N.to_nat n.
    Proof.
      intro a. unfold HW. rewrite bv_to_bits_not. rewrite num_true_complement.
      apply length_bv_to_bits.
    Qed.

    (* General accumulator lemma for HW sums — same pattern as fold_left_plus.
       NB: parameter named [l] not [env] to avoid the state field projector. *)
    Lemma num_1s_in_list_fold_plus : forall (l : list (bv n)) (k : nat),
      fold_left (fun (acc : nat) (pv : bv n) => acc + HW pv) l k =
      fold_left (fun (acc : nat) (pv : bv n) => acc + HW pv) l 0 + k.
    Proof.
      induction l as [| x rest IH]; simpl; intros k.
      - lia.
      - rewrite IH. rewrite IH with (k := HW x). lia.
    Qed.

    Lemma fold_left_plus_HW : forall (l : list (bv n)) (acc : nat) (a : bv n),
      fold_left (fun (acc : nat) (pv : bv n) => acc + HW pv) l (acc + (HW a))
      = fold_left (fun (acc : nat) (pv : bv n) => acc + HW pv) l (HW a) + acc.
    Proof.
      intros.
      rewrite num_1s_in_list_fold_plus.
      rewrite num_1s_in_list_fold_plus with (k := HW a).
      lia.
    Qed.

    Lemma valid_state_num_1s_induct : forall (env0 : Env) (acc : nat),
      fold_left (λ (acc : nat) (pv : bv n), acc + HW pv) env0 acc +
      fold_left (λ (acc : nat) (pv : bv n), acc + HW pv) (map bv_not env0) acc =
      length env0 * N.to_nat n + 2 * acc.
    Proof.
      (* induction before intros acc so the IH generalises over acc *)
      induction env0 as [| a rest IH].
      - simpl. lia.
      - simpl. intros acc.
        (* shift both accumulators to 0 using the general fold-left lemma *)
        rewrite (num_1s_in_list_fold_plus rest).
        rewrite (num_1s_in_list_fold_plus (map bv_not rest)).
        (* IH at acc=0: fold rest 0 + fold (map bv_not rest) 0 = length rest * n *)
        pose proof (IH 0) as IH0.
        (* hw_complement: HW a + HW (bv_not a) = n *)
        pose proof (hw_complement a) as Hc.
        (* simpl already expanded S (length rest) * n and 2 * acc; lia closes *)
        lia.
    Qed.

    Lemma valid_state_num_1s : forall (s : state),
      valid_state s ->
      num_1s_in_state s = length s.(env) * N.to_nat n.
    Proof.
      intros. unfold valid_state in *. unfold num_1s_in_state, num_1s_in_list. rewrite H.
      destruct s. simpl in *. rewrite valid_state_num_1s_induct. lia.
    Qed.



    (* ── Security theorem: full register set ────────────────────────────── *)

    Lemma all_secure : forall (prog : list instr) (init_s : state),
      valid_state init_s -> secure prog init_s.
    Proof.
      unfold secure. intros prog init_s Hvalid.
      exists (length init_s.(env) * N.to_nat n). intros steps.
      rewrite (valid_state_num_1s _ (run_preserves_valid init_s prog steps Hvalid)).
      rewrite run_preserves_length. reflexivity.
    Qed.

    

    (* ── Security theorem: secret registers only ────────────────────────── *)

    Inductive RegClass := | SecretReg | PublicReg.
    #[global] Instance RegClass_eq_dec : EqDecision RegClass.
    Proof. solve_decision. Defined.

    (* In the ladder X1 and A24 are public inputs, everything else is secret *)
    Definition ladder_classify (r : var) : RegClass :=
      match r with
      | 0 => PublicReg   (* rX1 - base point, known to attacker *)
      | 5 => PublicReg   (* rA24 — curve constant, public *)
      | _ => SecretReg
      end.

    (* sum HW only over a given list of register indices *)
    Definition num_1s_regs (env : Env) (regs : list var) : nat :=
      fold_left (fun acc r => acc + HW (read_register env r)) regs 0.

    (* secret register indices for the ladder program *)
    Definition ladder_secret_regs : list var :=
      [ rX2; rZ2; rX3; rZ3
      ; rU; rV; rW; rT
      ; rU2; rV2; rUT; rVW
      ; rSp; rSm; rX3'; rSm2; rZ3'
      ; rX2'; rD; rAD; rT2; rZ2' ].

    (* total HW of secret registers across both sides of dual circuit *)
    Definition num_1s_secret_state (s : state) (regs : list var) : nat :=
      num_1s_regs s.(env) regs + num_1s_regs s.(denv) regs.

    (* security focused on secret registers only *)
    Definition secure_secret (prog : list instr) (s : state) (regs : list var) :=
      exists c, forall steps,
        num_1s_secret_state (run s prog steps).1 regs = c.

    (* helper: reading from a complemented env gives the complement *)
    Lemma read_register_map_not : forall (env : Env) (r : var),
      r < length env ->
      read_register (map bv_not env) r = bv_not (read_register env r).
    Proof.
      intros env r Hr. unfold read_register.
      unfold default_var. rewrite <- map_nth with (f := bv_not). apply nth_indep. rewrite length_map. auto.
    Qed.

    (* fold_left accumulator lemma for num_1s_regs — same pattern as fold_left_plus.
       NB: parameter named [e] not [env] to avoid shadowing the state field projector. *)
    Lemma num_1s_regs_fold_plus : forall (e : Env) (regs : list var) (acc : nat),
      fold_left (fun (acc : nat) (r : var) => acc + HW (read_register e r)) regs acc =
      fold_left (fun (acc : nat) (r : var) => acc + HW (read_register e r)) regs 0 + acc.
    Proof.
      induction regs as [| r rest IH]; simpl; intros acc.
      - lia.
      - rewrite IH. rewrite IH with (acc := HW (read_register e r)). lia.
    Qed.

    (* peeling the head off num_1s_regs *)
    Lemma num_1s_regs_cons : forall (e : Env) (r : var) (regs : list var),
      num_1s_regs e (r :: regs) = HW (read_register e r) + num_1s_regs e regs.
    Proof.
      intros e r regs. unfold num_1s_regs. simpl.
      rewrite num_1s_regs_fold_plus. lia.
    Qed.

    (* HW of secret registers is constant under valid_state *)
    Lemma valid_state_num_1s_regs : forall (s : state) (regs : list var),
      valid_state s ->
      (forall r, In r regs -> r < length s.(env)) ->
      num_1s_secret_state s regs = length regs * N.to_nat n.
    Proof.
      intros s regs Hvalid.
      (* introduce Hbounds AFTER induction so the IH generalises it for the tail *)
      induction regs as [| r rest IH]; intros Hbounds.
      - (* nil: both sides 0 *)
        unfold num_1s_secret_state, num_1s_regs. simpl. lia.
      - unfold num_1s_secret_state.
        rewrite !num_1s_regs_cons.
        (* head register: HW(env[r]) + HW(denv[r]) = n *)
        assert (Hstep : HW (read_register s.(env) r) + HW (read_register s.(denv) r) = N.to_nat n).
        { rewrite Hvalid.
          rewrite read_register_map_not.
          - apply hw_complement.
          - apply Hbounds. left. reflexivity. }
        (* tail: IH applies with bounds restricted to rest *)
        assert (IHapp : num_1s_secret_state s rest = length rest * N.to_nat n).
        { apply IH. intros r' Hr'. apply Hbounds. right. exact Hr'. }
        unfold num_1s_secret_state in IHapp.
        simpl length. lia.
    Qed.

    (* HW of secret registers is constant throughout execution *)
    Lemma all_secure_secret : forall (prog : list instr) (init_s : state),
      valid_state init_s ->
      (forall r, In r ladder_secret_regs -> r < length init_s.(env)) ->
      secure_secret prog init_s ladder_secret_regs.
    Proof.
      unfold secure_secret. intros prog init_s Hvalid Hbounds.
      exists (length ladder_secret_regs * N.to_nat n).
      intros steps.
      apply valid_state_num_1s_regs.
      - apply run_preserves_valid. exact Hvalid.
      - intros r Hr. rewrite run_preserves_length. apply Hbounds. exact Hr.
    Qed.

    (* ── Compact register allocation (12 registers, same security) ─────── *)

    Notation cX1  := 0  (only parsing).   (* public: base point x-coord     *)
    Notation cX2  := 1  (only parsing).   (* secret                          *)
    Notation cZ2  := 2  (only parsing).   (* secret                          *)
    Notation cX3  := 3  (only parsing).   (* secret                          *)
    Notation cZ3  := 4  (only parsing).   (* secret                          *)
    Notation cA24 := 5  (only parsing).   (* public: curve constant          *)
    Notation cT0  := 6  (only parsing).   (* temp, reused across the step   *)
    Notation cT1  := 7  (only parsing).   (* temp                             *)
    Notation cT2  := 8  (only parsing).   (* temp                            *)
    Notation cT3  := 9  (only parsing).   (* temp                            *)
    Notation cT4  := 10 (only parsing).   (* temp                            *)
    Notation cT5  := 11 (only parsing).   (* temp                            *)

    Definition compact_program : list instr :=
      [ IAdd cT0  cX2  cZ2    (* T0 = X2+Z2        = U                       *)
      ; ISub cT1  cX2  cZ2    (* T1 = X2−Z2        = V                       *)
      ; IAdd cT2  cX3  cZ3    (* T2 = X3+Z3        = W                       *)
      ; ISub cT3  cX3  cZ3    (* T3 = X3−Z3        = T                       *)
      ; IMul cT4  cT0  cT0    (* T4 = U·U          = U²                      *)
      ; IMul cT5  cT1  cT1    (* T5 = V·V          = V²   [peak: 8 live]     *)
      ; IMul cT0  cT0  cT3    (* T0 = U·T          = UT   [T3 dead]          *)
      ; IMul cT3  cT1  cT2    (* T3 = V·W          = VW   [T1,T2 dead]       *)
      ; IAdd cT1  cT0  cT3    (* T1 = UT+VW        = Sp                      *)
      ; ISub cT2  cT0  cT3    (* T2 = UT−VW        = Sm   [T0,T3 dead]       *)
      ; IMul cT1  cT1  cT1    (* T1 = Sp·Sp        = X3'                     *)
      ; IMul cT0  cT2  cT2    (* T0 = Sm·Sm        = Sm²  [T2 dead]          *)
      ; IMul cT2  cT0  cX1    (* T2 = Sm²·X1       = Z3'  [T0,X1 dead]       *)
      ; IMul cT0  cT4  cT5    (* T0 = U²·V²        = X2'                     *)
      ; ISub cT3  cT4  cT5    (* T3 = U²−V²        = D    [T4 dead]          *)
      ; IMul cT4  cA24 cT3    (* T4 = A24·D        = AD   [A24 dead]         *)
      ; IAdd cT5  cT5  cT4    (* T5 = V²+AD        = T2'  [T5,T4 dead]       *)
      ; IMul cT3  cT3  cT5    (* T3 = D·T2'        = Z2'  [T3,T5 dead]       *)
      ].
      (* Final: cT0=X2', cT1=X3', cT2=Z3', cT3=Z2'  (4 output regs)         *)

    (* Generalised public/secret classification
       declare a list of public registers --> derive the classify function from it *)

    Definition classify_by_list (pub : list var) (r : var) : RegClass :=
      if decide (r ∈ pub) then PublicReg else SecretReg.

    (* Retrofit the original program with the general classifier *)
    Definition ladder_public_regs : list var := [rX1; rA24].  (* 0 and 5     *)
    Definition ladder_classify' : var -> RegClass :=
      classify_by_list ladder_public_regs.

    (* Compact program: same two public inputs, same physical register slots  *)
    Definition compact_public_regs : list var := [cX1; cA24].  (* also 0,5   *)
    Definition compact_classify : var -> RegClass :=
      classify_by_list compact_public_regs.

    (* Secret registers for the compact program (everything except public)    *)
    Definition compact_secret_regs : list var :=
      [cX2; cZ2; cX3; cZ3; cT0; cT1; cT2; cT3; cT4; cT5].

    (* HW of secret registers in compact program is constant
       same proof structure as all_secure_secret?  *)
    Lemma compact_all_secure_secret : forall (init_s : state),
      valid_state init_s ->
      (forall r, In r compact_secret_regs -> r < length init_s.(env)) ->
      secure_secret compact_program init_s compact_secret_regs.
    Proof.
      unfold secure_secret. intros init_s Hvalid Hbounds.
      exists (length compact_secret_regs * N.to_nat n).
      intros steps.
      apply valid_state_num_1s_regs.
      - apply run_preserves_valid. exact Hvalid.
      - intros r Hr.
        rewrite run_preserves_length. apply Hbounds. exact Hr.
    Qed.

    (* ── Selective dualization — bridge to processor model ──────────────────
       Full valid_state dualizes every register. The StateMachine only allocates
       dual slots for secret registers, so we need valid_state_partial here as
       the connecting invariant.                                               *)

    (* valid_state_partial: only secret registers have their complement tracked *)
    Definition valid_state_partial (s : state) (classify : var → RegClass) : Prop :=
      forall r,
        classify r = SecretReg →
        r < length s.(env) →
        read_register s.(denv) r = bv_not (read_register s.(env) r).

    (* Observe that valid_state implies valid_state_partial for any classify:
       if every register has its complement, then in particular secret ones do. *)
    Lemma valid_state_implies_partial :
      forall (s : state) (classify : var → RegClass),
        valid_state s →
        (forall r, r < length s.(env)) →
        valid_state_partial s classify.
    Proof.
      intros s classify Hv _Hlen r _Hsec Hr.
      unfold valid_state in Hv.
      rewrite Hv.
      apply read_register_map_not.
      exact Hr.
    Qed.

    (* dual_interp_selective: like dual_interp_instr but only updates denv[rd] when classify says rd is a secret register.
       - Public register writes leave denv unchanged. *)
    Definition dual_interp_selective
        (classify : var → RegClass) (s : state) (e : instr) : state * list Observation :=
      let '(env', obs) := interp_instr s.(env) e in
      let denv' :=
        match e with
        | IAdd rd _ _ | ISub rd _ _ | IMul rd _ _ =>
            if decide (classify rd = SecretReg)
            then write_register s.(denv) rd (bv_not (read_register env' rd))
            else s.(denv)                (* public write: no dual slot to update *)
        | Observe _ => s.(denv)          (* observations never touch denv *)
        end
      in
      ({| env := env'; denv := denv' |}, obs).

    (* Invariant preservation:
        if s satisfies valid_state_partial (classify), and the instruction writes a secret register,
        --> then the updated state still satisfies valid_state_partial.  *)
    Lemma dual_interp_selective_preserves_partial :
      forall (classify : var → RegClass) (s : state) (e : instr),
        valid_state_partial s classify →
        (forall r, r < length s.(env)) →
        length s.(denv) = length s.(env) →
        valid_state_partial (fst (dual_interp_selective classify s e)) classify.
    Proof.
      intros classify s e Hpartial Hlen Hdlen.
      unfold dual_interp_selective, valid_state_partial in *.
      destruct (interp_instr s.(env) e) as [env' obs] eqn:Hinterp.
      simpl fst. intros r Hsec Hr.
      cbn [env denv] in *.
      assert (Hlen_denv : forall x, x < length s.(denv))
        by (intro x; rewrite Hdlen; exact (Hlen x)).
      assert (Hr' : r < length s.(env)).
      { rewrite <- (interp_instr_preserves_length s.(env) e). rewrite Hinterp. exact Hr. }
      (* After destruct + simpl, Hinterp becomes (write_register env rd v, []) = (env', obs).
         injection extracts Henv' : write_register ... = env', which we rewrite backwards
         to convert env' back to env at register r (via read_register_write_diff).        *)
      destruct e as [rd ra rb | rd ra rb | rd ra rb | ro]; simpl in Hinterp;
      injection Hinterp as Henv' _;
      [ | | |
        (* Observe: env' = env s directly *)
        rewrite <- Henv'; exact (Hpartial r Hsec Hr') ];
      (* Arithmetic cases: Henv' : write_register (env s) rd v = env'  *)
      destruct (decide (classify rd = SecretReg)) as [Heq | Hne];
      destruct (decide (r = rd)) as [-> | Hne_r].
      (* Secret write, r = rd: dual slot written with the right value *)
      all: try (rewrite read_register_write_same by exact (Hlen_denv rd); reflexivity).
      (* Public write, r = rd: contradiction — r is secret but rd is public *)
      all: try (exfalso; exact (Hne Hsec)).
      (* r ≠ rd (both secret-write and public-write sub-cases):
         - try: undo the denv write_register at rd (only present in the secret case)
         - rewrite <- Henv': env' → write_register (env s) rd v
         - rewrite write_diff: read_register at r ≠ rd recovers env s value
         - Hpartial closes the goal *)
      all: (
        try (rewrite read_register_write_diff by (intro H; exact (Hne_r (eq_sym H))));
        rewrite <- Henv';
        rewrite read_register_write_diff by (intro H; exact (Hne_r (eq_sym H)));
        exact (Hpartial r Hsec Hr')).
    Qed.

    (* 1. set of public registers --> public are not duplicated *)
        (* ISA contract? write another update function where only have shadow regs for secret *)

    (* run function on env --> list of obs --> functional correctness hold across run on env and on goal circuit *)
      (* definition of functional correctness - how to state *)
    (* observation of circuit & dual same at every  *)

    (* add memory? *)
      (* define machine: consists of registers & a memory --> 1. InstrMem: list of instructions (alt: store as bv --> translate to instr
         2. DataMem: store secret & public data
        --> implement a simple processor: program counter (also public), fetch --> memory respond in 1 cycle with instruction -->
         decode execute in single cycle *)
    (* hardware-software contract? *)
    (* language?  *)
    (* duplicate dynamically? some registers are 0 until you allocate a pair *)
  End DualCircuit.

End HammingWeight.

(* ══════════════════════════════════════════════════════════════════════════════
   Processor model — concrete 3-stage pipeline with selective register dualization
   ══════════════════════════════════════════════════════════════════════════════ *)
Module StateMachine.

  (* Pipeline stages — mutually exclusive, exactly one active per cycle *)
  Inductive PipelineStage :=
    | Fetch
    | Execute
    | WriteBack.

Section StateMachine.
  Variable n : N.

  (* secret_map.(j) names which Regs slot is duplicated into DRegs slot j.
     e.g. secret_map.[0] = Fin 3 means DRegs[0] mirrors Regs[3].          *)
    
  (* conversion from 16 to 32 - doesn't need to be a variable *)

  Variable secret_map : Vector.t (Fin.t 32) 16.

  Record state := mkState {
    pc        : bv n;
    Regs      : Vector.t (bv n) 32;      (* all 32 general-purpose registers   *)
    DRegs     : Vector.t (bv n) 16;      (* dual of the 16 secret registers    *)
    InstrMem  : list (bv n);             (* program stored as encoded bitvectors — public *)
    (* DataMem   : nat -> bv n;             data heap                          *)
    Stage     : PipelineStage;           (* current pipeline stage             *)

    (* instruction memory bus — public: carries opcodes, no duplication needed *)
    toiMem    : bool * bv n;             (* (valid, fetch addr)                *)
    fromiMem  : bool * bv n;             (* (valid, fetched instr)             *)
    bookkeepingState : bool * nat * bv n * bv n             (* use nat for now *)

    (* data memory bus — may carry secret values, so dualized                  *)
    (* todMem    : bool * bv n * bv n;      (* (valid, addr, data)   write bus    *)
    dtodMem   : bool * bv n * bv n;      (* dual write bus                     *)
    fromdMem  : bool * bv n;             (* (valid, loaded data)  read bus     *)
    dfromdMem : bool * bv n;             dual read bus                      *)
  }. 
  Instance eta : Settable state := settable! mkState 
  <pc; Regs; DRegs; InstrMem; Stage; toiMem; fromiMem; bookkeepingState>.

  (* ── Invariant ───────────────────────────────────────────────────────────
     Every dual slot holds the bitwise complement of its secret original.
     DRegs[j] = bv_not (Regs[secret_map[j]])  for all j : Fin.t 16         *)
  Definition valid_state (s : state) : Prop :=
    (* DRegs[j] = bv_not(Regs[secret_map[j]]) for every secret slot *)
    (forall j : Fin.t 16,
      Vector.nth s.(DRegs) j =
      bv_not (Vector.nth s.(Regs) (Vector.nth secret_map j)))
    /\
    (* E2W register: when valid, the dual value is the complement of val *)
    (match s.(bookkeepingState) with
     | (((v, _), val), dval) => v = true -> dval = bv_not val
     end).

  (* ── Combinational units ─────────────────────────────────────────────── *)

  (* Safe register read/write by nat index *)
  Definition read_reg (rs : Vector.t (bv n) 32) (r : var) : bv n :=
    match Fin.of_nat r 32%nat with
    | inleft f  => Vector.nth rs f
    | inright _ => bv_0 n
    end.

  Definition write_reg (rs : Vector.t (bv n) 32) (r : var) (v : bv n) : Vector.t (bv n) 32 :=
    match Fin.of_nat r 32%nat with
    | inleft f  => Vector.replace rs f v
    | inright _ => rs
    end.

  (* ALU: decode + compute. Returns (write_enable, rd, val).
     we=true for arithmetic, false for Observe (no writeback needed). *)
  Definition exec_instr (rs : Vector.t (bv n) 32) (e : instr) : bool * var * bv n :=
    let get r := read_reg rs r in
    match e with
    | IAdd rd rs1 rs2 => (true,  rd, bv_add (get rs1) (get rs2))
    | ISub rd rs1 rs2 => (true,  rd, bv_sub (get rs1) (get rs2))
    | IMul rd rs1 rs2 => (true,  rd, bv_mul (get rs1) (get rs2))
    | Observe _       => (false, 0%nat, bv_0 n)
    end.

  (* DRegs selective update: set DRegs[j] := v for every j where secret_map[j] = rd *)
  Definition update_dregs (dregs : Vector.t (bv n) 16) (rd : var) (v : bv n)
      : Vector.t (bv n) 16 :=
    Vector.map2
      (fun dreg (mapped : Fin.t 32) =>
        if Nat.eqb (proj1_sig (Fin.to_nat mapped)) rd then v else dreg)
      dregs secret_map.

  (* Instruction encoding: bit layout [rs2(5)|rs1(5)|rd(5)|op(2)], requires n ≥ 17.
     op: 0=IAdd 1=ISub 2=IMul 3=Observe *)
  Definition encode_instr (e : instr) : bv n :=
    let pack (op rd rs1 rs2 : nat) :=
      Z_to_bv n (Z.of_nat op
               + Z.of_nat rd  * 4
               + Z.of_nat rs1 * 128
               + Z.of_nat rs2 * 4096) in
    match e with
    | IAdd rd rs1 rs2 => pack 0%nat rd rs1 rs2
    | ISub rd rs1 rs2 => pack 1%nat rd rs1 rs2
    | IMul rd rs1 rs2 => pack 2%nat rd rs1 rs2
    | Observe ro      => pack 3%nat ro 0%nat 0%nat
    end.

  Definition decode_instr (b : bv n) : option instr :=
    let v   := bv_unsigned b in
    let op  := Z.to_nat (v mod 4) in
    let rd  := Z.to_nat (v / 4   mod 32) in
    let rs1 := Z.to_nat (v / 128  mod 32) in
    let rs2 := Z.to_nat (v / 4096 mod 32) in
    match op with
    | 0%nat => Some (IAdd rd rs1 rs2)
    | 1%nat => Some (ISub rd rs1 rs2)
    | 2%nat => Some (IMul rd rs1 rs2)
    | 3%nat => Some (Observe rd)
    | _     => None
    end.

  (* ── Stage handlers ──────────────────────────────────────────────────── *)
  Definition fetch (s : state) : state :=
    s <|toiMem := (true, s.(pc))|>
      <|Stage := Execute|>.

  (* Execute reads from fromiMem (set by tick_iMem the same cycle fetch ran) *)
  Definition execute (s : state) : state :=
    let '(valid, encoded) := s.(fromiMem) in
    if valid then
      match decode_instr encoded with
      | None   => s <|fromiMem := (false, encoded)|> <|Stage := WriteBack|>
      | Some e =>
          let '((we, rd), v) := exec_instr s.(Regs) e in
          s <|bookkeepingState := (((we, rd), v), bv_not v)|>
            <|fromiMem := (false, encoded)|>
            <|pc    := bv_add s.(pc) (Z_to_bv n 1)|>
            <|Stage := WriteBack|>
      end
    else
      s <|Stage := WriteBack|>.

  Definition writeback (s : state) : state :=
    let '(((valid, rd), val), dval) := s.(bookkeepingState) in
    if valid then
      s <|Regs  := write_reg s.(Regs) rd val|>
        <|DRegs := update_dregs s.(DRegs) rd dval|>
        <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n)|>
        <|Stage := Fetch|>
    else
      s <|Stage := Fetch|>.

  (* One clock tick: dispatch on the current pipeline stage *)
  Definition tick (s : state) : state :=
    match s.(Stage) with
    | Fetch     => fetch s
    | Execute   => execute s
    | WriteBack => writeback s
    end.

  (* Memory-side ticks — admitted until bus protocol is defined *)
  Definition tick_dMem : state -> state. Admitted.

  (* Instruction memory responder (doiMem):
     if toiMem carries a valid request, encode InstrMem[addr] onto fromiMem
     and clear the request valid bit. *)
  Definition tick_iMem (s : state) : state :=
    let '(valid, addr) := s.(toiMem) in
    if valid then
      let encoded := match nth_error s.(InstrMem) (Z.to_nat (bv_unsigned addr)) with
                     | Some b => b
                     | None   => bv_0 n
                     end in
      s <|fromiMem := (true,  encoded)|>
        <|toiMem   := (false, addr)  |>
    else s.

  (* ── Security proof helpers ─────────────────────────────────────────── *)

  (* nth of Vector.map2 reduces pointwise — direct from stdlib VectorSpec.nth_map2 *)
  Lemma Vector_nth_map2 : forall (A B C : Type) (m : nat) (f : A -> B -> C)
      (v1 : Vector.t A m) (v2 : Vector.t B m) (j : Fin.t m),
    Vector.nth (Vector.map2 f v1 v2) j = f (Vector.nth v1 j) (Vector.nth v2 j).
  Proof.
    intros A B C m f v1 v2 j.
    exact (nth_map2 f v1 v2 j j j eq_refl eq_refl).
  Qed.

  (* Vector.replace at the same / a different position — from stdlib VectorSpec *)
  Lemma Vector_nth_replace_same : forall (A : Type) (m : nat) (v : Vector.t A m)
      (p : Fin.t m) (a : A),
    Vector.nth (Vector.replace v p a) p = a.
  Proof.
    intros A m v p a.
    exact (nth_replace_eq A m p v a).
  Qed.

  Lemma Vector_nth_replace_diff : forall (A : Type) (m : nat) (v : Vector.t A m)
      (p q : Fin.t m) (a : A),
    p <> q -> Vector.nth (Vector.replace v p a) q = Vector.nth v q.
  Proof.
    intros A m v p q a Hpq.
    (* stdlib: nth_replace_neq n p q (p≠q) v a : nth (replace v q a) p = nth v p
       our goal: nth (replace v p a) q = nth v q  — swap p and q *)
    exact (nth_replace_neq A m q p (fun H => Hpq (eq_sym H)) v a).
  Qed.

  (* update_dregs[j] = v   when secret_map[j] points to rd *)
  Lemma nth_update_dregs_eq (dregs : Vector.t (bv n) 16) (rd : var) (v : bv n) (j : Fin.t 16) :
    proj1_sig (Fin.to_nat (Vector.nth secret_map j)) = rd ->
    Vector.nth (update_dregs dregs rd v) j = v.
  Proof.
    intro Heq. unfold update_dregs.
    rewrite Vector_nth_map2. simpl.
    rewrite <- Heq, Nat.eqb_refl. reflexivity.
  Qed.

  (* update_dregs[j] = dregs[j]   when secret_map[j] does not point to rd *)
  Lemma nth_update_dregs_neq (dregs : Vector.t (bv n) 16) (rd : var) (v : bv n) (j : Fin.t 16) :
    proj1_sig (Fin.to_nat (Vector.nth secret_map j)) <> rd ->
    Vector.nth (update_dregs dregs rd v) j = Vector.nth dregs j.
  Proof.
    intro Hne. unfold update_dregs.
    rewrite Vector_nth_map2. simpl.
    rewrite (proj2 (Nat.eqb_neq _ _) Hne). reflexivity.
  Qed.

  (* Fin.R_sanity with n=1 gives proj1_sig (to_nat (FS f)) = S (proj1_sig (to_nat f)).
     Direct reflexivity fails because proj1_sig doesn't commute through the stuck match
     on abstract to_nat f; R_sanity avoids that by providing a pre-proved equation. *)
  Lemma to_nat_FS_proj1 {m} (f : Fin.t m) :
      proj1_sig (Fin.to_nat (Fin.FS f)) = S (proj1_sig (Fin.to_nat f)).
  Proof. exact (Fin.R_sanity 1 f). Qed.

  (* Helper: when Fin.of_nat rd m = inleft f, the index of f equals rd. *)
  Lemma of_nat_inleft_to_nat (rd : nat) : forall (m : nat) (f : Fin.t m),
      Fin.of_nat rd m = inleft f -> proj1_sig (Fin.to_nat f) = rd.
  Proof.
    induction rd as [| rd' IH]; intros m f Hof.
    - destruct m as [| m']; simpl in Hof.
      + discriminate.
      + injection Hof as <-. reflexivity.
    - destruct m as [| m']; simpl in Hof.
      + discriminate.
      + destruct (Fin.of_nat rd' m') as [f' | arg] eqn:Hof'; simpl in Hof.
        * injection Hof as <-.
          rewrite to_nat_FS_proj1.
          exact (f_equal S (IH m' f' Hof')).
        * discriminate.
  Qed.

  (* write_reg[j] = v / unchanged depending on whether j = rd *)
  Lemma nth_write_reg_same (rs : Vector.t (bv n) 32) (rd : var) (v : bv n) (j : Fin.t 32) :
    proj1_sig (Fin.to_nat j) = rd ->
    Vector.nth (write_reg rs rd v) j = v.
  Proof.
    intro Hrd. unfold write_reg.
    destruct (Fin.of_nat rd 32) as [f | arg] eqn:Hof.
    - assert (Hjf : j = f).
      { apply Fin.to_nat_inj. rewrite Hrd. exact (eq_sym (of_nat_inleft_to_nat rd 32 f Hof)). }
      rewrite Hjf. apply nth_replace_eq.
    - exfalso.
      destruct arg as [m Hm].
      pose proof (proj2_sig (Fin.to_nat j)) as Hlt.
      rewrite Hrd, Hm in Hlt. lia.
  Qed.

  Lemma nth_write_reg_diff (rs : Vector.t (bv n) 32) (rd : var) (v : bv n) (j : Fin.t 32) :
    proj1_sig (Fin.to_nat j) <> rd ->
    Vector.nth (write_reg rs rd v) j = Vector.nth rs j.
  Proof.
    intro Hne. unfold write_reg.
    destruct (Fin.of_nat rd 32) as [f | arg] eqn:Hof.
    - apply nth_replace_neq.
      intro Heq. apply Hne. subst j.
      exact (of_nat_inleft_to_nat rd 32 f Hof).
    - reflexivity.
  Qed.

  (* ── RecordUpdate field-preservation: setting Stage leaves other fields alone ── *)

  Lemma DRegs_set_Stage (s : state) (v : PipelineStage) :
      (s <|Stage := v|>).(DRegs) = s.(DRegs).
  Proof. destruct s; reflexivity. Qed.

  Lemma Regs_set_Stage (s : state) (v : PipelineStage) :
      (s <|Stage := v|>).(Regs) = s.(Regs).
  Proof. destruct s; reflexivity. Qed.

  Lemma bks_set_Stage (s : state) (v : PipelineStage) :
      (s <|Stage := v|>).(bookkeepingState) = s.(bookkeepingState).
  Proof. destruct s; reflexivity. Qed.

  (* WriteBack true: 4-setter chain — each field projects to its new value *)
  Lemma DRegs_writeback_chain (s : state) (rd : var) (val : bv n) :
      (s <|Regs  := write_reg   s.(Regs)  rd val        |>
         <|DRegs := update_dregs s.(DRegs) rd (bv_not val)|>
         <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n)|>
         <|Stage := Fetch|>).(DRegs) = update_dregs s.(DRegs) rd (bv_not val).
  Proof. destruct s; reflexivity. Qed.

  Lemma Regs_writeback_chain (s : state) (rd : var) (val : bv n) :
      (s <|Regs  := write_reg   s.(Regs)  rd val        |>
         <|DRegs := update_dregs s.(DRegs) rd (bv_not val)|>
         <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n)|>
         <|Stage := Fetch|>).(Regs) = write_reg s.(Regs) rd val.
  Proof. destruct s; reflexivity. Qed.

  Lemma bks_writeback_chain (s : state) (rd : var) (val : bv n) :
      (s <|Regs  := write_reg   s.(Regs)  rd val        |>
         <|DRegs := update_dregs s.(DRegs) rd (bv_not val)|>
         <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n)|>
         <|Stage := Fetch|>).(bookkeepingState) = (((false, 0%nat), bv_0 n), bv_0 n).
  Proof. destruct s; reflexivity. Qed.

  (* ── Security theorem ───────────────────────────────────────────────── *)

  (* top-level theorem: assuming all secret reg secret pub regs pub -->  two processors running w/ different secrets 
  --> even then the power (# of 1's) is the same*)

  (* separate secret and public registers *)
  (* Match on [slots] alone, using [in]/[return] to carry the length type.
     [vals] is passed as a continuation argument so Rocq knows its length
     matches [slots] without a simultaneous dependent match. *)
  Fixpoint install_secrets {k : nat}
      (regs  : Vector.t (bv n) 32)
      (slots : Vector.t (Fin.t 32) k)
      (vals  : Vector.t (bv n) k) : Vector.t (bv n) 32 :=
    match slots in Vector.t _ k'
          return Vector.t (bv n) k' -> Vector.t (bv n) 32 with
    | Vector.nil       => fun _     => regs
    | Vector.cons s ss => fun vals' =>
        install_secrets (Vector.replace regs s (Vector.hd vals')) ss (Vector.tl vals')
    end vals.
  
  Definition mk_processor_state
    (imem     : list (bv n))
    (pub_regs : Vector.t (bv n) 32)   (* public info — secret slots here are ignored *)
    (sec_vals : Vector.t (bv n) 16)   (* secret info — written over secret_map slots *)
    : state :=
  let regs := install_secrets pub_regs secret_map sec_vals in
  {| pc               := bv_0 n
   ; Regs             := regs
   ; DRegs            := Vector.map (fun j => bv_not (Vector.nth regs j)) secret_map
   ; InstrMem         := imem
   ; Stage            := Fetch
   ; toiMem          := (false, bv_0 n)
   ; fromiMem        := (false, bv_0 n)
   ; bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n) |}.
  (* assign values to registers / initialize  *)

  (* make two processors *)
  (* pass two different secret info and same public info *)
  (* equivalence *)



  Lemma tick_preserves_valid : forall (s : state),
    valid_state s -> valid_state (tick s).
  Proof.
    intros s [Hdregs Hbks].
    unfold tick.
    destruct s.(Stage).

    - (* Fetch: only toiMem and Stage updated; Regs/DRegs/bks unchanged *)
      unfold fetch, valid_state. simpl.
      split; [intro j; exact (Hdregs j) | exact Hbks].

    - (* Execute: only bks/fromiMem/pc/Stage updated; Regs/DRegs unchanged *)
      unfold execute, valid_state.
      destruct s.(fromiMem) as [valid encoded]. simpl.
      destruct valid.
      + destruct (decode_instr encoded) as [e |].
        * destruct (exec_instr s.(Regs) e) as [[we rd] v]. simpl.
          split; [intro j; exact (Hdregs j) | intro; reflexivity].
        * simpl. split; [intro j; exact (Hdregs j) | exact Hbks].
      + simpl. split; [intro j; exact (Hdregs j) | exact Hbks].

    - (* WriteBack: Regs/DRegs updated (valid=true) or Stage-only (valid=false) *)
      unfold writeback, valid_state.
      (* eqn: keeps the LHS as s.(bookkeepingState) so we can rewrite with it later *)
      destruct s.(bookkeepingState) as [[[valid rd] val] dval] eqn:Hbks_eq.
      destruct valid.
      + (* valid=true: dval = bv_not val by the bks invariant *)
        assert (Hdval : dval = bv_not val) by (apply Hbks; reflexivity).
        subst dval.
        split.
        * intro j.
          rewrite DRegs_writeback_chain, Regs_writeback_chain.
          destruct (Nat.eq_dec (proj1_sig (Fin.to_nat (Vector.nth secret_map j))) rd)
            as [Heq | Hne].
          { rewrite nth_update_dregs_eq by exact Heq.
            rewrite nth_write_reg_same by exact Heq.
            reflexivity. }
          { rewrite nth_update_dregs_neq by exact Hne.
            rewrite nth_write_reg_diff by exact Hne.
            exact (Hdregs j). }
        * rewrite bks_writeback_chain. intro H. discriminate H.
      + (* valid=false: only Stage updated; DRegs/Regs/bks project back to s *)
        rewrite DRegs_set_Stage, Regs_set_Stage.
        split; [intro j; exact (Hdregs j)|].
        rewrite bks_set_Stage, Hbks_eq.
        exact Hbks.
  Qed.

  (* TODO: extend valid_state to cover bookkeepingState (E2W register carries secrets) *)
  (* TODO: tick_dMem + DataMem field — data memory bus, dualized like DRegs             *)
  (* TODO: HW constant per cycle — processor-level analogue of all_secure_secret        *)

  (* Montgomery LadderStep on the processor — concrete instantiation
     Load the 18-instruction program into InstrMem, fix the secret register
     map, build an initial valid_state, and run for 54 ticks (18 instrs × 3
     pipeline stages). *)

  (* Safe Fin.t 32 from a nat index; defaults to F1 for any out-of-range value. *)
  Definition mk_reg (k : nat) : Fin.t 32 :=
    match Fin.of_nat k 32 with
    | inleft f  => f
    | inright _ => Fin.F1
    end.

  (* Secret registers: the 16 working registers of one LadderStep iteration.
     Public: rX1(0) - base-point x-coord; rA24(5) - curve constant (A+2)/4.
     Secret: projective coordinates X2(1),Z2(2),X3(3),Z3(4) and 12 intermediates
             U(6)..Sm(15), plus the output X2'(19).  The four outputs
             X3'(16), Z3'(18), Z2'(23) are left outside this map for clarity. *)
  (* list_to_fin32_vec: convert nat indices to a Fin.t 32 vector.
     Both Vector.nil and Vector.cons take A as their first explicit argument. *)
  Fixpoint list_to_fin32_vec (ks : list nat)
      : Vector.t (Fin.t 32%nat) (List.length ks) :=
    match ks return Vector.t (Fin.t 32%nat) (List.length ks) with
    | []       => @Vector.nil (Fin.t 32%nat)
    | k :: ks' => @Vector.cons (Fin.t 32%nat) (mk_reg k) _ (list_to_fin32_vec ks')
    end.

  Definition ladder_secret_map : Vector.t (Fin.t 32%nat) 16 :=
    list_to_fin32_vec
      [1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 19]%nat.

  (* Encode the LadderStep program as a flat list of instruction words. *)
  Definition ladder_instr_mem : list (bv n) := map encode_instr program.

  (* Build the initial 32-register file from the six input values.
     Register assignment: 0=X1(public), 1=X2, 2=Z2, 3=X3, 4=Z3, 5=A24(public). *)
  Definition ladder_regs (x2 z2 x3 z3 x1 a24 : bv n) : Vector.t (bv n) 32 :=
    let z := Vector.const (bv_0 n) 32 in
    write_reg (write_reg (write_reg (write_reg (write_reg (write_reg
      z 0%nat x1) 1%nat x2) 2%nat z2) 3%nat x3) 4%nat z3) 5%nat a24.

  (* Initial processor state.  DRegs are set to the bitwise complement of
     secret_map's projection of Regs, so valid_state holds by construction. *)
  Definition ladder_init (x2 z2 x3 z3 x1 a24 : bv n) : state :=
    let regs := ladder_regs x2 z2 x3 z3 x1 a24 in
    {| pc        := bv_0 n
     ; Regs      := regs
     ; DRegs     := Vector.map (fun f => bv_not (Vector.nth regs f)) secret_map
     ; InstrMem  := ladder_instr_mem
     ; Stage     := Fetch
     ; toiMem   := (false, bv_0 n)
     ; fromiMem := (false, bv_0 n)
     ; bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n) |}.

  Lemma ladder_init_valid (x2 z2 x3 z3 x1 a24 : bv n) :
      valid_state (ladder_init x2 z2 x3 z3 x1 a24).
  Proof.
    unfold valid_state, ladder_init. simpl. split.
    - intro j. rewrite (@Vector.nth_map _ _ _ _ _ j j eq_refl). reflexivity.
    - intro H. discriminate.
  Qed.

  (* One full clock cycle: processor stage transition + instruction memory response. *)
  Definition full_tick (s : state) : state := tick_iMem (tick s).

  (* Iterate full_tick for a given number of cycles. *)
  Fixpoint run_ticks (s : state) (fuel : nat) : state :=
    match fuel with
    | O       => s
    | S fuel' => run_ticks (full_tick s) fuel'
    end.

  (* Run one complete LadderStep: 18 instructions × 3 pipeline stages = 54 ticks. *)
  Definition ladder_result (x2 z2 x3 z3 x1 a24 : bv n) : state :=
    run_ticks (ladder_init x2 z2 x3 z3 x1 a24) 54.

  (* Security corollary: valid_state is preserved for all 54 ticks. *)
  Lemma ladder_result_valid (x2 z2 x3 z3 x1 a24 : bv n) :
      valid_state (ladder_result x2 z2 x3 z3 x1 a24).
  Proof.
    unfold ladder_result.
    (* run_ticks composes 54 applications of full_tick; each preserves valid_state
       by tick_preserves_valid + tick_iMem (admitted until tick_iMem is proved). *)
  Admitted.

  (* ── Top-level security theorem ─────────────────────────────────────────── *)

  Lemma mk_processor_state_valid
      (imem : list (bv n)) (pub_regs : Vector.t (bv n) 32) (sec_vals : Vector.t (bv n) 16) :
      valid_state (mk_processor_state imem pub_regs sec_vals).
  Proof.
    unfold valid_state, mk_processor_state. simpl. split.
    - intro j. rewrite (@Vector.nth_map _ _ _ _ _ j j eq_refl). reflexivity.
    - intro H. discriminate.
  Qed.

  (* ── HW observable ───────────────────────────────────────────────────────── *)

  (* Hamming weight of one n-bit bitvector: count the 1-bits. *)
  Definition HW_bv (v : bv n) : nat :=
    fold_left (fun (acc : nat) (b : bool) => if b then (acc + 1)%nat else acc)
              (bv_to_bits v) 0%nat.

  (* Hamming weight of the full processor state: sum HW_bv over every bitvector
     field.  This models the instantaneous power draw at one clock edge —
     every wire that holds a 1 contributes one unit.                          *)
  Definition state_HW (s : state) : nat :=
    let hw_regs  := Vector.fold_left (fun acc v => (acc + HW_bv v)%nat) 0%nat s.(Regs)  in
    let hw_dregs := Vector.fold_left (fun acc v => (acc + HW_bv v)%nat) 0%nat s.(DRegs) in
    let hw_imem  := fold_left (fun acc v => (acc + HW_bv v)%nat) s.(InstrMem) 0%nat     in
    let '(((_, _), val), dval) := s.(bookkeepingState) in
    ( HW_bv s.(pc)          (* program counter                               *)
    + hw_regs               (* 32 general-purpose registers                  *)
    + hw_dregs              (* 16 dual registers (secret complements)         *)
    + hw_imem               (* instruction memory words                      *)
    + HW_bv (snd s.(toiMem))    (* fetch address bus                         *)
    + HW_bv (snd s.(fromiMem))  (* fetch data bus                            *)
    + HW_bv val             (* E2W result value                              *)
    + HW_bv dval)%nat.      (* E2W dual value                                *)

  (* The total observable power is state_HW. *)
  Definition total_HW_observable (s : state) : nat := state_HW s.

  (* ── Power-independence theorem ──────────────────────────────────────────── *)
  (* Two processors with the same public registers and instruction memory but
     different secrets produce identical observable Hamming weight.              *)
  Theorem power_independence
      (imem     : list (bv n))
      (pub_regs : Vector.t (bv n) 32)
      (sec1 sec2 : Vector.t (bv n) 16) :
      total_HW_observable (mk_processor_state imem pub_regs sec1) =
      total_HW_observable (mk_processor_state imem pub_regs sec2).
  Proof.
    (* Both sides reduce to 16 * N.to_nat n via valid_state + hw_complement. *)
  Admitted.

End StateMachine.
End StateMachine.

(* ══════════════════════════════════════════════════════════════════════════════
   Probabilistic Two-Register Model
   - masking a secret register with a fresh uniform random value leaks no information through Hamming-weight side channels.

   Machine: two n-bit registers — r0 (secret, unknown to attacker), r1 (random).
   Ensemble semantics: GenRV forks the current state into 2^n copies, one per possible value of the target register, modelling uniform sampling. 
    The key property is that bv_add secret is a permutation on bv n, so after
      GenRV r1 ; Add r1 r0 r1
   the multiset of r1 values across the ensemble is {0,..,2^n-1} regardless of
   the secret in r0 — the total Hamming weight is therefore constant.
   ══════════════════════════════════════════════════════════════════════════════ *)
Section TwoRegProb.
  Variable n : N.

  (* State - two registers *)
  Record two_state := mk_two_state { r0 : bv n; r1 : bv n }.

  (* Instruction set *)
  (* Register index: false = r0 (secret),  true = r1 (random) *)
  Inductive two_instr :=
    | T_Add   (rd rs1 rs2 : bool)  (* rd ← rs1 + rs2                          *)
    | T_GenRV (rd : bool).         (* rd := uniform random (forks the ensemble) *)

  (* Ensemble: list of equally-probable states *)
  Definition Ensemble := list two_state.

  Definition read_r (s : two_state) (r : bool) : bv n :=
    if r then s.(r1) else s.(r0).

  Definition write_r (s : two_state) (r : bool) (v : bv n) : two_state :=
    if r then mk_two_state s.(r0) v
    else      mk_two_state v      s.(r1).

  (* Every n-bit bitvector in order — the range GenRV samples uniformly. *)
  Definition all_bv : list (bv n) :=
    map (fun k => Z_to_bv n (Z.of_nat k)) (seq 0 (Z.to_nat (2 ^ Z.of_N n))).

  
  (* Small-step semantics *)

  (* One instruction on one state produces a list of successor states.
     T_Add is deterministic (singleton list); T_GenRV forks into |all_bv| = 2^n copies *)
  Definition interp_two (s : two_state) (e : two_instr) : list two_state :=
    match e with
    | T_Add rd rs1 rs2 =>
        [write_r s rd (bv_add (read_r s rs1) (read_r s rs2))]
    | T_GenRV rd =>
        map (fun v => write_r s rd v) all_bv
    end.

  (* Lift one step over the full ensemble *)
  Definition step_two (ens : Ensemble) (e : two_instr) : Ensemble :=
    flat_map (fun s => interp_two s e) ens.

  (* Run a program to completion *)
  Fixpoint run_two (ens : Ensemble) (prog : list two_instr) : Ensemble :=
    match prog with
    | []        => ens
    | e :: rest => run_two (step_two ens e) rest
    end.


  (* Security metric *)

  (* Hamming weight of a single bitvector. *)
  Definition HW2 (a : bv n) : nat :=
    fold_left (fun (acc : nat) (b : bool) => if b then (acc + 1)%nat else acc) (bv_to_bits a) 0%nat.

  (* todo: instead of summing over ensemble, state equivalence between distribution of copies. *)
  Definition total_HW_r1 (ens : Ensemble) : nat :=
    fold_left (fun (acc : nat) (s : two_state) => (acc + HW2 s.(r1))%nat) ens 0%nat.

  (* Masking program *)

  (* Step 1: GenRV r1 — fork into 2^n copies, each with a distinct r1 value.
     Step 2: Add r1 r0 r1 — mask r1 with the secret in r0. *)
  Definition mask_prog : list two_instr :=
    [ T_GenRV true               (* r1 := uniform random                       *)
    ; T_Add   true false true ]. (* r1 ← r0 + r1  (mask secret with random)    *)

  (* Key security lemma *)
  (* After mask_prog, total_HW_r1 is the same for any two secrets.
     Proof outline:
       • After T_GenRV: r1 ∈ {0,..,2^n-1} → total_HW = ∑_v HW(v) = n·2^(n-1).
       • T_Add maps r1 ↦ secret + r1; since bv_add secret is a permutation,
         {secret+v | v ∈ all_bv} = all_bv as multisets.
       • Hence total_HW_r1 is unchanged ⟹ independent of secret.            *)
  Lemma mask_security (s1 s2 : bv n) :
    total_HW_r1 (run_two [mk_two_state s1 (bv_0 n)] mask_prog) =
    total_HW_r1 (run_two [mk_two_state s2 (bv_0 n)] mask_prog).
  Proof.
    (* Needs: bv_add is a permutation (bv arithmetic) + sum HW over all_bv is constant. *)
  Admitted.

  (* InfoTheo library *)
End TwoRegProb.

(* dual circuit / each module doesn't have full info *)

