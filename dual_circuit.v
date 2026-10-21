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

Section HammingWeight.
  Variable n : N. (* width of bv *)
  Variable p : bv n.

  (* Reduce modulo p before encoding: bitvector arithmetic would wrap modulo 2^n first. *)
  Definition fadd_bv (a b : bv n) : bv n :=
    Z_to_bv n ((bv_unsigned a + bv_unsigned b) mod bv_unsigned p).
  Definition fsub_bv (a b : bv n) : bv n :=
    Z_to_bv n ((bv_unsigned a - bv_unsigned b) mod bv_unsigned p).
  Definition fmul_bv (a b : bv n) : bv n :=
    Z_to_bv n ((bv_unsigned a * bv_unsigned b) mod bv_unsigned p).
  Definition fsq_bv  (a : bv n)   : bv n :=
    fmul_bv a a.

  Local Lemma mod_to_bv_unsigned (z : Z) : 0 < bv_unsigned p -> bv_unsigned (Z_to_bv n (z mod bv_unsigned p)) = z mod bv_unsigned p.
  Proof.
    intros Hp. apply Z_to_bv_small.
    pose proof (Z.mod_pos_bound z (bv_unsigned p) Hp).
    pose proof (bv_unsigned_in_range n p). lia.
  Qed.

  Lemma fadd_bv_correct (a b : bv n) : 0 < bv_unsigned p -> bv_unsigned (fadd_bv a b) = (bv_unsigned a + bv_unsigned b) mod bv_unsigned p.
  Proof. intros Hp. unfold fadd_bv. apply mod_to_bv_unsigned. exact Hp. Qed.

  Lemma fsub_bv_correct (a b : bv n) : 0 < bv_unsigned p -> bv_unsigned (fsub_bv a b) = (bv_unsigned a - bv_unsigned b) mod bv_unsigned p.
  Proof. intros Hp. unfold fsub_bv. apply mod_to_bv_unsigned. exact Hp. Qed.

  Lemma fmul_bv_correct (a b : bv n) : 0 < bv_unsigned p -> bv_unsigned (fmul_bv a b) = (bv_unsigned a * bv_unsigned b) mod bv_unsigned p.
  Proof. intros Hp. unfold fmul_bv. apply mod_to_bv_unsigned. exact Hp. Qed.

  (* Probability-label sketch, without distribution semantics or a soundness proof.
     Labels alone do not track dependence or guarantee uniformity. *)
  Inductive ProbType :=
    | Prob_concrete
    | Prob_random
    | Prob_unknown.

  Record ProbVar :=
  { Value : bv n;
    Ptype : ProbType
  }.

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

  Definition fadd_probvar (a b : ProbVar) : ProbVar :=
    {|
    Value := fadd_bv a.(Value) b.(Value);
    Ptype := faddsub_prob a.(Ptype) b.(Ptype)
  |}.

  Definition fsub_probvar (a b : ProbVar) : ProbVar :=
    {|
    Value := fsub_bv a.(Value) b.(Value);
    Ptype := faddsub_prob a.(Ptype) b.(Ptype)
  |}.

  Definition fmul_probvar (a b : ProbVar) : ProbVar :=
    {|
    Value := fmul_bv a.(Value) b.(Value);
    Ptype := fmul_prob a.(Ptype) b.(Ptype)
  |}.

  Inductive ProbHW :=
    | ProbHW_concrete (n : N)
    | ProbHW_random
    | ProbHW_unknown.

  (* Register-machine instructions. *)
  Definition var := nat.

  Inductive instr : Type :=
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

  Definition ProbEnv :=
    list ProbVar.

  Definition prob_default_var : ProbVar :=
    {|
    Value := bv_0 n;
    Ptype := Prob_unknown
  |}.

  Definition prob_read_register (env : ProbEnv) (i : var) : ProbVar :=
    nth i env prob_default_var.
  Definition prob_write_register (env : ProbEnv) (i : var) (data : ProbVar) : ProbEnv :=
    list_insert i data env.

  Definition num_true (bools : list bool) : nat :=
    fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) bools 0.

  Definition HW (a : bv n) : nat :=
    num_true (bv_to_bits a).

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
    | IAdd rd a b    => (prob_write_register env rd (fadd_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | ISub rd a b    => (prob_write_register env rd (fsub_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | IMul rd a b    => (prob_write_register env rd (fmul_probvar (prob_read_register env a) (prob_read_register env b)), [])
    | Observe rd     => (env, [RegObservation rd (prob_read_register env rd).(Value)])
    end.

  (* Complementary-register model. *)
  Section DualCircuit.

    (* Execution. *)

    Definition Env :=
      list (bv n).
    Record state := { env : Env; denv : Env }.

    Definition default_var : bv n :=
      bv_0 n.
    Definition read_register  (env : Env) (i : var) : bv n      :=
      nth i env default_var.
    Definition write_register (env : Env) (i : var) (data : bv n) : Env :=
      list_insert i data env.

    Definition interp_instr (env : Env) (e : instr) : Env * list Observation :=
      match e with
      | IAdd rd a b => (write_register env rd (fadd_bv (read_register env a) (read_register env b)), [])
      | ISub rd a b => (write_register env rd (fsub_bv (read_register env a) (read_register env b)), [])
      | IMul rd a b => (write_register env rd (fmul_bv (read_register env a) (read_register env b)), [])
      | Observe rd  => (env, [RegObservation rd (read_register env rd)])
      end.

    (* Update the main and complement banks atomically. *)
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

    Definition valid_state (s : state) : Prop :=
      s.(denv) = map bv_not s.(env).

    (* Unbounded reads include the default value beyond the end of the list. *)
    Definition is_complement (e1 e2 : Env) : Prop :=
      forall i, read_register e2 i = bv_not (read_register e1 i).

    Definition num_1s_in_state (s : state) : nat :=
      num_1s_in_list s.(env) + num_1s_in_list s.(denv).

    (* Constant aggregate register HW after every instruction prefix. *)
    Definition secure (prog : list instr) (s : state) :=
      exists c, forall steps, num_1s_in_state (run s prog steps).1 = c.

    (* Register access and preservation. *)

    Lemma write_register_length : forall (e : Env) (i : var) (v : bv n), length (write_register e i v) = length e.
    Proof. intros e i v. unfold write_register. apply length_insert. Qed.

    Lemma read_register_write_same : forall (e : Env) (i : var) (v : bv n),
      i < length e ->
      read_register (write_register e i v) i = v.
    Proof.
      intros e. induction e as [| x xs IH]; intros i v Hi.
      - simpl in Hi. lia.
      - destruct i; simpl; [reflexivity | apply IH; simpl in Hi; lia].
    Qed.

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

    Lemma interp_instr_preserves_length : forall (e : Env) (i : instr), length (interp_instr e i).1 = length e.
    Proof.
      intros e i. destruct i; simpl; rewrite ?write_register_length; reflexivity.
    Qed.

    Lemma interp_instr_read_other : forall (env0 : Env) (e : instr) (r : var),
      (match e with
       | IAdd rd _ _ | ISub rd _ _ | IMul rd _ _ => r <> rd
       | Observe _                                => True
       end) -> read_register (interp_instr env0 e).1 r = read_register env0 r.
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
        instrs (s_init, obs_init)).1)
      = length (env s_init).
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

    (* Complement preservation. *)

    Lemma dual_interp_preserves_valid : forall (s : state) (e : instr), valid_state (dual_interp_instr s e).1.
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

    (* Complement bit counts. *)

    Lemma fold_left_plus : forall (rest : list bool) (acc : nat),
      fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) rest acc
      = fold_left (fun (acc : nat) (b : bool) => if b then acc + 1 else acc) rest 0 + acc.
    Proof.
      induction rest. simpl. reflexivity.
      simpl. intros. destruct a; auto. rewrite IHrest. rewrite IHrest with (acc := 1). lia.
    Qed.

    Lemma num_true_complement : forall (bools : list bool), num_true bools + num_true (map negb bools) = length bools.
    Proof.
      induction bools as [| b rest IH]; simpl.
      - reflexivity.
      - unfold num_true in *. simpl filter.
        destruct b; simpl. rewrite fold_left_plus. lia. rewrite fold_left_plus with (acc := 1). lia.
    Qed.

    Create HintDb List.
    Hint Rewrite length_map : List.
    Hint Rewrite @length_bv_to_bits : List.

    Lemma Some_ne_None' : forall A (opt : option A) a, opt = Some a -> opt <> None.
    Proof.
      destruct opt; auto.
    Qed.

    Lemma nth_error_lookup : forall A (xs : list A) (idx : nat) (d : A), nth_error xs idx = xs !! idx.
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

    Lemma bv_to_bits_not : forall (a : bv n), bv_to_bits (bv_not a) = map negb (bv_to_bits a).
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
      { repeat rewrite list_basics.list.lookup_ge_None_2 by (autorewrite with List; lia); done. }
    Qed.

    Lemma hw_complement : forall (a : bv n), HW a + HW (bv_not a) = N.to_nat n.
    Proof.
      intro a. unfold HW. rewrite bv_to_bits_not. rewrite num_true_complement.
      apply length_bv_to_bits.
    Qed.

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
      fold_left (λ (acc : nat) (pv : bv n), acc + HW pv) env0 acc
      + fold_left (λ (acc : nat) (pv : bv n), acc + HW pv) (map bv_not env0) acc
      = length env0 * N.to_nat n + 2 * acc.
    Proof.
      induction env0 as [| a rest IH].
      - simpl. lia.
      - simpl. intros acc.
        rewrite (num_1s_in_list_fold_plus rest).
        rewrite (num_1s_in_list_fold_plus (map bv_not rest)).
        pose proof (IH 0) as IH0.
        pose proof (hw_complement a) as Hc.
        lia.
    Qed.

    Lemma valid_state_num_1s : forall (s : state), valid_state s -> num_1s_in_state s = length s.(env) * N.to_nat n.
    Proof.
      intros. unfold valid_state in *. unfold num_1s_in_state, num_1s_in_list. rewrite H.
      destruct s. simpl in *. rewrite valid_state_num_1s_induct. lia.
    Qed.

    (* Full-register HW security. *)

    Lemma all_secure : forall (prog : list instr) (init_s : state), valid_state init_s -> secure prog init_s.
    Proof.
      unfold secure. intros prog init_s Hvalid.
      exists (length init_s.(env) * N.to_nat n). intros steps.
      rewrite (valid_state_num_1s _ (run_preserves_valid init_s prog steps Hvalid)).
      rewrite run_preserves_length. reflexivity.
    Qed.

    (* HW security for selected registers. *)

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
      [rX2; rZ2; rX3; rZ3; rU; rV; rW; rT; rU2; rV2; rUT; rVW; rSp; rSm; rX3'; rSm2; rZ3'; rX2'; rD; rAD; rT2; rZ2'].

    (* total HW of secret registers across both sides of dual circuit *)
    Definition num_1s_secret_state (s : state) (regs : list var) : nat :=
      num_1s_regs s.(env) regs + num_1s_regs s.(denv) regs.

    (* security focused on secret registers only *)
    Definition secure_secret (prog : list instr) (s : state) (regs : list var) :=
      exists c, forall steps, num_1s_secret_state (run s prog steps).1 regs = c.

    Lemma read_register_map_not : forall (env : Env) (r : var),
      r < length env ->
      read_register (map bv_not env) r = bv_not (read_register env r).
    Proof.
      intros env r Hr. unfold read_register.
      unfold default_var. rewrite <- map_nth with (f := bv_not). apply nth_indep. rewrite length_map. auto.
    Qed.

    Lemma num_1s_regs_fold_plus : forall (e : Env) (regs : list var) (acc : nat),
      fold_left (fun (acc : nat) (r : var) => acc + HW (read_register e r)) regs acc =
      fold_left (fun (acc : nat) (r : var) => acc + HW (read_register e r)) regs 0 + acc.
    Proof.
      induction regs as [| r rest IH]; simpl; intros acc.
      - lia.
      - rewrite IH. rewrite IH with (acc := HW (read_register e r)). lia.
    Qed.

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
      induction regs as [| r rest IH]; intros Hbounds.
      -
        unfold num_1s_secret_state, num_1s_regs. simpl. lia.
      - unfold num_1s_secret_state.
        rewrite !num_1s_regs_cons.
        assert (Hstep : HW (read_register s.(env) r) + HW (read_register s.(denv) r) = N.to_nat n).
        { rewrite Hvalid.
          rewrite read_register_map_not.
          - apply hw_complement.
          - apply Hbounds. left. reflexivity. }
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

    (* 12-register allocation: HW security only; functional correctness is not proved here. *)

    Notation cX1  := 0  (only parsing).
    Notation cX2  := 1  (only parsing).
    Notation cZ2  := 2  (only parsing).
    Notation cX3  := 3  (only parsing).
    Notation cZ3  := 4  (only parsing).
    Notation cA24 := 5  (only parsing).
    Notation cT0  := 6  (only parsing).
    Notation cT1  := 7  (only parsing).
    Notation cT2  := 8  (only parsing).
    Notation cT3  := 9  (only parsing).
    Notation cT4  := 10 (only parsing).
    Notation cT5  := 11 (only parsing).

    Definition compact_program : list instr :=
      [ IAdd cT0  cX2  cZ2    (* U *)
      ; ISub cT1  cX2  cZ2    (* V *)
      ; IAdd cT2  cX3  cZ3    (* W *)
      ; ISub cT3  cX3  cZ3    (* T *)
      ; IMul cT4  cT0  cT0    (* U^2 *)
      ; IMul cT5  cT1  cT1    (* V^2 *)
      ; IMul cT0  cT0  cT3    (* UT *)
      ; IMul cT3  cT1  cT2    (* VW *)
      ; IAdd cT1  cT0  cT3    (* Sp = UT+VW *)
      ; ISub cT2  cT0  cT3    (* Sm = UT-VW *)
      ; IMul cT1  cT1  cT1    (* X3' *)
      ; IMul cT0  cT2  cT2    (* Sm^2 *)
      ; IMul cT2  cT0  cX1    (* Z3' *)
      ; IMul cT0  cT4  cT5    (* X2' *)
      ; ISub cT3  cT4  cT5    (* D = U^2-V^2 *)
      ; IMul cT4  cA24 cT3    (* A24*D *)
      ; IAdd cT5  cT5  cT4    (* V^2+A24*D *)
      ; IMul cT3  cT3  cT5    (* Z2' *)
      ].
    (* Outputs: cT0=X2', cT1=X3', cT2=Z3', cT3=Z2'. *)

    (* Registers not listed as public are classified as secret. *)

    Definition classify_by_list (pub : list var) (r : var) : RegClass :=
      if decide (r ∈ pub) then PublicReg else SecretReg.

    Definition ladder_public_regs : list var :=
      [rX1; rA24].  (* 0 and 5     *)
    Definition ladder_classify' : var -> RegClass :=
      classify_by_list ladder_public_regs.

    Definition compact_public_regs : list var :=
      [cX1; cA24].  (* also 0,5   *)
    Definition compact_classify : var -> RegClass :=
      classify_by_list compact_public_regs.

    Definition compact_secret_regs : list var :=
      [cX2; cZ2; cX3; cZ3; cT0; cT1; cT2; cT3; cT4; cT5].

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

    (* Selective pairing experiment; StateMachine pairs all 32 registers. *)
    Definition valid_state_partial (s : state) (classify : var → RegClass) : Prop :=
      forall r,
        classify r = SecretReg →
        r < length s.(env) →
        read_register s.(denv) r = bv_not (read_register s.(env) r).

    Lemma valid_state_implies_partial :
      forall (s : state) (classify : var → RegClass),
        valid_state s →
        valid_state_partial s classify.
    Proof.
      intros s classify Hv r _Hsec Hr.
      unfold valid_state in Hv.
      rewrite Hv.
      apply read_register_map_not.
      exact Hr.
    Qed.

    (* Public writes leave the complement bank unchanged. *)
    Definition dual_interp_selective (classify : var → RegClass) (s : state) (e : instr) : state * list Observation :=
      let '(env', obs) := interp_instr s.(env) e in
      let denv' :=
        match e with
        | IAdd rd _ _ | ISub rd _ _ | IMul rd _ _ =>
            if decide (classify rd = SecretReg)
            then write_register s.(denv) rd (bv_not (read_register env' rd))
            else s.(denv)
        | Observe _ => s.(denv)
        end in
      ({| env := env'; denv := denv' |}, obs).

    Lemma dual_interp_selective_preserves_partial :
      forall (classify : var → RegClass) (s : state) (e : instr),
        valid_state_partial s classify →
        length s.(denv) = length s.(env) →
        valid_state_partial (fst (dual_interp_selective classify s e)) classify.
    Proof.
      intros classify s e Hpartial Hdlen.
      unfold dual_interp_selective, valid_state_partial in *.
      destruct (interp_instr s.(env) e) as [env' obs] eqn:Hinterp.
      simpl fst. intros r Hsec Hr.
      cbn [env denv] in *.
      assert (Hr' : r < length s.(env)).
      { rewrite <- (interp_instr_preserves_length s.(env) e). rewrite Hinterp. exact Hr. }
      destruct e as [rd ra rb | rd ra rb | rd ra rb | ro]; simpl in Hinterp;
      injection Hinterp as Henv' _;
      [ | | |
        rewrite <- Henv'; exact (Hpartial r Hsec Hr') ];
      destruct (decide (classify rd = SecretReg)) as [Heq | Hne];
      destruct (decide (r = rd)) as [-> | Hne_r].
      all: try (rewrite read_register_write_same by (rewrite Hdlen; exact Hr'); reflexivity).
      all: try (exfalso; exact (Hne Hsec)).
      all: (
        try (rewrite read_register_write_diff by (intro H; exact (Hne_r (eq_sym H))));
        rewrite <- Henv';
        rewrite read_register_write_diff by (intro H; exact (Hne_r (eq_sym H)));
        exact (Hpartial r Hsec Hr')).
    Qed.

  End DualCircuit.

End HammingWeight.
