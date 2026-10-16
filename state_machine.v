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

Require Import dual_circuit.

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
  Instance eta : Settable state := settable! mkState <pc; Regs; DRegs; InstrMem; Stage; toiMem; fromiMem; bookkeepingState>.

  (* ── Invariant ───────────────────────────────────────────────────────────
     Every dual slot holds the bitwise complement of its secret original.
     DRegs[j] = bv_not (Regs[secret_map[j]])  for all j : Fin.t 16         *)
  Definition valid_state (s : state) : Prop :=
    (* DRegs[j] = bv_not(Regs[secret_map[j]]) for every secret slot *)
    (forall j : Fin.t 16, Vector.nth s.(DRegs) j = bv_not (Vector.nth s.(Regs) (Vector.nth secret_map j))) /\
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
  Definition update_dregs (dregs : Vector.t (bv n) 16) (rd : var) (v : bv n) : Vector.t (bv n) 16 := Vector.map2 (fun dreg (mapped : Fin.t 32) => if Nat.eqb (proj1_sig (Fin.to_nat mapped)) rd then v else dreg) dregs secret_map.

  (* Instruction encoding: bit layout [rs2(5)|rs1(5)|rd(5)|op(2)], requires n ≥ 17.
     op: 0=IAdd 1=ISub 2=IMul 3=Observe *)
  Definition encode_instr (e : instr) : bv n :=
    let pack (op rd rs1 rs2 : nat) := Z_to_bv n (Z.of_nat op + Z.of_nat rd * 4 + Z.of_nat rs1 * 128 + Z.of_nat rs2 * 4096) in
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
  Definition fetch (s : state) : state := s <|toiMem := (true, s.(pc))|> <|Stage := Execute|>.

  (* Execute reads from fromiMem (set by tick_iMem the same cycle fetch ran) *)
  Definition execute (s : state) : state :=
    let '(valid, encoded) := s.(fromiMem) in
    if valid then
      match decode_instr encoded with
      | None   => s <|fromiMem := (false, encoded)|> <|Stage := WriteBack|>
      | Some e =>
          let '((we, rd), v) := exec_instr s.(Regs) e in
          s <|bookkeepingState := (((we, rd), v), bv_not v)|> <|fromiMem := (false, encoded)|> <|pc    := bv_add s.(pc) (Z_to_bv n 1)|> <|Stage := WriteBack|>
      end
    else
      s <|Stage := WriteBack|>.

  Definition writeback (s : state) : state :=
    let '(((valid, rd), val), dval) := s.(bookkeepingState) in
    if valid then
      s <|Regs  := write_reg s.(Regs) rd val|> <|DRegs := update_dregs s.(DRegs) rd dval|> <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n)|> <|Stage := Fetch|>
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
      s <|fromiMem := (true,  encoded)|> <|toiMem   := (false, addr)  |>
    else s.

  (* ── Security proof helpers ─────────────────────────────────────────── *)

  (* nth of Vector.map2 reduces pointwise — direct from stdlib VectorSpec.nth_map2 *)
  Lemma Vector_nth_map2 : forall (A B C : Type) (m : nat) (f : A -> B -> C) (v1 : Vector.t A m) (v2 : Vector.t B m) (j : Fin.t m), Vector.nth (Vector.map2 f v1 v2) j = f (Vector.nth v1 j) (Vector.nth v2 j).
  Proof.
    intros A B C m f v1 v2 j.
    exact (nth_map2 f v1 v2 j j j eq_refl eq_refl).
  Qed.

  (* Vector.replace at the same / a different position — from stdlib VectorSpec *)
  Lemma Vector_nth_replace_same : forall (A : Type) (m : nat) (v : Vector.t A m) (p : Fin.t m) (a : A), Vector.nth (Vector.replace v p a) p = a.
  Proof.
    intros A m v p a.
    exact (nth_replace_eq A m p v a).
  Qed.

  Lemma Vector_nth_replace_diff : forall (A : Type) (m : nat) (v : Vector.t A m) (p q : Fin.t m) (a : A), p <> q -> Vector.nth (Vector.replace v p a) q = Vector.nth v q.
  Proof.
    intros A m v p q a Hpq.
    (* stdlib: nth_replace_neq n p q (p≠q) v a : nth (replace v q a) p = nth v p
       our goal: nth (replace v p a) q = nth v q  — swap p and q *)
    exact (nth_replace_neq A m q p (fun H => Hpq (eq_sym H)) v a).
  Qed.

  (* update_dregs[j] = v   when secret_map[j] points to rd *)
  Lemma nth_update_dregs_eq (dregs : Vector.t (bv n) 16) (rd : var) (v : bv n) (j : Fin.t 16) : proj1_sig (Fin.to_nat (Vector.nth secret_map j)) = rd -> Vector.nth (update_dregs dregs rd v) j = v.
  Proof.
    intro Heq. unfold update_dregs.
    rewrite Vector_nth_map2. simpl.
    rewrite <- Heq, Nat.eqb_refl. reflexivity.
  Qed.

  (* update_dregs[j] = dregs[j]   when secret_map[j] does not point to rd *)
  Lemma nth_update_dregs_neq (dregs : Vector.t (bv n) 16) (rd : var) (v : bv n) (j : Fin.t 16) : proj1_sig (Fin.to_nat (Vector.nth secret_map j)) <> rd -> Vector.nth (update_dregs dregs rd v) j = Vector.nth dregs j.
  Proof.
    intro Hne. unfold update_dregs.
    rewrite Vector_nth_map2. simpl.
    rewrite (proj2 (Nat.eqb_neq _ _) Hne). reflexivity.
  Qed.

  (* Fin.R_sanity with n=1 gives proj1_sig (to_nat (FS f)) = S (proj1_sig (to_nat f)).
     Direct reflexivity fails because proj1_sig doesn't commute through the stuck match
     on abstract to_nat f; R_sanity avoids that by providing a pre-proved equation. *)
  Lemma to_nat_FS_proj1 {m} (f : Fin.t m) : proj1_sig (Fin.to_nat (Fin.FS f)) = S (proj1_sig (Fin.to_nat f)).
  Proof. exact (Fin.R_sanity 1 f). Qed.

  (* Helper: when Fin.of_nat rd m = inleft f, the index of f equals rd. *)
  Lemma of_nat_inleft_to_nat (rd : nat) : forall (m : nat) (f : Fin.t m), Fin.of_nat rd m = inleft f -> proj1_sig (Fin.to_nat f) = rd.
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
  Lemma nth_write_reg_same (rs : Vector.t (bv n) 32) (rd : var) (v : bv n) (j : Fin.t 32) : proj1_sig (Fin.to_nat j) = rd -> Vector.nth (write_reg rs rd v) j = v.
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

  Lemma nth_write_reg_diff (rs : Vector.t (bv n) 32) (rd : var) (v : bv n) (j : Fin.t 32) : proj1_sig (Fin.to_nat j) <> rd -> Vector.nth (write_reg rs rd v) j = Vector.nth rs j.
  Proof.
    intro Hne. unfold write_reg.
    destruct (Fin.of_nat rd 32) as [f | arg] eqn:Hof.
    - apply nth_replace_neq.
      intro Heq. apply Hne. subst j.
      exact (of_nat_inleft_to_nat rd 32 f Hof).
    - reflexivity.
  Qed.

  (* ── RecordUpdate field-preservation: setting Stage leaves other fields alone ── *)

  Lemma DRegs_set_Stage (s : state) (v : PipelineStage) : (s <|Stage := v|>).(DRegs) = s.(DRegs).
  Proof. destruct s; reflexivity. Qed.

  Lemma Regs_set_Stage (s : state) (v : PipelineStage) : (s <|Stage := v|>).(Regs) = s.(Regs).
  Proof. destruct s; reflexivity. Qed.

  Lemma bks_set_Stage (s : state) (v : PipelineStage) : (s <|Stage := v|>).(bookkeepingState) = s.(bookkeepingState).
  Proof. destruct s; reflexivity. Qed.

  (* WriteBack true: 4-setter chain — each field projects to its new value *)
  Lemma DRegs_writeback_chain (s : state) (rd : var) (val : bv n) : (s <|Regs  := write_reg   s.(Regs)  rd val        |> <|DRegs := update_dregs s.(DRegs) rd (bv_not val)|> <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n)|> <|Stage := Fetch|>).(DRegs) = update_dregs s.(DRegs) rd (bv_not val).
  Proof. destruct s; reflexivity. Qed.

  Lemma Regs_writeback_chain (s : state) (rd : var) (val : bv n) : (s <|Regs  := write_reg   s.(Regs)  rd val        |> <|DRegs := update_dregs s.(DRegs) rd (bv_not val)|> <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n)|> <|Stage := Fetch|>).(Regs) = write_reg s.(Regs) rd val.
  Proof. destruct s; reflexivity. Qed.

  Lemma bks_writeback_chain (s : state) (rd : var) (val : bv n) : (s <|Regs  := write_reg   s.(Regs)  rd val        |> <|DRegs := update_dregs s.(DRegs) rd (bv_not val)|> <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_0 n)|> <|Stage := Fetch|>).(bookkeepingState) = (((false, 0%nat), bv_0 n), bv_0 n).
  Proof. destruct s; reflexivity. Qed.

  (* ── Security theorem ───────────────────────────────────────────────── *)

  (* top-level theorem: assuming all secret reg secret pub regs pub -->  two processors running w/ different secrets 
  --> even then the power (# of 1's) is the same*)

  (* separate secret and public registers *)
  (* Match on [slots] alone, using [in]/[return] to carry the length type.
     [vals] is passed as a continuation argument so Rocq knows its length
     matches [slots] without a simultaneous dependent match. *)
  Fixpoint install_secrets {k : nat} (regs : Vector.t (bv n) 32) (slots : Vector.t (Fin.t 32) k) (vals : Vector.t (bv n) k) : Vector.t (bv n) 32 :=
    match slots in Vector.t _ k' return Vector.t (bv n) k' -> Vector.t (bv n) 32 with
    | Vector.nil       => fun _     => regs
    | Vector.cons s ss => fun vals' => install_secrets (Vector.replace regs s (Vector.hd vals')) ss (Vector.tl vals')
    end vals.
  
  Definition mk_processor_state (imem : list (bv n)) (pub_regs : Vector.t (bv n) 32) (* public info — secret slots here are ignored *) (sec_vals : Vector.t (bv n) 16) (* secret info — written over secret_map slots *) : state :=
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



  Lemma tick_preserves_valid : forall (s : state), valid_state s -> valid_state (tick s).
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
          destruct (Nat.eq_dec (proj1_sig (Fin.to_nat (Vector.nth secret_map j))) rd) as [Heq | Hne].
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
  Fixpoint list_to_fin32_vec (ks : list nat) : Vector.t (Fin.t 32%nat) (List.length ks) :=
    match ks return Vector.t (Fin.t 32%nat) (List.length ks) with
    | []       => @Vector.nil (Fin.t 32%nat)
    | k :: ks' => @Vector.cons (Fin.t 32%nat) (mk_reg k) _ (list_to_fin32_vec ks')
    end.

  Definition ladder_secret_map : Vector.t (Fin.t 32%nat) 16 := list_to_fin32_vec [1; 2; 3; 4; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 19]%nat.

  (* Encode the LadderStep program as a flat list of instruction words. *)
  Definition ladder_instr_mem : list (bv n) := map encode_instr program.

  (* Build the initial 32-register file from the six input values.
     Register assignment: 0=X1(public), 1=X2, 2=Z2, 3=X3, 4=Z3, 5=A24(public). *)
  Definition ladder_regs (x2 z2 x3 z3 x1 a24 : bv n) : Vector.t (bv n) 32 :=
    let z := Vector.const (bv_0 n) 32 in
    write_reg (write_reg (write_reg (write_reg (write_reg (write_reg z 0%nat x1) 1%nat x2) 2%nat z2) 3%nat x3) 4%nat z3) 5%nat a24.

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

  Lemma ladder_init_valid (x2 z2 x3 z3 x1 a24 : bv n) : valid_state (ladder_init x2 z2 x3 z3 x1 a24).
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
  Definition ladder_result (x2 z2 x3 z3 x1 a24 : bv n) : state := run_ticks (ladder_init x2 z2 x3 z3 x1 a24) 54.

  (* Security corollary: valid_state is preserved for all 54 ticks. *)
  Lemma ladder_result_valid (x2 z2 x3 z3 x1 a24 : bv n) : valid_state (ladder_result x2 z2 x3 z3 x1 a24).
  Proof.
    unfold ladder_result.
    (* run_ticks composes 54 applications of full_tick; each preserves valid_state
       by tick_preserves_valid + tick_iMem (admitted until tick_iMem is proved). *)
  Admitted.

  (* ── Top-level security theorem ─────────────────────────────────────────── *)

  Lemma mk_processor_state_valid (imem : list (bv n)) (pub_regs : Vector.t (bv n) 32) (sec_vals : Vector.t (bv n) 16) : valid_state (mk_processor_state imem pub_regs sec_vals).
  Proof.
    unfold valid_state, mk_processor_state. simpl. split.
    - intro j. rewrite (@Vector.nth_map _ _ _ _ _ j j eq_refl). reflexivity.
    - intro H. discriminate.
  Qed.

  (* ── HW observable ───────────────────────────────────────────────────────── *)

  (* Hamming weight of one n-bit bitvector: count the 1-bits. *)
  Definition HW_bv (v : bv n) : nat := fold_left (fun (acc : nat) (b : bool) => if b then (acc + 1)%nat else acc) (bv_to_bits v) 0%nat.

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
  Theorem power_independence (imem     : list (bv n)) (pub_regs : Vector.t (bv n) 32) (sec1 sec2 : Vector.t (bv n) 16) : total_HW_observable (mk_processor_state imem pub_regs sec1) = total_HW_observable (mk_processor_state imem pub_regs sec2).
  Proof.
    (* Both sides reduce to 16 * N.to_nat n via valid_state + hw_complement. *)
  Admitted.

End StateMachine.
End StateMachine.

