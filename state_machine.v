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

(* Cycle-level processor with complementary registers and a paired result latch. *)
Module StateMachine.

  (* One stage runs per cycle; instructions do not overlap. *)
  Inductive PipelineStage :=
    | Fetch
    | Execute
    | WriteBack.

Section StateMachine.
  Variable n : N.
  Variable modulus : bv n.

  Record state := mkState {
    pc        : bv n;
    Regs      : Vector.t (bv n) 32;
    DRegs     : Vector.t (bv n) 32;      (* complements at matching indices *)
    InstrMem  : list (bv n);            (* encoded instructions *)
    Stage     : PipelineStage;
    toiMem    : bool * bv n;            (* request valid, fetch address *)
    fromiMem  : bool * bv n;            (* response valid, instruction *)
    bookkeepingState : bool * nat * bv n * bv n (* write enable, destination, value, complement *)
  }.
  Instance eta : Settable state :=
    settable! mkState <pc; Regs; DRegs; InstrMem; Stage; toiMem; fromiMem; bookkeepingState>.

  (* All register and execution-latch values stay paired, even when inactive. *)
  Definition valid_state (s : state) : Prop :=
    (forall j : Fin.t 32, Vector.nth s.(DRegs) j = bv_not (Vector.nth s.(Regs) j)) /\
    (let '(((_, _), val), dval) := s.(bookkeepingState) in dval = bv_not val).

  (* Out-of-range reads return zero; out-of-range writes leave registers unchanged. *)
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

  (* Field arithmetic reduces modulo p before encoding; wrapping first would lose carries. *)
  (* Returns write enable, destination, and value. Observe is a no-op in this processor. *)
  Definition exec_instr (rs : Vector.t (bv n) 32) (e : instr) : bool * var * bv n :=
    let get r := read_reg rs r in
    match e with
    | IAdd rd rs1 rs2 => (true,  rd, fadd_bv n modulus (get rs1) (get rs2))
    | ISub rd rs1 rs2 => (true,  rd, fsub_bv n modulus (get rs1) (get rs2))
    | IMul rd rs1 rs2 => (true,  rd, fmul_bv n modulus (get rs1) (get rs2))
    | Observe _       => (false, 0%nat, bv_0 n)
    end.

  (* Layout: [rs2(5)|rs1(5)|rd(5)|op(2)], requiring n >= 17 and indices < 32.
     Opcodes: 0=IAdd, 1=ISub, 2=IMul, 3=Observe. *)
  Definition encode_instr (e : instr) : bv n :=
    let pack (op rd rs1 rs2 : nat) :=
      Z_to_bv n (Z.of_nat op
               + Z.of_nat rd * 4
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

  Definition instr_in_bounds (e : instr) : Prop :=
    match e with
    | IAdd rd ra rb | ISub rd ra rb | IMul rd ra rb => (rd < 32 /\ ra < 32 /\ rb < 32)%nat
    | Observe r => (r < 32)%nat
    end.

  Local Lemma packed_fields op rd ra rb :
    0 <= op < 4 -> 0 <= rd < 32 -> 0 <= ra < 32 -> 0 <= rb < 32 ->
    let word := op + rd * 4 + ra * 128 + rb * 4096 in
    word mod 4 = op /\ (word / 4) mod 32 = rd /\
    (word / 128) mod 32 = ra /\ (word / 4096) mod 32 = rb.
  Proof.
    intros Hop Hrd Hra Hrb. cbv zeta. repeat split.
    - replace (op + rd * 4 + ra * 128 + rb * 4096) with (op + (rd + ra * 32 + rb * 1024) * 4) by ring.
      rewrite Z.mod_add by lia. apply Z.mod_small. exact Hop.
    - replace (op + rd * 4 + ra * 128 + rb * 4096) with (op + (rd + ra * 32 + rb * 1024) * 4) by ring.
      rewrite Z.div_add, Z.div_small by lia. rewrite Z.add_0_l.
      replace (rd + ra * 32 + rb * 1024) with (rd + (ra + rb * 32) * 32) by ring.
      rewrite Z.mod_add by lia. apply Z.mod_small. exact Hrd.
    - replace (op + rd * 4 + ra * 128 + rb * 4096) with ((op + rd * 4) + (ra + rb * 32) * 128) by ring.
      rewrite Z.div_add, Z.div_small by lia. rewrite Z.add_0_l.
      rewrite Z.mod_add by lia. apply Z.mod_small. exact Hra.
    - rewrite Z.div_add, Z.div_small by lia. rewrite Z.add_0_l.
      apply Z.mod_small. exact Hrb.
  Qed.

  Lemma decode_encode_instr e :
    (17 <= n)%N -> instr_in_bounds e -> decode_instr (encode_instr e) = Some e.
  Proof.
    intros Hwidth Hbounds.
    assert (Hcapacity : 131072 <= 2 ^ Z.of_N n).
    { change (2 ^ 17 <= 2 ^ Z.of_N n). apply Z.pow_le_mono_r; lia. }
    destruct e as [rd ra rb | rd ra rb | rd ra rb | rd]; cbn [instr_in_bounds] in Hbounds.
    all: unfold decode_instr, encode_instr; cbv beta zeta.
    all: rewrite Z_to_bv_small by (unfold bv_modulus; lia).
    all: match goal with
      | |- context [Z.to_nat ((?op + Z.of_nat ?rd * 4 + Z.of_nat ?ra * 128 + Z.of_nat ?rb * 4096) mod 4)] =>
          destruct (packed_fields op (Z.of_nat rd) (Z.of_nat ra) (Z.of_nat rb) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hop [Hrd [Hra Hrb]]];
          rewrite Hop, Hrd, Hra, Hrb, !Nat2Z.id; reflexivity
      end.
  Qed.

  (* Stage transitions. *)
  Definition fetch (s : state) : state :=
    s <|toiMem := (true, s.(pc))|> <|Stage := Execute|>.

  (* Fetch receives its memory response before the next Execute cycle. *)
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
        <|DRegs := write_reg s.(DRegs) rd dval|>
        <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_not (bv_0 n))|>
        <|Stage := Fetch|>
    else
      s <|Stage := Fetch|>.

  Definition tick (s : state) : state :=
    match s.(Stage) with
    | Fetch     => fetch s
    | Execute   => execute s
    | WriteBack => writeback s
    end.

  (* Respond to a fetch request. Missing addresses return the zero instruction, not a halt. *)
  Definition tick_iMem (s : state) : state :=
    let '(valid, addr) := s.(toiMem) in
    if valid then
      let encoded := match nth_error s.(InstrMem) (Z.to_nat (bv_unsigned addr)) with
                     | Some b => b
                     | None   => bv_0 n
                     end in
      s <|fromiMem := (true,  encoded)|> <|toiMem   := (false, addr)  |>
    else s.

  (* Register-index and record-update lemmas. *)

  Lemma to_nat_FS_proj1 {m} (f : Fin.t m) : proj1_sig (Fin.to_nat (Fin.FS f)) = S (proj1_sig (Fin.to_nat f)).
  Proof. exact (Fin.R_sanity 1 f). Qed.

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

  Lemma DRegs_set_Stage (s : state) (v : PipelineStage) : (s <|Stage := v|>).(DRegs) = s.(DRegs).
  Proof. destruct s; reflexivity. Qed.

  Lemma Regs_set_Stage (s : state) (v : PipelineStage) : (s <|Stage := v|>).(Regs) = s.(Regs).
  Proof. destruct s; reflexivity. Qed.

  Lemma bks_set_Stage (s : state) (v : PipelineStage) : (s <|Stage := v|>).(bookkeepingState) = s.(bookkeepingState).
  Proof. destruct s; reflexivity. Qed.

  Lemma DRegs_writeback_chain (s : state) (rd : var) (val : bv n) :
      (s <|Regs  := write_reg   s.(Regs)  rd val        |>
         <|DRegs := write_reg s.(DRegs) rd (bv_not val)|>
         <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_not (bv_0 n))|>
         <|Stage := Fetch|>).(DRegs) = write_reg s.(DRegs) rd (bv_not val).
  Proof. destruct s; reflexivity. Qed.

  Lemma Regs_writeback_chain (s : state) (rd : var) (val : bv n) :
      (s <|Regs  := write_reg   s.(Regs)  rd val        |>
         <|DRegs := write_reg s.(DRegs) rd (bv_not val)|>
         <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_not (bv_0 n))|>
         <|Stage := Fetch|>).(Regs) = write_reg s.(Regs) rd val.
  Proof. destruct s; reflexivity. Qed.

  Lemma bks_writeback_chain (s : state) (rd : var) (val : bv n) :
      (s <|Regs  := write_reg   s.(Regs)  rd val        |>
         <|DRegs := write_reg s.(DRegs) rd (bv_not val)|>
         <|bookkeepingState := (((false, 0%nat), bv_0 n), bv_not (bv_0 n))|>
         <|Stage := Fetch|>).(bookkeepingState) = (((false, 0%nat), bv_0 n), bv_not (bv_0 n)).
  Proof. destruct s; reflexivity. Qed.

  Definition mk_processor_state (imem : list (bv n)) (regs : Vector.t (bv n) 32) : state :=
    {| pc := bv_0 n
     ; Regs := regs
     ; DRegs := Vector.map bv_not regs
     ; InstrMem := imem
     ; Stage := Fetch
     ; toiMem := (false, bv_0 n)
     ; fromiMem := (false, bv_0 n)
     ; bookkeepingState := (((false, 0%nat), bv_0 n), bv_not (bv_0 n)) |}.

  Lemma mk_processor_state_valid imem regs : valid_state (mk_processor_state imem regs).
  Proof.
    unfold valid_state, mk_processor_state. cbn [Regs DRegs bookkeepingState]. split.
    - intro j. rewrite (@Vector.nth_map _ _ _ _ _ j j eq_refl). reflexivity.
    - reflexivity.
  Qed.

  Lemma tick_preserves_valid : forall (s : state), valid_state s -> valid_state (tick s).
  Proof.
    intros s [Hdregs Hbks].
    unfold tick.
    destruct s.(Stage).

    -
      unfold fetch, valid_state. simpl.
      split; [intro j; exact (Hdregs j) | exact Hbks].

    -
      unfold execute, valid_state.
      destruct s.(fromiMem) as [valid encoded]. simpl.
      destruct valid.
      + destruct (decode_instr encoded) as [e |].
        * destruct (exec_instr s.(Regs) e) as [[we rd] v]. simpl.
          split; [intro j; exact (Hdregs j) | reflexivity].
        * simpl. split; [intro j; exact (Hdregs j) | exact Hbks].
      + simpl. split; [intro j; exact (Hdregs j) | exact Hbks].

    -
      unfold writeback, valid_state.
      destruct s.(bookkeepingState) as [[[valid rd] val] dval] eqn:Hbks_eq.
      destruct valid.
      +
        subst dval.
        split.
        * intro j.
          rewrite DRegs_writeback_chain, Regs_writeback_chain.
          destruct (Nat.eq_dec (proj1_sig (Fin.to_nat j)) rd) as [Heq | Hne].
          { rewrite !nth_write_reg_same by exact Heq.
            reflexivity. }
          { rewrite !nth_write_reg_diff by exact Hne.
            exact (Hdregs j). }
        * rewrite bks_writeback_chain. reflexivity.
      +
        rewrite DRegs_set_Stage, Regs_set_Stage.
        split; [intro j; exact (Hdregs j)|].
        rewrite bks_set_Stage, Hbks_eq.
        exact Hbks.
  Qed.

  Definition ladder_instr_mem : list (bv n) :=
    map encode_instr program.

  (* Inputs: 0=X1, 1=X2, 2=Z2, 3=X3, 4=Z3, 5=A24; scratch registers start at zero. *)
  Definition ladder_regs (x2 z2 x3 z3 x1 a24 : bv n) : Vector.t (bv n) 32 :=
    let z := Vector.const (bv_0 n) 32 in
    write_reg
      (write_reg
        (write_reg
          (write_reg
            (write_reg (write_reg z 0%nat x1) 1%nat x2)
            2%nat z2)
          3%nat x3)
        4%nat z3)
      5%nat a24.

  Definition ladder_init (x2 z2 x3 z3 x1 a24 : bv n) : state :=
    mk_processor_state ladder_instr_mem (ladder_regs x2 z2 x3 z3 x1 a24).

  Lemma ladder_init_valid (x2 z2 x3 z3 x1 a24 : bv n) : valid_state (ladder_init x2 z2 x3 z3 x1 a24).
  Proof. apply mk_processor_state_valid. Qed.

  (* One full clock cycle: processor stage transition + instruction memory response. *)
  Definition full_tick (s : state) : state :=
    tick_iMem (tick s).

  Fixpoint run_ticks (s : state) (fuel : nat) : state :=
    match fuel with
    | O       => s
    | S fuel' => run_ticks (full_tick s) fuel'
    end.

  Lemma tick_iMem_preserves_valid s : valid_state s -> valid_state (tick_iMem s).
  Proof.
    intro Hvalid. unfold tick_iMem. destruct (toiMem s) as [request addr].
    destruct request; exact Hvalid.
  Qed.

  Lemma full_tick_preserves_valid s : valid_state s -> valid_state (full_tick s).
  Proof. intro Hvalid. apply tick_iMem_preserves_valid, tick_preserves_valid, Hvalid. Qed.

  Lemma run_ticks_preserves_valid s cycles : valid_state s -> valid_state (run_ticks s cycles).
  Proof.
    revert s. induction cycles; intros s Hvalid; cbn [run_ticks].
    - exact Hvalid.
    - apply IHcycles, full_tick_preserves_valid, Hvalid.
  Qed.

  Local Lemma fetch_cycle counter regs duals imem request response pending encoded :
    nth_error imem (Z.to_nat (bv_unsigned counter)) = Some encoded ->
    full_tick (mkState counter regs duals imem Fetch request response pending) =
    mkState counter regs duals imem Execute (false, counter) (true, encoded) pending.
  Proof.
    intro Hfetch. unfold full_tick, tick, fetch, tick_iMem. cbn.
    rewrite Hfetch. reflexivity.
  Qed.

  Local Lemma execute_cycle counter regs duals imem addr encoded pending e we rd value :
    decode_instr encoded = Some e -> exec_instr regs e = (we, rd, value) ->
    full_tick (mkState counter regs duals imem Execute (false, addr) (true, encoded) pending) =
    mkState (bv_add counter (Z_to_bv n 1)) regs duals imem WriteBack (false, addr) (false, encoded) (((we, rd), value), bv_not value).
  Proof.
    intros Hdecode Hexec. unfold full_tick, tick. cbn [Stage]. unfold execute. cbn [fromiMem Regs].
    rewrite Hdecode, Hexec. reflexivity.
  Qed.

  Local Lemma writeback_cycle counter regs duals imem addr response we rd value :
    full_tick (mkState counter regs duals imem WriteBack (false, addr) response (((we, rd), value), bv_not value)) =
    mkState counter (if we then write_reg regs rd value else regs)
      (if we then write_reg duals rd (bv_not value) else duals) imem Fetch (false, addr) response
      (if we then (((false, 0%nat), bv_0 n), bv_not (bv_0 n)) else (((false, rd), value), bv_not value)).
  Proof. destruct we; reflexivity. Qed.

  Theorem instruction_cycle_correct s encoded e we rd value :
    Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some encoded ->
    decode_instr encoded = Some e ->
    exec_instr (Regs s) e = (we, rd, value) ->
    let final := run_ticks s 3 in
    Regs final = (if we then write_reg (Regs s) rd value else Regs s) /\
    DRegs final = (if we then write_reg (DRegs s) rd (bv_not value) else DRegs s) /\
    pc final = bv_add (pc s) (Z_to_bv n 1) /\
    Stage final = Fetch /\ InstrMem final = InstrMem s.
  Proof.
    destruct s as [counter regs duals imem stage request response pending].
    cbn. intros Hstage Hfetch Hdecode Hexec. subst stage.
    rewrite fetch_cycle with (encoded := encoded) by exact Hfetch.
    rewrite execute_cycle with (e := e) (we := we) (rd := rd) (value := value) by assumption.
    rewrite writeback_cycle.
    destruct we; repeat split; reflexivity.
  Qed.

  Lemma read_write_reg_same rs rd value :
    (rd < 32)%nat -> read_reg (write_reg rs rd value) rd = value.
  Proof.
    intro Hrd. unfold read_reg. destruct (Fin.of_nat rd 32) as [j | [extra Hextra]] eqn:Hindex.
    - apply nth_write_reg_same. exact (of_nat_inleft_to_nat rd 32 j Hindex).
    - lia.
  Qed.

  Lemma instruction_cycle_write s e rd value :
    (17 <= n)%N -> instr_in_bounds e -> (rd < 32)%nat -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr e) ->
    exec_instr (Regs s) e = (true, rd, value) ->
    read_reg (Regs (run_ticks s 3)) rd = value.
  Proof.
    intros Hwidth Hbounds Hrd Hstage Hfetch Hexec.
    pose proof (instruction_cycle_correct s (encode_instr e) e true rd value Hstage Hfetch
      (decode_encode_instr e Hwidth Hbounds) Hexec) as Hcycle.
    destruct Hcycle as [Hregs _]. rewrite Hregs. apply read_write_reg_same. exact Hrd.
  Qed.

  Corollary add_cycle_correct s rd ra rb :
    (17 <= n)%N -> 0 < bv_unsigned modulus ->
    instr_in_bounds (IAdd rd ra rb) -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr (IAdd rd ra rb)) ->
    bv_unsigned (read_reg (Regs (run_ticks s 3)) rd) =
    (bv_unsigned (read_reg (Regs s) ra) + bv_unsigned (read_reg (Regs s) rb)) mod bv_unsigned modulus.
  Proof.
    intros Hwidth Hp Hbounds Hstage Hfetch.
    rewrite (instruction_cycle_write s (IAdd rd ra rb) rd (fadd_bv n modulus (read_reg (Regs s) ra) (read_reg (Regs s) rb)))
      by (try assumption; try reflexivity; exact (proj1 Hbounds)).
    apply fadd_bv_correct. exact Hp.
  Qed.

  Corollary sub_cycle_correct s rd ra rb :
    (17 <= n)%N -> 0 < bv_unsigned modulus ->
    instr_in_bounds (ISub rd ra rb) -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr (ISub rd ra rb)) ->
    bv_unsigned (read_reg (Regs (run_ticks s 3)) rd) =
    (bv_unsigned (read_reg (Regs s) ra) - bv_unsigned (read_reg (Regs s) rb)) mod bv_unsigned modulus.
  Proof.
    intros Hwidth Hp Hbounds Hstage Hfetch.
    rewrite (instruction_cycle_write s (ISub rd ra rb) rd (fsub_bv n modulus (read_reg (Regs s) ra) (read_reg (Regs s) rb)))
      by (try assumption; try reflexivity; exact (proj1 Hbounds)).
    apply fsub_bv_correct. exact Hp.
  Qed.

  Corollary mul_cycle_correct s rd ra rb :
    (17 <= n)%N -> 0 < bv_unsigned modulus ->
    instr_in_bounds (IMul rd ra rb) -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr (IMul rd ra rb)) ->
    bv_unsigned (read_reg (Regs (run_ticks s 3)) rd) =
    (bv_unsigned (read_reg (Regs s) ra) * bv_unsigned (read_reg (Regs s) rb)) mod bv_unsigned modulus.
  Proof.
    intros Hwidth Hp Hbounds Hstage Hfetch.
    rewrite (instruction_cycle_write s (IMul rd ra rb) rd (fmul_bv n modulus (read_reg (Regs s) ra) (read_reg (Regs s) rb)))
      by (try assumption; try reflexivity; exact (proj1 Hbounds)).
    apply fmul_bv_correct. exact Hp.
  Qed.

  (* 54 cycles for the 18-instruction program; functional correctness remains to be proved. *)
  Definition ladder_result (x2 z2 x3 z3 x1 a24 : bv n) : state :=
    run_ticks (ladder_init x2 z2 x3 z3 x1 a24) 54.

  Lemma ladder_result_valid (x2 z2 x3 z3 x1 a24 : bv n) : valid_state (ladder_result x2 z2 x3 z3 x1 a24).
  Proof.
    unfold ladder_result.
    apply run_ticks_preserves_valid, ladder_init_valid.
  Qed.

  (* Cycle-boundary HW observation. *)
  Definition HW_bv (v : bv n) : nat :=
    fold_left (fun (acc : nat) (b : bool) => if b then (acc + 1)%nat else acc) (bv_to_bits v) 0%nat.

  (* Counts bitvector fields, including inactive latch/bus payloads.
     Stage, valid bits, write enable, and the nat destination are not counted. *)
  Definition state_HW (s : state) : nat :=
    let hw_regs  := Vector.fold_left (fun acc v => (acc + HW_bv v)%nat) 0%nat s.(Regs)  in
    let hw_dregs := Vector.fold_left (fun acc v => (acc + HW_bv v)%nat) 0%nat s.(DRegs) in
    let hw_imem  := fold_left (fun acc v => (acc + HW_bv v)%nat) s.(InstrMem) 0%nat     in
    let '(((_, _), val), dval) := s.(bookkeepingState) in
    ( HW_bv s.(pc)
    + hw_regs
    + hw_dregs
    + hw_imem
    + HW_bv (snd s.(toiMem))
    + HW_bv (snd s.(fromiMem))
    + HW_bv val
    + HW_bv dval)%nat.

  Definition total_HW_observable (s : state) : nat :=
    state_HW s.

  Definition protected_HW (s : state) : nat :=
    let '(((_, _), val), dval) := s.(bookkeepingState) in
    (Vector.fold_left (fun acc v => acc + HW_bv v)%nat 0%nat s.(Regs) +
     Vector.fold_left (fun acc v => acc + HW_bv v)%nat 0%nat s.(DRegs) +
     HW_bv val + HW_bv dval)%nat.

  (* Trace security still requires these fields to agree across secrets. *)
  Definition public_HW (s : state) : nat :=
    (HW_bv s.(pc) +
     fold_left (fun acc v => acc + HW_bv v)%nat s.(InstrMem) 0%nat +
     HW_bv (snd s.(toiMem)) + HW_bv (snd s.(fromiMem)))%nat.

  Local Lemma vector_pair_HW {m} (regs : Vector.t (bv n) m) : forall a b,
    (Vector.fold_left (fun acc v => acc + HW_bv v)%nat a regs +
     Vector.fold_left (fun acc v => acc + HW_bv v)%nat b (Vector.map bv_not regs))%nat =
    (m * N.to_nat n + a + b)%nat.
  Proof.
    induction regs as [| value m rest IH]; intros a b; cbn [Vector.fold_left Vector.map].
    - lia.
    - rewrite IH. pose proof (hw_complement n value) as Hpair.
      change (HW_bv value + HW_bv (bv_not value) = N.to_nat n)%nat in Hpair. nia.
  Qed.

  Lemma valid_state_duals s : valid_state s -> DRegs s = Vector.map bv_not (Regs s).
  Proof.
    intros [Hregs _]. apply (proj1 (Vector.eq_nth_iff _ _ _ _)).
    intros j k Heq. subst k. rewrite (@Vector.nth_map _ _ _ _ _ j j eq_refl). apply Hregs.
  Qed.

  (* The 32 register pairs and the execution-latch pair each contribute n bits. *)
  Theorem protected_HW_constant s : valid_state s -> protected_HW s = (33 * N.to_nat n)%nat.
  Proof.
    intro Hvalid. pose proof (valid_state_duals s Hvalid) as Hduals.
    destruct Hvalid as [_ Hlatch]. unfold protected_HW. rewrite Hduals.
    destruct (bookkeepingState s) as [[[active rd] value] dual]. cbn in Hlatch. subst dual.
    pose proof (vector_pair_HW (Regs s) 0%nat 0%nat) as Hregs.
    pose proof (hw_complement n value) as Hpair.
    change (HW_bv value + HW_bv (bv_not value) = N.to_nat n)%nat in Hpair. lia.
  Qed.

  Corollary run_ticks_protected_HW s cycles :
    valid_state s -> protected_HW (run_ticks s cycles) = (33 * N.to_nat n)%nat.
  Proof. intro Hvalid. apply protected_HW_constant, run_ticks_preserves_valid, Hvalid. Qed.

  Lemma state_HW_decomposition s : valid_state s -> state_HW s = (public_HW s + 33 * N.to_nat n)%nat.
  Proof.
    intro Hvalid. pose proof (protected_HW_constant s Hvalid) as Hprotected.
    unfold state_HW, public_HW, protected_HW in *.
    destruct (bookkeepingState s) as [[[active rd] value] dual]. lia.
  Qed.

  Theorem state_HW_public s1 s2 :
    valid_state s1 -> valid_state s2 ->
    pc s1 = pc s2 -> InstrMem s1 = InstrMem s2 ->
    snd (toiMem s1) = snd (toiMem s2) -> snd (fromiMem s1) = snd (fromiMem s2) ->
    state_HW s1 = state_HW s2.
  Proof.
    intros H1 H2 Hpc Himem Haddr Hdata.
    rewrite !state_HW_decomposition by assumption.
    unfold public_HW. rewrite Hpc, Himem, Haddr, Hdata. reflexivity.
  Qed.

  (* Initial states only; this is not yet a full leakage-trace theorem. *)
  Theorem power_independence imem regs1 regs2 :
    total_HW_observable (mk_processor_state imem regs1) =
    total_HW_observable (mk_processor_state imem regs2).
  Proof.
    unfold total_HW_observable. apply state_HW_public;
      try apply mk_processor_state_valid; reflexivity.
  Qed.

End StateMachine.
End StateMachine.
