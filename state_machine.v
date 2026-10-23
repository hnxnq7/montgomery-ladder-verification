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

Require Import dual_circuit ladder_math.

(* Cycle-level processor with complementary registers and two paired result latches. *)
Module StateMachine.

  (* One stage runs per cycle; instructions do not overlap. *)
  Inductive PipelineStage :=
    | Fetch
    | Execute
    | WriteBack.

  Inductive instr :=
    | IAdd (rd ra rb : nat)
    | ISub (rd ra rb : nat)
    | IMul (rd ra rb : nat)
    | Observe (r : nat)
    | Copy (rd rs : nat)
    | GetBit (rd rs index : nat)
    | Xor (rd ra rb : nat)
    | CSwap (control ra rb : nat).

  Definition lift_instr (e : dual_circuit.instr) : instr :=
    match e with
    | dual_circuit.IAdd d a b => IAdd d a b
    | dual_circuit.ISub d a b => ISub d a b
    | dual_circuit.IMul d a b => IMul d a b
    | dual_circuit.Observe r => Observe r
    end.

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
    bookkeepingState : bool * nat * bv n * bv n;
    bookkeepingState2 : bool * nat * bv n * bv n
  }.
  Instance eta : Settable state :=
    settable! mkState <pc; Regs; DRegs; InstrMem; Stage; toiMem; fromiMem; bookkeepingState; bookkeepingState2>.

  (* All register and execution-latch values stay paired, even when inactive. *)
  Definition valid_state (s : state) : Prop :=
    (forall j : Fin.t 32, Vector.nth s.(DRegs) j = bv_not (Vector.nth s.(Regs) j)) /\
    (let '(((_, _), val), dval) := s.(bookkeepingState) in dval = bv_not val) /\
    (let '(((_, _), val), dval) := s.(bookkeepingState2) in dval = bv_not val).

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
  (* First write result. Observe is a no-op; CSwap swaps exactly when control = 1. *)
  Definition exec_instr (rs : Vector.t (bv n) 32) (e : instr) : bool * var * bv n :=
    let get r := read_reg rs r in
    match e with
    | IAdd rd rs1 rs2 => (true,  rd, fadd_bv n modulus (get rs1) (get rs2))
    | ISub rd rs1 rs2 => (true,  rd, fsub_bv n modulus (get rs1) (get rs2))
    | IMul rd rs1 rs2 => (true,  rd, fmul_bv n modulus (get rs1) (get rs2))
    | Observe _       => (false, 0%nat, bv_0 n)
    | Copy rd rs => (true, rd, get rs)
    | GetBit rd rs index =>
        (true, rd, Z_to_bv n (if Z.testbit (bv_unsigned (get rs)) (Z.of_nat index) then 1 else 0))
    | Xor rd ra rb => (true, rd, bv_xor (get ra) (get rb))
    | CSwap control ra rb =>
        (true, ra, if Z.eqb (bv_unsigned (get control)) 1 then get rb else get ra)
    end.

  Definition exec_instr2 (rs : Vector.t (bv n) 32) (e : instr) : bool * var * bv n :=
    match e with
    | CSwap control ra rb =>
        (true, rb, if Z.eqb (bv_unsigned (read_reg rs control)) 1 then read_reg rs ra else read_reg rs rb)
    | _ => (false, 0%nat, bv_0 n)
    end.

  (* Layout: [last(8)|rs1(5)|rd(5)|op(3)]; n >= 21, registers < 32, bit indices < 256.
     Opcodes: 0=IAdd, 1=ISub, 2=IMul, 3=Observe, 4=Copy, 5=GetBit, 6=Xor, 7=CSwap. *)
  Definition encode_instr (e : instr) : bv n :=
    let pack (op rd rs1 rs2 : nat) :=
      Z_to_bv n (Z.of_nat op
               + Z.of_nat rd * 8
               + Z.of_nat rs1 * 256
               + Z.of_nat rs2 * 8192) in
    match e with
    | IAdd rd rs1 rs2 => pack 0%nat rd rs1 rs2
    | ISub rd rs1 rs2 => pack 1%nat rd rs1 rs2
    | IMul rd rs1 rs2 => pack 2%nat rd rs1 rs2
    | Observe ro      => pack 3%nat ro 0%nat 0%nat
    | Copy rd rs => pack 4%nat rd rs 0%nat
    | GetBit rd rs index => pack 5%nat rd rs index
    | Xor rd ra rb => pack 6%nat rd ra rb
    | CSwap control ra rb => pack 7%nat control ra rb
    end.

  Definition decode_instr (b : bv n) : option instr :=
    let v   := bv_unsigned b in
    let op  := Z.to_nat (v mod 8) in
    let rd  := Z.to_nat (v / 8   mod 32) in
    let rs1 := Z.to_nat (v / 256  mod 32) in
    let rs2 := Z.to_nat (v / 8192 mod 256) in
    match op with
    | 0%nat => Some (IAdd rd rs1 rs2)
    | 1%nat => Some (ISub rd rs1 rs2)
    | 2%nat => Some (IMul rd rs1 rs2)
    | 3%nat => Some (Observe rd)
    | 4%nat => Some (Copy rd rs1)
    | 5%nat => Some (GetBit rd rs1 rs2)
    | 6%nat => Some (Xor rd rs1 rs2)
    | 7%nat => Some (CSwap rd rs1 rs2)
    | _     => None
    end.

  Definition instr_in_bounds (e : instr) : Prop :=
    match e with
    | IAdd rd ra rb | ISub rd ra rb | IMul rd ra rb | Xor rd ra rb | CSwap rd ra rb =>
        (rd < 32 /\ ra < 32 /\ rb < 32)%nat
    | Observe r => (r < 32)%nat
    | Copy rd rs => (rd < 32 /\ rs < 32)%nat
    | GetBit rd rs index => (rd < 32 /\ rs < 32 /\ index < 256)%nat
    end.

  Local Lemma packed_fields op rd ra rb :
    0 <= op < 8 -> 0 <= rd < 32 -> 0 <= ra < 32 -> 0 <= rb < 256 ->
    let word := op + rd * 8 + ra * 256 + rb * 8192 in
    word mod 8 = op /\ (word / 8) mod 32 = rd /\
    (word / 256) mod 32 = ra /\ (word / 8192) mod 256 = rb.
  Proof.
    intros Hop Hrd Hra Hrb. cbv zeta. repeat split.
    - replace (op + rd * 8 + ra * 256 + rb * 8192) with (op + (rd + ra * 32 + rb * 1024) * 8) by ring.
      rewrite Z.mod_add by lia. apply Z.mod_small. exact Hop.
    - replace (op + rd * 8 + ra * 256 + rb * 8192) with (op + (rd + ra * 32 + rb * 1024) * 8) by ring.
      rewrite Z.div_add, Z.div_small by lia. rewrite Z.add_0_l.
      replace (rd + ra * 32 + rb * 1024) with (rd + (ra + rb * 32) * 32) by ring.
      rewrite Z.mod_add by lia. apply Z.mod_small. exact Hrd.
    - replace (op + rd * 8 + ra * 256 + rb * 8192) with ((op + rd * 8) + (ra + rb * 32) * 256) by ring.
      rewrite Z.div_add, Z.div_small by lia. rewrite Z.add_0_l.
      rewrite Z.mod_add by lia. apply Z.mod_small. exact Hra.
    - rewrite Z.div_add, Z.div_small by lia. rewrite Z.add_0_l.
      apply Z.mod_small. exact Hrb.
  Qed.

  Lemma decode_encode_instr e :
    (21 <= n)%N -> instr_in_bounds e -> decode_instr (encode_instr e) = Some e.
  Proof.
    intros Hwidth Hbounds.
    assert (Hcapacity : 2097152 <= 2 ^ Z.of_N n).
    { change (2 ^ 21 <= 2 ^ Z.of_N n). apply Z.pow_le_mono_r; lia. }
    destruct e as [rd ra rb | rd ra rb | rd ra rb | rd | rd ra | rd ra rb | rd ra rb | rd ra rb]; cbn [instr_in_bounds] in Hbounds.
    all: unfold decode_instr, encode_instr; cbv beta zeta.
    all: rewrite Z_to_bv_small by (unfold bv_modulus; lia).
    all: match goal with
      | |- context [Z.to_nat ((?op + Z.of_nat ?rd * 8 + Z.of_nat ?ra * 256 + Z.of_nat ?rb * 8192) mod 8)] =>
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
          let '((we2, rd2), v2) := exec_instr2 s.(Regs) e in
          s <|bookkeepingState := (((we, rd), v), bv_not v)|>
            <|bookkeepingState2 := (((we2, rd2), v2), bv_not v2)|>
            <|fromiMem := (false, encoded)|>
            <|pc    := bv_add s.(pc) (Z_to_bv n 1)|>
            <|Stage := WriteBack|>
      end
    else
      s <|Stage := WriteBack|>.

  Definition idle_result : bool * nat * bv n * bv n :=
    (((false, 0%nat), bv_0 n), bv_not (bv_0 n)).

  Definition apply_write (rs : Vector.t (bv n) 32) (w : bool * nat * bv n) :=
    let '(we, rd, value) := w in if we then write_reg rs rd value else rs.

  (* Both paired writes commit in one cycle; all operands were read during Execute. *)
  Definition writeback (s : state) : state :=
    let '(((we, rd), val), dval) := s.(bookkeepingState) in
    let '(((we2, rd2), val2), dval2) := s.(bookkeepingState2) in
    s <|Regs := apply_write (apply_write s.(Regs) (we, rd, val)) (we2, rd2, val2)|>
      <|DRegs := apply_write (apply_write s.(DRegs) (we, rd, dval)) (we2, rd2, dval2)|>
      <|bookkeepingState := idle_result|>
      <|bookkeepingState2 := idle_result|>
      <|Stage := Fetch|>.

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
     ; bookkeepingState := idle_result
     ; bookkeepingState2 := idle_result |}.

  Lemma mk_processor_state_valid imem regs : valid_state (mk_processor_state imem regs).
  Proof.
    unfold valid_state, mk_processor_state. cbn [Regs DRegs bookkeepingState bookkeepingState2]. split.
    - intro j. rewrite (@Vector.nth_map _ _ _ _ _ j j eq_refl). reflexivity.
    - split; reflexivity.
  Qed.

  Local Lemma apply_write_paired regs duals we rd value :
    (forall j, Vector.nth duals j = bv_not (Vector.nth regs j)) ->
    forall j, Vector.nth (apply_write duals (we, rd, bv_not value)) j =
      bv_not (Vector.nth (apply_write regs (we, rd, value)) j).
  Proof.
    intros H j. destruct we; cbn [apply_write]; [|apply H].
    destruct (Nat.eq_dec (proj1_sig (Fin.to_nat j)) rd).
    - rewrite !nth_write_reg_same by assumption. reflexivity.
    - rewrite !nth_write_reg_diff by assumption. apply H.
  Qed.

  Lemma tick_preserves_valid : forall (s : state), valid_state s -> valid_state (tick s).
  Proof.
    intros s H. unfold tick. destruct (Stage s).
    - exact H.
    - unfold execute. destruct (fromiMem s) as [active encoded].
      destruct active; [|exact H]. destruct (decode_instr encoded) as [e|]; [|exact H].
      destruct (exec_instr (Regs s) e) as [[we rd] value].
      destruct (exec_instr2 (Regs s) e) as [[we2 rd2] value2].
      split; [exact (proj1 H)|split; reflexivity].
    - destruct H as [Hr [H1 H2]]. unfold writeback.
      destruct (bookkeepingState s) as [[[we rd] value] dual].
      destruct (bookkeepingState2 s) as [[[we2 rd2] value2] dual2].
      cbn in H1, H2. subst dual dual2.
      split; [|split; reflexivity].
      apply apply_write_paired, apply_write_paired, Hr.
  Qed.

  Definition ladder_instr_mem : list (bv n) :=
    map (fun e => encode_instr (lift_instr e)) program.

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

  Local Lemma fetch_cycle counter regs duals imem request response pending pending2 encoded :
    nth_error imem (Z.to_nat (bv_unsigned counter)) = Some encoded ->
    full_tick (mkState counter regs duals imem Fetch request response pending pending2) =
    mkState counter regs duals imem Execute (false, counter) (true, encoded) pending pending2.
  Proof.
    intro Hfetch. unfold full_tick, tick, fetch, tick_iMem. cbn.
    rewrite Hfetch. reflexivity.
  Qed.

  Local Lemma execute_cycle counter regs duals imem addr encoded pending pending2 e we rd value we2 rd2 value2 :
    decode_instr encoded = Some e -> exec_instr regs e = (we, rd, value) ->
    exec_instr2 regs e = (we2, rd2, value2) ->
    full_tick (mkState counter regs duals imem Execute (false, addr) (true, encoded) pending pending2) =
    mkState (bv_add counter (Z_to_bv n 1)) regs duals imem WriteBack (false, addr) (false, encoded)
      (((we, rd), value), bv_not value) (((we2, rd2), value2), bv_not value2).
  Proof.
    intros Hd H1 H2. unfold full_tick, tick. cbn [Stage].
    unfold execute. cbn [fromiMem Regs]. rewrite Hd, H1, H2. reflexivity.
  Qed.

  Theorem instruction_cycle_correct s encoded e we rd value we2 rd2 value2 :
    Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some encoded ->
    decode_instr encoded = Some e ->
    exec_instr (Regs s) e = (we, rd, value) ->
    exec_instr2 (Regs s) e = (we2, rd2, value2) ->
    let final := run_ticks s 3 in
    Regs final = apply_write (apply_write (Regs s) (we, rd, value)) (we2, rd2, value2) /\
    DRegs final = apply_write (apply_write (DRegs s) (we, rd, bv_not value)) (we2, rd2, bv_not value2) /\
    pc final = bv_add (pc s) (Z_to_bv n 1) /\
    Stage final = Fetch /\ InstrMem final = InstrMem s.
  Proof.
    destruct s as [counter regs duals imem stage request response pending pending2].
    cbn. intros Hstage Hfetch Hd H1 H2. subst stage.
    rewrite fetch_cycle with (encoded := encoded) by exact Hfetch.
    rewrite execute_cycle with (e := e) (we := we) (rd := rd) (value := value)
      (we2 := we2) (rd2 := rd2) (value2 := value2) by assumption.
    destruct we, we2; repeat split; reflexivity.
  Qed.

  Lemma run_ticks_add s first rest :
    run_ticks s (first + rest) = run_ticks (run_ticks s first) rest.
  Proof. revert s. induction first; intro s; cbn [run_ticks Nat.add]; auto. Qed.

  Lemma run_instruction counter regs duals imem request response pending pending2 e rest :
    (21 <= n)%N -> instr_in_bounds e ->
    nth_error imem (Z.to_nat (bv_unsigned counter)) = Some (encode_instr e) ->
    let '(we, rd, value) := exec_instr regs e in
    let '(we2, rd2, value2) := exec_instr2 regs e in
    run_ticks (mkState counter regs duals imem Fetch request response pending pending2) (3 + rest) =
    run_ticks
      (mkState (bv_add counter (Z_to_bv n 1))
        (apply_write (apply_write regs (we, rd, value)) (we2, rd2, value2))
        (apply_write (apply_write duals (we, rd, bv_not value)) (we2, rd2, bv_not value2))
        imem Fetch (false, counter) (false, encode_instr e) idle_result idle_result) rest.
  Proof.
    intros Hw Hb Hfetch.
    destruct (exec_instr regs e) as [[we rd] value] eqn:H1.
    destruct (exec_instr2 regs e) as [[we2 rd2] value2] eqn:H2.
    rewrite run_ticks_add. cbn [run_ticks].
    rewrite fetch_cycle with (encoded := encode_instr e) by exact Hfetch.
    rewrite execute_cycle with (e := e) (we := we) (rd := rd) (value := value)
      (we2 := we2) (rd2 := rd2) (value2 := value2)
      by (try assumption; apply decode_encode_instr; assumption).
    reflexivity.
  Qed.

  Lemma read_write_reg_same rs rd value :
    (rd < 32)%nat -> read_reg (write_reg rs rd value) rd = value.
  Proof.
    intro Hrd. unfold read_reg. destruct (Fin.of_nat rd 32) as [j | [extra Hextra]] eqn:Hindex.
    - apply nth_write_reg_same. exact (of_nat_inleft_to_nat rd 32 j Hindex).
    - lia.
  Qed.

  Lemma instruction_cycle_write s e rd value :
    (21 <= n)%N -> instr_in_bounds e -> (rd < 32)%nat -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr e) ->
    exec_instr (Regs s) e = (true, rd, value) ->
    exec_instr2 (Regs s) e = (false, 0%nat, bv_0 n) ->
    read_reg (Regs (run_ticks s 3)) rd = value.
  Proof.
    intros Hwidth Hbounds Hrd Hstage Hfetch Hexec Hexec2.
    pose proof (instruction_cycle_correct s (encode_instr e) e true rd value false 0%nat (bv_0 n) Hstage Hfetch
      (decode_encode_instr e Hwidth Hbounds) Hexec Hexec2) as Hcycle.
    destruct Hcycle as [Hregs _]. rewrite Hregs. cbn [apply_write]. apply read_write_reg_same. exact Hrd.
  Qed.

  Corollary add_cycle_correct s rd ra rb :
    (21 <= n)%N -> 0 < bv_unsigned modulus ->
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
    (21 <= n)%N -> 0 < bv_unsigned modulus ->
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
    (21 <= n)%N -> 0 < bv_unsigned modulus ->
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


  Corollary copy_cycle_correct s rd rs :
    (21 <= n)%N -> instr_in_bounds (Copy rd rs) -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr (Copy rd rs)) ->
    read_reg (Regs (run_ticks s 3)) rd = read_reg (Regs s) rs.
  Proof.
    intros Hw Hb Hs Hf. apply (instruction_cycle_write s (Copy rd rs));
      try assumption; try reflexivity; exact (proj1 Hb).
  Qed.

  Corollary getbit_cycle_correct s rd rs index :
    (21 <= n)%N -> instr_in_bounds (GetBit rd rs index) -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr (GetBit rd rs index)) ->
    read_reg (Regs (run_ticks s 3)) rd =
      Z_to_bv n (if Z.testbit (bv_unsigned (read_reg (Regs s) rs)) (Z.of_nat index) then 1 else 0).
  Proof.
    intros Hw Hb Hs Hf. apply (instruction_cycle_write s (GetBit rd rs index));
      try assumption; try reflexivity; exact (proj1 Hb).
  Qed.

  Corollary xor_cycle_correct s rd ra rb :
    (21 <= n)%N -> instr_in_bounds (Xor rd ra rb) -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr (Xor rd ra rb)) ->
    read_reg (Regs (run_ticks s 3)) rd = bv_xor (read_reg (Regs s) ra) (read_reg (Regs s) rb).
  Proof.
    intros Hw Hb Hs Hf. apply (instruction_cycle_write s (Xor rd ra rb));
      try assumption; try reflexivity; exact (proj1 Hb).
  Qed.

  Lemma read_write_reg_diff rs rd r value :
    rd <> r -> read_reg (write_reg rs rd value) r = read_reg rs r.
  Proof.
    intro Hneq. unfold read_reg.
    destruct (Fin.of_nat r 32) as [j|extra] eqn:Hindex; [|reflexivity].
    apply nth_write_reg_diff. rewrite (of_nat_inleft_to_nat r 32 j Hindex). congruence.
  Qed.

  Theorem cswap_cycle_correct s control ra rb :
    (21 <= n)%N -> instr_in_bounds (CSwap control ra rb) -> Stage s = Fetch ->
    nth_error (InstrMem s) (Z.to_nat (bv_unsigned (pc s))) = Some (encode_instr (CSwap control ra rb)) ->
    let swap := Z.eqb (bv_unsigned (read_reg (Regs s) control)) 1 in
    let a := read_reg (Regs s) ra in
    let b := read_reg (Regs s) rb in
    read_reg (Regs (run_ticks s 3)) ra = (if swap then b else a) /\
    read_reg (Regs (run_ticks s 3)) rb = (if swap then a else b) /\
    (forall r, r <> ra -> r <> rb -> read_reg (Regs (run_ticks s 3)) r = read_reg (Regs s) r).
  Proof.
    intros Hw Hb Hs Hf. cbv zeta.
    pose proof (instruction_cycle_correct s (encode_instr (CSwap control ra rb))
      (CSwap control ra rb) true ra
      (if Z.eqb (bv_unsigned (read_reg (Regs s) control)) 1 then read_reg (Regs s) rb else read_reg (Regs s) ra)
      true rb
      (if Z.eqb (bv_unsigned (read_reg (Regs s) control)) 1 then read_reg (Regs s) ra else read_reg (Regs s) rb)
      Hs Hf (decode_encode_instr _ Hw Hb) eq_refl eq_refl) as [Hr _].
    rewrite Hr. cbn [apply_write]. destruct Hb as [Hc [Ha Hb]].
    split.
    - destruct (Nat.eq_dec ra rb) as [Heq|Hneq].
      + subst rb. rewrite read_write_reg_same by assumption.
        destruct (Z.eqb _ _); reflexivity.
      + rewrite read_write_reg_diff by congruence. apply read_write_reg_same, Ha.
    - split.
      + apply read_write_reg_same, Hb.
      + intros r Hra Hrb. rewrite !read_write_reg_diff by congruence. reflexivity.
  Qed.
  (* 54 cycles for the 18-instruction program. *)
  Definition ladder_result (x2 z2 x3 z3 x1 a24 : bv n) : state :=
    run_ticks (ladder_init x2 z2 x3 z3 x1 a24) 54.

  Lemma ladder_result_valid (x2 z2 x3 z3 x1 a24 : bv n) : valid_state (ladder_result x2 z2 x3 z3 x1 a24).
  Proof.
    unfold ladder_result.
    apply run_ticks_preserves_valid, ladder_init_valid.
  Qed.

  Definition ladder_output (s : state) : Z * Z * Z * Z :=
    (bv_unsigned (read_reg (Regs s) 19%nat), bv_unsigned (read_reg (Regs s) 23%nat),
     bv_unsigned (read_reg (Regs s) 16%nat), bv_unsigned (read_reg (Regs s) 18%nat)).

  Local Lemma counter_increment index :
    0 <= index < 2 ^ Z.of_N n -> 1 < 2 ^ Z.of_N n ->
    bv_add (Z_to_bv n index) (Z_to_bv n 1) = Z_to_bv n (index + 1).
  Proof.
    intros Hi Hn. apply bv_eq.
    rewrite bv_add_unsigned, (Z_to_bv_small n index), (Z_to_bv_small n 1)
      by (unfold bv_modulus; lia).
    symmetry. apply Z_to_bv_unsigned.
  Qed.


  Definition execute_regs (regs : Vector.t (bv n) 32) (e : instr) : Vector.t (bv n) 32 :=
    let '(we, rd, value) := exec_instr regs e in
    let '(we2, rd2, value2) := exec_instr2 regs e in
    apply_write (apply_write regs (we, rd, value)) (we2, rd2, value2).

  Fixpoint run_code (regs : Vector.t (bv n) 32) (code : list instr) : Vector.t (bv n) 32 :=
    match code with
    | [] => regs
    | e :: rest => run_code (execute_regs regs e) rest
    end.

  (* Each instruction is fetched at its offset in the same instruction memory. *)
  Local Lemma run_code_from_pc code offset regs duals imem request response pending pending2 :
    (21 <= n)%N -> Forall instr_in_bounds code ->
    Z.of_nat (offset + length code) < 2 ^ Z.of_N n ->
    (forall j e, nth_error code j = Some e ->
      nth_error imem (offset + j)%nat = Some (encode_instr e)) ->
    let final := run_ticks
      (mkState (Z_to_bv n (Z.of_nat offset)) regs duals imem Fetch request response pending pending2)
      (3 * length code) in
    Regs final = run_code regs code /\
    pc final = Z_to_bv n (Z.of_nat (offset + length code)) /\ Stage final = Fetch.
  Proof.
    revert offset regs duals imem request response pending pending2.
    induction code as [|e code IH]; intros offset regs duals imem request response pending pending2 Hw Hb Hcap Hmem.
    - cbn. rewrite Nat.add_0_r. repeat split; reflexivity.
    - inversion Hb as [|? ? He Hrest]; subst.
      assert (Hfetch : nth_error imem (Z.to_nat (bv_unsigned (Z_to_bv n (Z.of_nat offset)))) =
        Some (encode_instr e)).
      { rewrite Z_to_bv_small by (unfold bv_modulus; cbn [length] in Hcap; lia).
        rewrite Nat2Z.id. specialize (Hmem 0%nat e eq_refl).
        rewrite Nat.add_0_r in Hmem. exact Hmem. }
      replace (3 * length (e :: code))%nat with (3 + 3 * length code)%nat by (cbn [length]; lia).
      pose proof (run_instruction (Z_to_bv n (Z.of_nat offset)) regs duals imem request response
        pending pending2 e (3 * length code)%nat Hw He Hfetch) as Hstep.
      unfold execute_regs. cbn [run_code]. unfold execute_regs.
      destruct (exec_instr regs e) as [[we rd] value] eqn:H1.
      destruct (exec_instr2 regs e) as [[we2 rd2] value2] eqn:H2.
      cbn beta iota zeta in Hstep. rewrite Hstep.
      rewrite counter_increment by (cbn [length] in Hcap; lia).
      replace (Z.of_nat offset + 1) with (Z.of_nat (S offset)) by lia.
      replace (offset + length (e :: code))%nat with (S offset + length code)%nat by (cbn [length]; lia).
      apply IH; try assumption.
      + cbn [length] in Hcap. lia.
      + intros j next Hnext. replace (S offset + j)%nat with (offset + S j)%nat by lia.
        apply Hmem. exact Hnext.
  Qed.

  Theorem run_code_correct regs code :
    (21 <= n)%N -> Forall instr_in_bounds code ->
    Z.of_nat (length code) < 2 ^ Z.of_N n ->
    let final := run_ticks (mk_processor_state (map encode_instr code) regs) (3 * length code) in
    Regs final = run_code regs code /\
    pc final = Z_to_bv n (Z.of_nat (length code)) /\ Stage final = Fetch.
  Proof.
    intros Hw Hb Hcap. unfold mk_processor_state.
    assert (Hzero : bv_0 n = Z_to_bv n 0).
    { apply bv_eq. rewrite bv_0_unsigned, Z_to_bv_small by
        (unfold bv_modulus; pose proof (Z.pow_pos_nonneg 2 (Z.of_N n)); lia). reflexivity. }
    rewrite Hzero.
    apply (run_code_from_pc code 0%nat); try assumption.
    intros j e Hlookup. cbn [Nat.add].
    rewrite nth_error_map, Hlookup. reflexivity.
  Qed.
  Theorem ladder_block_correct regs :
    (21 <= n)%N -> 0 < bv_unsigned modulus ->
    let get r := bv_unsigned (read_reg regs r) in
    ladder_output (run_ticks (mk_processor_state ladder_instr_mem regs) 54) =
    LadderStep (bv_unsigned modulus) (get 5%nat) (get 0%nat)
      (get 1%nat) (get 2%nat) (get 3%nat) (get 4%nat).
  Proof.
    intros Hw Hp.
    assert (Hcapacity : 2097152 <= 2 ^ Z.of_N n).
    { change (2 ^ 21 <= 2 ^ Z.of_N n). apply Z.pow_le_mono_r; lia. }
    cbv zeta. unfold mk_processor_state.
    assert (Hzero : bv_0 n = Z_to_bv n 0).
    { apply bv_eq. rewrite bv_0_unsigned, Z_to_bv_small by (unfold bv_modulus; lia). reflexivity. }
    rewrite Hzero.
    do 18 (
      match goal with
      | |- context [run_ticks (mkState (Z_to_bv n ?index) ?regs ?duals ?imem Fetch ?req ?resp ?l1 ?l2) ?fuel] =>
        let position := eval vm_compute in (Z.to_nat index) in
        let instruction := eval cbv [List.nth program lift_instr] in
          (lift_instr (List.nth position program (dual_circuit.Observe 0%nat))) in
        let remaining := eval compute in (fuel - 3)%nat in
        let Hstep := fresh "Hstep" in
        pose proof (run_instruction (Z_to_bv n index) regs duals imem req resp l1 l2 instruction remaining
          Hw ltac:(cbn [instr_in_bounds]; lia)
          ltac:(rewrite Z_to_bv_small by (unfold bv_modulus; lia); reflexivity)) as Hstep;
        cbn [exec_instr exec_instr2 Nat.add] in Hstep;
        rewrite Hstep; clear Hstep
      end;
      cbn [exec_instr exec_instr2 apply_write];
      repeat first [rewrite read_write_reg_same by lia | rewrite read_write_reg_diff by lia];
      repeat match goal with
      | |- context [fadd_bv n modulus ?a ?b] => let v := fresh "value" in set (v := fadd_bv n modulus a b)
      | |- context [fsub_bv n modulus ?a ?b] => let v := fresh "value" in set (v := fsub_bv n modulus a b)
      | |- context [fmul_bv n modulus ?a ?b] => let v := fresh "value" in set (v := fmul_bv n modulus a b)
      end;
      rewrite counter_increment by lia).
    cbn [run_ticks]. unfold ladder_output. cbn [Regs].
    repeat first [rewrite read_write_reg_same by lia | rewrite read_write_reg_diff by lia].
    repeat match goal with v := _ |- _ =>
      match goal with |- context [v] =>
        unfold v
      end
    end.
    repeat first [rewrite fadd_bv_correct by exact Hp |
                  rewrite fsub_bv_correct by exact Hp | rewrite fmul_bv_correct by exact Hp].
    unfold LadderStep, fsq, fadd, fsub, fmul. reflexivity.
  Qed.

  Theorem ladder_result_correct x2 z2 x3 z3 x1 a24 :
    (21 <= n)%N -> 0 < bv_unsigned modulus ->
    ladder_output (ladder_result x2 z2 x3 z3 x1 a24) =
    LadderStep (bv_unsigned modulus) (bv_unsigned a24) (bv_unsigned x1)
      (bv_unsigned x2) (bv_unsigned z2) (bv_unsigned x3) (bv_unsigned z3).
  Proof.
    intros Hw Hp. unfold ladder_result, ladder_init.
    rewrite ladder_block_correct by assumption. unfold ladder_regs.
    repeat first [rewrite read_write_reg_same by lia | rewrite read_write_reg_diff by lia].
    reflexivity.
  Qed.

  (* Registers 24..27 hold the scalar, previous bit, current bit, and swap control. *)
  Definition iteration_code (index : nat) : list instr :=
    [GetBit 26%nat 24%nat index; Xor 27%nat 26%nat 25%nat;
     CSwap 27%nat 1%nat 3%nat; CSwap 27%nat 2%nat 4%nat] ++ map lift_instr program ++
    [Copy 1%nat 19%nat; Copy 2%nat 23%nat; Copy 3%nat 16%nat;
     Copy 4%nat 18%nat; Copy 25%nat 26%nat].

  Definition iteration_result (regs : Vector.t (bv n) 32) (index : nat) : state :=
    run_ticks (mk_processor_state (map encode_instr (iteration_code index)) regs) 81.

  Definition point_regs (s : state) : Z * Z * Z * Z :=
    (bv_unsigned (read_reg (Regs s) 1%nat), bv_unsigned (read_reg (Regs s) 2%nat),
     bv_unsigned (read_reg (Regs s) 3%nat), bv_unsigned (read_reg (Regs s) 4%nat)).

  Lemma iteration_code_length index : length (iteration_code index) = 27%nat.
  Proof. reflexivity. Qed.

  Theorem iteration_correct regs index previous :
    (21 <= n)%N -> (index < 256)%nat -> 0 < bv_unsigned modulus ->
    bv_unsigned (read_reg regs 25%nat) = Z.b2z previous ->
    let get r := bv_unsigned (read_reg regs r) in
    let expected := MontLadderCSwap_step (bv_unsigned modulus) (get 5%nat) (get 0%nat)
      (bit_i (get 24%nat) index) previous (get 1%nat, get 2%nat, get 3%nat, get 4%nat) in
    let final := iteration_result regs index in
    (point_regs final, bv_unsigned (read_reg (Regs final) 25%nat)) = (expected.1, Z.b2z expected.2) /\
    read_reg (Regs final) 0%nat = read_reg regs 0%nat /\
    read_reg (Regs final) 5%nat = read_reg regs 5%nat /\
    read_reg (Regs final) 24%nat = read_reg regs 24%nat /\
    bv_unsigned (pc final) = 27 /\ Stage final = Fetch.
  Proof.
    intros Hw Hi Hp Hprevious.
    assert (Hcapacity : 2097152 <= 2 ^ Z.of_N n).
    { change (2 ^ 21 <= 2 ^ Z.of_N n). apply Z.pow_le_mono_r; lia. }
    assert (Hprev : read_reg regs 25%nat = Z_to_bv n (Z.b2z previous)).
    { apply bv_eq. rewrite Hprevious, Z_to_bv_small by
        (unfold bv_modulus; destruct previous; cbn; lia). reflexivity. }
    cbv zeta. unfold iteration_result, mk_processor_state.
    assert (Hzero : bv_0 n = Z_to_bv n 0).
    { apply bv_eq. rewrite bv_0_unsigned, Z_to_bv_small by (unfold bv_modulus; lia). reflexivity. }
    rewrite Hzero.
    remember (Z.testbit (bv_unsigned (read_reg regs 24%nat)) (Z.of_nat index)) as current eqn:Hbit.
    do 27 (
      match goal with
      | |- context [run_ticks (mkState (Z_to_bv n ?counter) ?rs ?ds ?imem Fetch ?req ?resp ?l1 ?l2) ?fuel] =>
        let position := eval vm_compute in (Z.to_nat counter) in
        let instruction := eval cbv [List.nth iteration_code program lift_instr map app] in
          (List.nth position (iteration_code index) (Observe 0%nat)) in
        let remaining := eval compute in (fuel - 3)%nat in
        let Hstep := fresh "Hstep" in
        pose proof (run_instruction (Z_to_bv n counter) rs ds imem req resp l1 l2 instruction remaining
          Hw ltac:(cbn [instr_in_bounds]; lia)
          ltac:(rewrite Z_to_bv_small by (unfold bv_modulus; lia); reflexivity)) as Hstep;
        cbn [exec_instr exec_instr2 Nat.add] in Hstep;
        rewrite Hstep; clear Hstep
      end;
      cbn [exec_instr exec_instr2 apply_write];
      repeat first [rewrite read_write_reg_same by lia | rewrite read_write_reg_diff by lia];
      rewrite ?Hprev; try rewrite <- Hbit;
      repeat match goal with
      | |- context [fadd_bv n modulus ?a ?b] => let v := fresh "value" in set (v := fadd_bv n modulus a b)
      | |- context [fsub_bv n modulus ?a ?b] => let v := fresh "value" in set (v := fsub_bv n modulus a b)
      | |- context [fmul_bv n modulus ?a ?b] => let v := fresh "value" in set (v := fmul_bv n modulus a b)
      end;
      rewrite ?counter_increment by lia).
    cbn [run_ticks]; unfold point_regs; cbn [Regs pc Stage].
    repeat first [rewrite read_write_reg_same by lia | rewrite read_write_reg_diff by lia].
    repeat match goal with v := _ |- _ => match goal with |- context [v] => unfold v end end.
    repeat first [rewrite fadd_bv_correct by exact Hp |
                      rewrite fsub_bv_correct by exact Hp | rewrite fmul_bv_correct by exact Hp].
    unfold MontLadderCSwap_step, ladder_math.CSwap, LadderStep, fsq, fadd, fsub, fmul, bit_i.
    rewrite <- Hbit. destruct current, previous.
    all: rewrite ?bv_xor_unsigned, ?Z_to_bv_small by (unfold bv_modulus; cbn [Z.b2z]; lia).
    all: cbn [Z.b2z Z.lxor Z.eqb Pos.eqb]; repeat split; reflexivity.
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
    let '(((_, _), val2), dval2) := s.(bookkeepingState2) in
    ( HW_bv s.(pc)
    + hw_regs
    + hw_dregs
    + hw_imem
    + HW_bv (snd s.(toiMem))
    + HW_bv (snd s.(fromiMem))
    + HW_bv val
    + HW_bv dval + HW_bv val2 + HW_bv dval2)%nat.

  Definition total_HW_observable (s : state) : nat :=
    state_HW s.

  Definition protected_HW (s : state) : nat :=
    let '(((_, _), val), dval) := s.(bookkeepingState) in
    let '(((_, _), val2), dval2) := s.(bookkeepingState2) in
    (Vector.fold_left (fun acc v => acc + HW_bv v)%nat 0%nat s.(Regs) +
     Vector.fold_left (fun acc v => acc + HW_bv v)%nat 0%nat s.(DRegs) +
     HW_bv val + HW_bv dval + HW_bv val2 + HW_bv dval2)%nat.

  (* Public bitvector fields contributing to the HW observation. *)
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

  (* The 32 register pairs and two execution-latch pairs each contribute n bits. *)
  Theorem protected_HW_constant s : valid_state s -> protected_HW s = (34 * N.to_nat n)%nat.
  Proof.
    intro Hvalid. pose proof (valid_state_duals s Hvalid) as Hduals.
    destruct Hvalid as [_ [Hlatch Hlatch2]]. unfold protected_HW. rewrite Hduals.
    destruct (bookkeepingState s) as [[[active rd] value] dual]. cbn in Hlatch. subst dual.
    destruct (bookkeepingState2 s) as [[[active2 rd2] value2] dual2]. cbn in Hlatch2. subst dual2.
    pose proof (hw_complement n value2) as Hpair2.
    change (HW_bv value2 + HW_bv (bv_not value2) = N.to_nat n)%nat in Hpair2.
    pose proof (vector_pair_HW (Regs s) 0%nat 0%nat) as Hregs.
    pose proof (hw_complement n value) as Hpair.
    change (HW_bv value + HW_bv (bv_not value) = N.to_nat n)%nat in Hpair. lia.
  Qed.

  Corollary run_ticks_protected_HW s cycles :
    valid_state s -> protected_HW (run_ticks s cycles) = (34 * N.to_nat n)%nat.
  Proof. intro Hvalid. apply protected_HW_constant, run_ticks_preserves_valid, Hvalid. Qed.

  Lemma state_HW_decomposition s : valid_state s -> state_HW s = (public_HW s + 34 * N.to_nat n)%nat.
  Proof.
    intro Hvalid. pose proof (protected_HW_constant s Hvalid) as Hprotected.
    unfold state_HW, public_HW, protected_HW in *.
    destruct (bookkeepingState s) as [[[active rd] value] dual].
    destruct (bookkeepingState2 s) as [[[active2 rd2] value2] dual2]. lia.
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

  (* Initial-state specialization. *)
  Theorem power_independence imem regs1 regs2 :
    total_HW_observable (mk_processor_state imem regs1) =
    total_HW_observable (mk_processor_state imem regs2).
  Proof.
    unfold total_HW_observable. apply state_HW_public;
      try apply mk_processor_state_valid; reflexivity.
  Qed.


  Definition public_state (s : state) :=
    (s.(Stage), s.(pc), s.(InstrMem), s.(toiMem), s.(fromiMem)).

  Lemma tick_public s1 s2 :
    public_state s1 = public_state s2 -> public_state (tick s1) = public_state (tick s2).
  Proof.
    destruct s1 as [p r d m stage req resp l l2].
    destruct s2 as [p' r' d' m' stage' req' resp' l' l2'].
    unfold public_state. cbn. intro H. injection H as Hstage Hp Hm Hreq Hresp.
    subst stage' p' m' req' resp'.
    unfold tick. cbn [Stage]. destruct stage.
    - reflexivity.
    - unfold execute. cbn [fromiMem Regs]. destruct resp as [active word].
      destruct active; [|reflexivity]. destruct (decode_instr word) as [e|]; [|reflexivity].
      destruct (exec_instr r e) as [[we rd] v], (exec_instr2 r e) as [[we2 rd2] v2].
      destruct (exec_instr r' e) as [[we' rd'] v'], (exec_instr2 r' e) as [[we2' rd2'] v2'].
      reflexivity.
    - unfold writeback. cbn [bookkeepingState bookkeepingState2].
      destruct l as [[[we rd] v] dv], l2 as [[[we2 rd2] v2] dv2].
      destruct l' as [[[we' rd'] v'] dv'], l2' as [[[we2' rd2'] v2'] dv2'].
      reflexivity.
  Qed.

  Lemma tick_iMem_public s1 s2 :
    public_state s1 = public_state s2 -> public_state (tick_iMem s1) = public_state (tick_iMem s2).
  Proof.
    destruct s1 as [p r d m stage req resp l l2].
    destruct s2 as [p' r' d' m' stage' req' resp' l' l2'].
    unfold public_state. cbn. intro H. injection H as Hstage Hp Hm Hreq Hresp.
    subst stage' p' m' req' resp'.
    unfold tick_iMem. cbn [toiMem InstrMem].
    destruct req as [active addr]. destruct active; reflexivity.
  Qed.

  Lemma full_tick_public s1 s2 :
    public_state s1 = public_state s2 -> public_state (full_tick s1) = public_state (full_tick s2).
  Proof. intro H. apply tick_iMem_public, tick_public, H. Qed.

  Fixpoint hw_trace (s : state) (cycles : nat) : list nat :=
    state_HW s :: match cycles with
                 | O => []
                 | S rest => hw_trace (full_tick s) rest
                 end.

  Lemma hw_trace_length s cycles : length (hw_trace s cycles) = S cycles.
  Proof. revert s. induction cycles; intro s; cbn [hw_trace length]; auto. Qed.

  Theorem hw_trace_independent s1 s2 cycles :
    valid_state s1 -> valid_state s2 -> public_state s1 = public_state s2 ->
    hw_trace s1 cycles = hw_trace s2 cycles.
  Proof.
    revert s1 s2. induction cycles as [|cycles IH]; intros s1 s2 H1 H2 Hpub;
      assert (Hhw : state_HW s1 = state_HW s2) by
        (unfold public_state in Hpub; injection Hpub as Hstage Hp Hm Hreq Hresp;
         apply state_HW_public; try assumption; congruence).
    - cbn [hw_trace]. rewrite Hhw. reflexivity.
    - cbn [hw_trace]. rewrite Hhw. f_equal.
      apply IH; [apply full_tick_preserves_valid, H1 |
                 apply full_tick_preserves_valid, H2 | apply full_tick_public, Hpub].
  Qed.

  Corollary processor_trace_independent imem regs1 regs2 cycles :
    hw_trace (mk_processor_state imem regs1) cycles =
    hw_trace (mk_processor_state imem regs2) cycles.
  Proof.
    apply hw_trace_independent; try apply mk_processor_state_valid; reflexivity.
  Qed.
End StateMachine.
End StateMachine.
