From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import masked_arithmetic masked_bank masked_ladder.
From Masking Require Import arithmetic_bank_refresh arithmetic_shares.
From Stdlib Require Import ZArith Bits Vector Lia.

Module MaskedController.
Module M := MaskedArithmetic.
Module B := MaskedBank.
Module Core := M.Core.
Import fn type InterfaceExample.QStdlib.
Import (notations) eexpr expr.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* Scalar bits 0..254; xP 255; coordinates 256..259; prev/curr/swap 260..262;
   accumulator 263; the eighteen ladder intermediates 264..281. *)
Definition groups : nat := 282.
Definition Bank n := B.Bank n groups.
Definition Coins n := B.Coins n groups.
Definition Control := Pair (Bits 3) (Pair (Bits 8) (Bits 5)).
Definition State n := Pair Control (Bank n).
Definition Instruction := Pair (Bits 2) (Pair (Bits 9) (Pair (Bits 9) (Bits 9))).
Definition Randomness n := Pair (M.Masks (S n)) (Coins n).
Definition Load := Pair M.Word M.Word.
Definition Commands := Pair Bool (Pair Bool Load).
Definition Input n := Pair (State n) (Pair Commands (Randomness n)).
Definition PreparationInput n := Pair (State n) (Pair Commands (M.Masks (S n))).
Definition initial_state n : type.interp (State n) := type.default (State n).

(* Copy/add/subtract/multiply. Constants occupy read-only addresses 282 and 283. *)
Record micro := Micro { opcode : Z; lhs : Z; rhs : Z; destination : Z }.
Definition encode_instruction (i : micro) : type.interp Instruction :=
  (bits.of_Z 2 (opcode i), (bits.of_Z 9 (lhs i),
    (bits.of_Z 9 (rhs i), bits.of_Z 9 (destination i)))).

Definition swap_program (b left right : Z) : list micro :=
  [:: Micro 2 right left 264; Micro 3 b 264 265;
      Micro 1 left 265 left; Micro 2 right 265 right].

Definition ladder_program : list micro :=
  [:: Micro 1 256 257 264; Micro 2 256 257 265;
      Micro 1 258 259 266; Micro 2 258 259 267;
      Micro 3 264 264 268; Micro 3 265 265 269;
      Micro 3 264 267 270; Micro 3 265 266 271;
      Micro 1 270 271 272; Micro 2 270 271 273;
      Micro 3 272 272 274; Micro 3 273 273 275;
      Micro 3 275 255 276; Micro 3 268 269 277;
      Micro 2 268 269 278; Micro 3 283 278 279;
      Micro 1 269 279 280; Micro 3 278 280 281].

Definition bit_program : list micro :=
  [:: Micro 0 0 0 261; Micro 3 260 261 264; Micro 1 260 261 265;
      Micro 1 264 264 264; Micro 2 265 264 262] ++
  swap_program 262 256 258 ++ swap_program 262 257 259 ++ ladder_program.
Definition final_program := swap_program 260 256 258 ++ swap_program 260 257 259.

Fixpoint lookup_program {var} (pc : Z) (code : list micro) :
    fn var (Bits 5) Instruction :=
  match code with
  | List.nil => Fn (fun _ => quartz_eexpr:(
      return $(expr.Const (t := Instruction) (encode_instruction (Micro 0 0 0 0)))))
  | i :: rest => Fn (fun p => quartz_eexpr:(
      let tail := {lookup_program (pc + 1) rest} (#p) in
      if #p == $(expr.Const (t := Bits 5) (bits.of_Z 5 pc)) then
        return $(expr.Const (t := Instruction) (encode_instruction i))
      else return #tail))
  end.

Definition anchor {var} n : fn var M.Word (M.Shares (S n)) :=
  Fn (fun w => quartz_eexpr:(
    let a := $(expr.Const (t := M.Shares (S n)) (type.default (M.Shares (S n)))) in
    let a <- #a[(1 'd 0)] = #w in return #a)).

Definition read_operand {var} n : fn var (Pair (Bank n) (Bits 9)) (M.Shares (S n)) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let i := #p .2 in
    let one := {anchor n} ((255 'd 1)) in
    let a24 := {anchor n} ((255 'd 121666)) in
    if #i == (9 'd 282) then return #one else
    if #i == (9 'd 283) then return #a24 else return #a[#i])).

Definition execute {var} n :
    fn var (Pair Instruction (Pair (Bank n) (M.Masks (S n)))) (Bank n) :=
  Fn (fun p => quartz_eexpr:(
    let ins := #p .1 in let bank := #p .2 .1 in let masks := #p .2 .2 in
    let a := {read_operand n} ((#bank,#ins .2 .1)) in
    let b := {read_operand n} ((#bank,#ins .2 .2 .1)) in
    let sum := {M.share_map Core.Add (S n)} ((#a,#b)) in
    let difference := {M.share_map Core.Sub (S n)} ((#a,#b)) in
    let product := {M.multiply (S n)} ((#a,(#b,#masks))) in
    let value := if #ins .1 == (2 'd 0) then #a else
      if #ins .1 == (2 'd 1) then #sum else
      if #ins .1 == (2 'd 2) then #difference else #product in
    let bank <- #bank[#ins .2 .2 .2] = #value in return #bank)).

(* Idle=0, bit=1, final swaps=2, square=3, multiply=4, finish=5, done=6. *)
Definition decode {var} : fn var Control Instruction :=
  Fn (fun c => quartz_eexpr:(
    let phase := #c .1 in let index := #c .2 .1 in let pc := #c .2 .2 in
    let bit_ins := {lookup_program 0 bit_program} (#pc) in
    let final_ins := {lookup_program 0 final_program} (#pc) in
    let exponent := $(expr.Const (t := Bits 255) (bits.of_Z 255 (Core.prime - 2))) in
    let shifted := #exponent >> $(expr.Unop (@unop.UnsignedResize 8 255) (expr.Var index)) in
    let exponent_bit := $(expr.Unop (unop.Slice 0 1) (expr.Var shifted)) in
    let factor := if #exponent_bit then (9 'd 257) else (9 'd 282) in
    if #phase == (3 'd 1) then
      if #pc == (5 'd 0) then
        return ((2 'd 0), ($(expr.Unop (@unop.UnsignedResize 8 9) (expr.Var index)),
          ((9 'd 0),(9 'd 261))))
      else return #bit_ins
    else if #phase == (3 'd 2) then return #final_ins
    else if #phase == (3 'd 3) then return ((2 'd 3),((9 'd 263),((9 'd 263),(9 'd 263))))
    else if #phase == (3 'd 4) then return ((2 'd 3),((9 'd 263),(#factor,(9 'd 263))))
    else return ((2 'd 3),((9 'd 256),((9 'd 263),(9 'd 263)))))).

Definition advance {var} : fn var Control Control :=
  Fn (fun c => quartz_eexpr:(
    let phase := #c .1 in let index := #c .2 .1 in let pc := #c .2 .2 in
    if #phase == (3 'd 1) then
      if #pc == (5 'd 31) then
        if #index == (8 'd 0) then return ((3 'd 2),(#index,(5 'd 0)))
        else return (#phase,(#index - (8 'd 1),(5 'd 0)))
      else return (#phase,(#index,#pc + (5 'd 1)))
    else if #phase == (3 'd 2) then
      if #pc == (5 'd 7) then return ((3 'd 3),((8 'd 254),(5 'd 0)))
      else return (#phase,(#index,#pc + (5 'd 1)))
    else if #phase == (3 'd 3) then return ((3 'd 4),(#index,#pc))
    else if #phase == (3 'd 4) then
      if #index == (8 'd 0) then return ((3 'd 5),(#index,#pc))
      else return ((3 'd 3),(#index - (8 'd 1),#pc))
    else if #phase == (3 'd 5) then return ((3 'd 6),(#index,#pc))
    else return #c)).

(* Multiwrite COPY edge. Reads all five sources before writing any destination. *)
Definition collect {var} n : fn var (Bank n) (Bank n) :=
  Fn (fun bank => quartz_eexpr:(
    let xd := #bank[(9 'd 277)] in let zd := #bank[(9 'd 281)] in
    let xa := #bank[(9 'd 274)] in let za := #bank[(9 'd 276)] in
    let curr := #bank[(9 'd 261)] in
    let bank <- #bank[(9 'd 256)] = #xd in let bank <- #bank[(9 'd 257)] = #zd in
    let bank <- #bank[(9 'd 258)] = #xa in let bank <- #bank[(9 'd 259)] = #za in
    let bank <- #bank[(9 'd 260)] = #curr in return #bank)).

Fixpoint load_bits {var} n (positions : list nat) :
    fn var (Pair M.Word (Bank n)) (Bank n) :=
  match positions with
  | List.nil => Fn (fun p => quartz_eexpr:(return #p .2))
  | i :: rest => Fn (fun p => quartz_eexpr:(
      let raw := #p .1 in let bank := #p .2 in
      let bit := $(expr.Unop (unop.Slice (Z.of_nat i) 1) (expr.Var raw)) in
      let word := $(expr.Unop (@unop.UnsignedResize 1 255) (expr.Var bit)) in
      let shared := {anchor n} (#word) in
      let address := $(expr.Const (t := Bits 9) (bits.of_Z 9 (Z.of_nat i))) in
      let bank <- #bank[#address] = #shared in
      let bank := {load_bits n rest} ((#raw,#bank)) in return #bank))
  end.

Definition load_bank {var} n : fn var Load (Bank n) :=
  Fn (fun input => quartz_eexpr:(
    let zero := (255 'd 0) in
    let xP := {Core.arithmetic Core.Add} ((#input .1,#zero)) in
    let xP := {anchor n} (#xP) in let one := {anchor n} ((255 'd 1)) in
    let bank := $(expr.Const (t := Bank n) (type.default (Bank n))) in
    let bank := {load_bits n (iota 0 255)} ((#input .2,#bank)) in
    let bank <- #bank[(9 'd 255)] = #xP in let bank <- #bank[(9 'd 256)] = #one in
    let bank <- #bank[(9 'd 258)] = #xP in let bank <- #bank[(9 'd 259)] = #one in
    let bank <- #bank[(9 'd 263)] = #one in return #bank)).

Definition next_control {var} : fn var (Pair Control (Pair Bool Bool)) Control :=
  Fn (fun p => quartz_eexpr:(
    let c := #p .1 in let phase := #c .1 in
    if #p .2 .1 then return $(expr.Const (t := Control) (type.default Control))
    else if (#phase == (3 'd 0)) | (#phase == (3 'd 6)) then
      if #p .2 .2 then return ((3 'd 1),((8 'd 254),(5 'd 0))) else return #c
    else return advance (#c))).

Definition prepare_bank {var} n : fn var (PreparationInput n) (Bank n) :=
  Fn (fun p => quartz_eexpr:(
    let c := #p .1 .1 in let bank := #p .1 .2 in let phase := #c .1 in
    let command := #p .2 .1 in let masks := #p .2 .2 in
    if #command .1 then
      return $(expr.Const (t := Bank n) (type.default (Bank n)))
    else if (#phase == (3 'd 0)) | (#phase == (3 'd 6)) then
      if #command .2 .1 then
        let bank := {load_bank n} (#command .2 .2) in
        return #bank
      else return #bank
    else
      let ins := decode (#c) in
      let work := {execute n} ((#ins,(#bank,#masks))) in
      let collected := {collect n} (#bank) in
      if (#phase == (3 'd 1)) & (#c .2 .2 == (5 'd 31)) then return #collected
      else if #phase == (3 'd 7) then return #bank
      else return #work)).

Definition prepare {var} n : fn var (PreparationInput n) (State n) :=
  Fn (fun p => quartz_eexpr:(
    let c := next_control ((#p .1 .1,(#p .2 .1 .1,#p .2 .1 .2 .1))) in
    let bank := {prepare_bank n} (#p) in return (#c,#bank))).

(* The port supplies fresh independent canonical coins each observed clock, including
   reset/idle/done. There is no RNG state. Freshness is a distributional obligation. *)
Definition tick {var} n : fn var (Input n) (State n) :=
  Fn (fun p => quartz_eexpr:(
    let prepared := {prepare n} ((#p .1,(#p .2 .1,#p .2 .2 .1))) in
    let bank := {B.refresh n groups} ((#prepared .2,#p .2 .2 .2)) in
    return (#prepared .1,#bank))).

Definition ready {var} n : fn var (State n) Bool :=
  Fn (fun s => quartz_eexpr:(return #s .1 .1 == (3 'd 6))).
Definition output {var} n : fn var (State n) (M.Shares (S n)) :=
  Fn (fun s => quartz_eexpr:(let bank := #s .2 in return #bank[(9 'd 263)])).

Definition prepared n (p : type.interp (Input n)) :=
  fn.interp (prepare n) (p.1,(p.2.1,p.2.2.1)).

Local Opaque B.refresh prepare prepare_bank next_control.
Theorem tick_factorization n p :
  fn.interp (tick n) p =
  ((prepared n p).1, fn.interp (B.refresh n groups) ((prepared n p).2,p.2.2.2)).
Proof. reflexivity. Qed.

Theorem preparation_refresh_independent n state command masks coins coins' :
  prepared n (state,(command,(masks,coins))) = prepared n (state,(command,(masks,coins'))).
Proof. reflexivity. Qed.

Local Transparent prepare.
Theorem tick_public_control n p :
  (fn.interp (tick n) p).1 =
  fn.interp next_control (p.1.1,(p.2.1.1,p.2.1.2.1)).
Proof. reflexivity. Qed.
Local Opaque prepare.

Theorem tick_refresh_refines n p :
  B.decode n groups (fn.interp (tick n) p).2 =
  ArithmeticBankRefresh.refresh
    (B.decode n groups (prepared n p).2) (B.decode_coins n groups p.2.2.2).
Proof. rewrite tick_factorization /=. exact: B.refresh_refines. Qed.

Theorem tick_canonical n p :
  B.canonical n groups (prepared n p).2 ->
  B.canonical n groups (fn.interp (tick n) p).2.
Proof. rewrite tick_factorization /=. exact: B.refresh_canonical. Qed.

Theorem tick_reconstruct n p (i : 'I_groups) :
  ArithmeticShares.reconstruct
    (M.decode (S n) (@M.read (M.Shares (S n)) groups (fn.interp (tick n) p).2 (val i))) =
  ArithmeticShares.reconstruct
    (M.decode (S n) (@M.read (M.Shares (S n)) groups (prepared n p).2 (val i))).
Proof. rewrite tick_factorization /= B.refresh_read. exact: M.refresh_correct. Qed.

Definition scheduled_edges : nat := (1 + 255 * 32 + 8 + 255 * 2 + 1)%nat.
Definition retained_secret_bits n : nat := (groups * (S n) * 255)%nat.
Definition retained_public_bits : nat := (3 + 8 + 5)%nat.
Definition randomness_port_bits n : nat := (255 * ((S n) * (S n) + groups * n))%nat.

Lemma schedule_sizes : List.length bit_program = 31%nat /\ List.length final_program = 8%nat.
Proof. split; reflexivity. Qed.
Lemma scheduled_edges_value : scheduled_edges = 8680%nat.
Proof. reflexivity. Qed.
Lemma retained_secret_bits_value n : retained_secret_bits n = (71910 * S n)%nat.
Proof. by rewrite /retained_secret_bits /groups mulnAC. Qed.

Lemma read_default t k i :
  @M.read t k (type.default (Array t k)) i = type.default t.
Proof. revert i. induction k; intros [|i]; simpl; try reflexivity. exact (IHk i). Qed.

Lemma read_outside t k (a : Vector.t (type.interp t) k) i :
  Nat.le k i -> @M.read t k a i = type.default t.
Proof.
  revert i. induction a; intros [|i] Hi; simpl; try reflexivity; try lia.
  apply IHa. lia.
Qed.

Lemma default_shares_canonical k : M.canonical k (type.default (M.Shares k)).
Proof.
  intro i. rewrite read_default. change (0 <= 0 < Core.prime).
  split; [lia | exact M.AC.prime_positive].
Qed.

Lemma default_bank_canonical n : B.canonical n groups (type.default (Bank n)).
Proof. intro i. rewrite read_default. exact: default_shares_canonical. Qed.

Lemma bank_read_canonical n (a : type.interp (Bank n)) i :
  B.canonical n groups a -> M.canonical (S n) (@M.read (M.Shares (S n)) groups a i).
Proof.
  intro Ha. destruct (Compare_dec.lt_dec i groups) as [Hi|Hi].
  - have Hi' : is_true (ltn i groups) by apply/ltP.
    exact (Ha (Ordinal Hi')).
  - rewrite read_outside; [lia | exact: default_shares_canonical].
Qed.

Lemma bank_update_canonical n (a : type.interp (Bank n)) i x :
  B.canonical n groups a -> M.canonical (S n) x ->
  B.canonical n groups (domain.Vector.upd a i (fun _ => x)).
Proof.
  move=> Ha Hx j. rewrite (M.read_upd _ _ _ _ (elimT ltP (ltn_ord j))).
  case: (Nat.eqb (val j) i); [exact Hx | exact (Ha j)].
Qed.

Lemma anchor_interp n w : fn.interp (anchor n) w =
  domain.Vector.upd (type.default (M.Shares (S n))) 0 (fun _ => w).
Proof. reflexivity. Qed.

Lemma anchor_canonical n w :
  0 <= Zmod.unsigned w < Core.prime -> M.canonical (S n) (fn.interp (anchor n) w).
Proof.
  move=> Hw i. rewrite anchor_interp (M.read_upd _ _ _ _ (elimT ltP (ltn_ord i))).
  case: (Nat.eqb (val i) 0); [exact Hw | exact (default_shares_canonical (S n) i)].
Qed.

Theorem initial_canonical n : B.canonical n groups (initial_state n).2.
Proof. exact: default_bank_canonical. Qed.

Definition equal_bits {w} (x y : bits w) := Zmod.nonzero (Zmod.embed_bool (Zmod.eqb x y)).

Lemma read_operand_interp n a i : fn.interp (read_operand n) (a,i) =
  if equal_bits i (bits.of_Z 9 282) then fn.interp (anchor n) (bits.of_Z 255 1) else
  if equal_bits i (bits.of_Z 9 283) then fn.interp (anchor n) (bits.of_Z 255 121666) else
  @M.read (M.Shares (S n)) groups a (Z.to_nat (Zmod.unsigned i)).
Proof. reflexivity. Qed.

Lemma read_operand_canonical n a i : B.canonical n groups a ->
  M.canonical (S n) (fn.interp (read_operand n) (a,i)).
Proof.
  intro Ha. rewrite read_operand_interp.
  case: (equal_bits i (bits.of_Z 9 282)).
  - apply anchor_canonical. vm_compute. split; congruence.
  - case: (equal_bits i (bits.of_Z 9 283)).
    + apply anchor_canonical. vm_compute. split; congruence.
    + exact: bank_read_canonical.
Qed.

Local Opaque M.share_map M.multiply read_operand anchor.
Lemma execute_interp n ins a masks :
  fn.interp (execute n) (ins,(a,masks)) =
  let x := fn.interp (read_operand n) (a,ins.2.1) in
  let y := fn.interp (read_operand n) (a,ins.2.2.1) in
  domain.Vector.upd a (Z.to_nat (Zmod.unsigned ins.2.2.2)) (fun _ =>
    if equal_bits ins.1 (bits.of_Z 2 0) then x else
    if equal_bits ins.1 (bits.of_Z 2 1) then fn.interp (M.share_map Core.Add (S n)) (x,y) else
    if equal_bits ins.1 (bits.of_Z 2 2) then fn.interp (M.share_map Core.Sub (S n)) (x,y) else
    fn.interp (M.multiply (S n)) (x,(y,masks))).
Proof. reflexivity. Qed.

Theorem execute_canonical n ins a masks : B.canonical n groups a ->
  B.canonical n groups (fn.interp (execute n) (ins,(a,masks))).
Proof.
  intro Ha. rewrite execute_interp. apply bank_update_canonical; [exact Ha|].
  case: (equal_bits ins.1 (bits.of_Z 2 0)); [exact: read_operand_canonical|].
  case: (equal_bits ins.1 (bits.of_Z 2 1)); [exact: M.share_map_canonical|].
  case: (equal_bits ins.1 (bits.of_Z 2 2)); [exact: M.share_map_canonical|].
  exact: M.multiply_canonical.
Qed.

Lemma collect_interp n a : fn.interp (collect n) a =
  let get i := @M.read (M.Shares (S n)) groups a i in
  let b := domain.Vector.upd a 256 (fun _ => get 277%nat) in
  let b := domain.Vector.upd b 257 (fun _ => get 281%nat) in
  let b := domain.Vector.upd b 258 (fun _ => get 274%nat) in
  let b := domain.Vector.upd b 259 (fun _ => get 276%nat) in
  domain.Vector.upd b 260 (fun _ => get 261%nat).
Proof. reflexivity. Qed.

Theorem collect_canonical n a : B.canonical n groups a ->
  B.canonical n groups (fn.interp (collect n) a).
Proof.
  intro Ha. rewrite collect_interp.
  apply bank_update_canonical; last exact: bank_read_canonical.
  apply bank_update_canonical; last exact: bank_read_canonical.
  apply bank_update_canonical; last exact: bank_read_canonical.
  apply bank_update_canonical; last exact: bank_read_canonical.
  apply bank_update_canonical; [exact Ha | exact: bank_read_canonical].
Qed.

Lemma bit_word_canonical (b : bits 1) :
  0 <= Zmod.unsigned (bits.of_Z 255 (Zmod.unsigned b)) < Core.prime.
Proof.
  have Hb := bits.unsigned_range b ltac:(lia).
  rewrite bits.unsigned_of_Z_small; unfold Core.prime; cbn in *; lia.
Qed.

Lemma load_bits_cons_interp n i rest raw a :
  fn.interp (load_bits n (i :: rest)) (raw,a) =
  fn.interp (load_bits n rest)
    (raw,domain.Vector.upd a
      (Z.to_nat (Zmod.unsigned (bits.of_Z 9 (Z.of_nat i))))
      (fun _ => fn.interp (anchor n)
        (bits.of_Z 255 (Zmod.unsigned (unop.interp (unop.Slice (Z.of_nat i) 1) raw))))).
Proof. reflexivity. Qed.

Lemma load_bits_canonical n positions raw a :
  B.canonical n groups a -> B.canonical n groups (fn.interp (load_bits n positions) (raw,a)).
Proof.
  revert a. induction positions as [|i rest IH]; intros a Ha; [exact Ha|].
  rewrite load_bits_cons_interp. apply IH. apply bank_update_canonical; [exact Ha|].
  apply anchor_canonical. exact: bit_word_canonical.
Qed.

Local Opaque Core.arithmetic load_bits.
Lemma load_bank_interp n input : fn.interp (load_bank n) input =
  let xP := fn.interp (anchor n)
    (fn.interp (Core.arithmetic Core.Add) (input.1,bits.of_Z 255 0)) in
  let one := fn.interp (anchor n) (bits.of_Z 255 1) in
  let a := fn.interp (load_bits n (iota 0 255)) (input.2,type.default (Bank n)) in
  let a := domain.Vector.upd a 255 (fun _ => xP) in
  let a := domain.Vector.upd a 256 (fun _ => one) in
  let a := domain.Vector.upd a 258 (fun _ => xP) in
  let a := domain.Vector.upd a 259 (fun _ => one) in
  domain.Vector.upd a 263 (fun _ => one).
Proof. reflexivity. Qed.

Theorem load_bank_canonical n input : B.canonical n groups (fn.interp (load_bank n) input).
Proof.
  have Hone : M.canonical (S n) (fn.interp (anchor n) (bits.of_Z 255 1)).
  { apply anchor_canonical. vm_compute. split; congruence. }
  have HxP : M.canonical (S n) (fn.interp (anchor n)
      (fn.interp (Core.arithmetic Core.Add) (input.1,bits.of_Z 255 0))).
  { apply anchor_canonical. exact: M.AC.arithmetic_canonical. }
  rewrite load_bank_interp.
  apply bank_update_canonical; last exact Hone.
  apply bank_update_canonical; last exact Hone.
  apply bank_update_canonical; last exact HxP.
  apply bank_update_canonical; last exact Hone.
  apply bank_update_canonical; last exact HxP.
  apply load_bits_canonical. exact: default_bank_canonical.
Qed.

Local Opaque load_bank execute collect decode.
Local Transparent prepare_bank.
Theorem prepare_bank_canonical n p : B.canonical n groups p.1.2 ->
  B.canonical n groups (fn.interp (prepare_bank n) p).
Proof.
  intro Ha.
  cbn [prepare_bank fn.interp fn.body fn.eexpr_map_fn fn.expr_map_fn
    eexpr.interp eexpr.LetBlock expr.interp binop.interp typeWithHole.get].
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    first [exact Ha | exact (default_bank_canonical n) |
      exact (load_bank_canonical n p.2.1.2.2) |
      exact (collect_canonical n p.1.2 Ha) |
      exact (execute_canonical n (fn.interp decode p.1.1) p.1.2 p.2.2 Ha)].
Qed.
Local Opaque prepare_bank.

Local Transparent prepare.
Theorem tick_preserves_canonical n p : B.canonical n groups p.1.2 ->
  B.canonical n groups (fn.interp (tick n) p).2.
Proof.
  intro Ha. apply tick_canonical.
  change (B.canonical n groups (fn.interp (prepare_bank n) (p.1,(p.2.1,p.2.2.1)))).
  exact: prepare_bank_canonical.
Qed.
Local Opaque prepare.

Definition reconstruct_group n (a : type.interp (M.Shares (S n))) :=
  ArithmeticShares.reconstruct (M.decode (S n) a).

Definition clear_instruction n (ins : type.interp Instruction) (a : type.interp (Bank n)) :=
  let x := reconstruct_group n (fn.interp (read_operand n) (a,ins.2.1)) in
  let y := reconstruct_group n (fn.interp (read_operand n) (a,ins.2.2.1)) in
  if equal_bits ins.1 (bits.of_Z 2 0) then x else
  if equal_bits ins.1 (bits.of_Z 2 1) then (x + y)%R else
  if equal_bits ins.1 (bits.of_Z 2 2) then (x - y)%R else (x * y)%R.

Theorem execute_reconstruct n ins a masks (j : 'I_groups) :
  reconstruct_group n
    (@M.read (M.Shares (S n)) groups (fn.interp (execute n) (ins,(a,masks))) (val j)) =
  if Nat.eqb (val j) (Z.to_nat (Zmod.unsigned ins.2.2.2)) then clear_instruction n ins a
  else reconstruct_group n (@M.read (M.Shares (S n)) groups a (val j)).
Proof.
  rewrite execute_interp (M.read_upd _ _ _ _ (elimT ltP (ltn_ord j))).
  case: (Nat.eqb (val j) (Z.to_nat (Zmod.unsigned ins.2.2.2))); [|reflexivity].
  rewrite /clear_instruction /reconstruct_group.
  case: (equal_bits ins.1 (bits.of_Z 2 0)); [reflexivity|].
  case: (equal_bits ins.1 (bits.of_Z 2 1)).
  - by rewrite M.add_refines ArithmeticShares.add_correct.
  - case: (equal_bits ins.1 (bits.of_Z 2 2)).
    + by rewrite M.sub_refines ArithmeticShares.sub_correct.
    + exact: M.multiply_correct.
Qed.

End MaskedController.
Print Assumptions MaskedController.tick_refresh_refines.
Print Assumptions MaskedController.tick_canonical.
Print Assumptions MaskedController.tick_reconstruct.
Print Assumptions MaskedController.preparation_refresh_independent.
Print Assumptions MaskedController.tick_public_control.
Print Assumptions MaskedController.initial_canonical.
Print Assumptions MaskedController.execute_canonical.
Print Assumptions MaskedController.collect_canonical.
Print Assumptions MaskedController.tick_preserves_canonical.
Print Assumptions MaskedController.execute_reconstruct.
