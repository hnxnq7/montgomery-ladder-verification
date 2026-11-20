From HB Require Import structures.
From mathcomp Require Import boot order algebra reals.
From quartz.lang Require Import domain Syntax.
From quartz.examples Require Import Processor.
From LadderQuartz Require Import accelerator accelerator_correctness.
From Masking Require Import fiat_field arithmetic_shares arithmetic_refresh.
From Stdlib Require Import ZArith Bits Lia Vector.

(* Combinational sharing primitives. Coins are explicit inputs; no registers or RNG are introduced. *)
Module MaskedArithmetic.
Module Core := LadderAccelerator.
Module AC := AcceleratorCorrectness.
Import fn type InterfaceExample.QStdlib.
Import (coercions) domain.Zmod.
Import (notations) eexpr expr.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition Word := Bits 255.
Definition Shares (k : nat) := Array Word k.
Definition index_width (k : nat) := Z.max 1 (Z.log2_up (Z.of_nat k)).
Definition index_bits k (i : 'I_k) := bits.of_Z (index_width k) (Z.of_nat (val i)).
Definition decode_word (w : bits 255) : FiatField.curve25519 :=
  FiatField.encode FiatField.curve25519_modulus_gt1 (Zmod.unsigned w).

Definition field_operation op (a b : FiatField.curve25519) :=
  match op with Core.Add => (a + b)%R | Core.Sub => (a - b)%R | Core.Mul => (a * b)%R end.

Lemma decode_arithmetic op a b :
  decode_word (fn.interp (Core.arithmetic op) (a,b)) =
  field_operation op (decode_word a) (decode_word b).
Proof.
  unfold decode_word. rewrite AC.arithmetic_correct.
  unfold AC.field_operation, field_operation.
  change Core.prime with (Z.pos FiatField.curve25519_modulus).
  rewrite FiatField.encode_mod.
  destruct op; [apply FiatField.encode_add | apply FiatField.encode_sub | apply FiatField.encode_mul].
Qed.

Lemma index_unsigned k (i : 'I_k) : Zmod.unsigned (index_bits k i) = Z.of_nat (val i).
Proof.
  have Hi : Nat.lt (val i) k := elimT ltP (ltn_ord i).
  have Hk : (0 < Z.of_nat k)%Z by lia.
  have Hp : Z.of_nat k <= 2 ^ index_width k.
  { apply (proj2 (Z.log2_up_le_pow2 _ _ Hk)). unfold index_width. apply Z.le_max_r. }
  unfold index_bits. apply bits.unsigned_of_Z_small. lia.
Qed.

Definition read {t k} (a : Vector.t (type.interp t) k) (i : nat) : type.interp t :=
  List.nth_default (type.default t) (Vector.to_list a) i.

Definition decode k (a : Vector.t (bits 255) k) : ArithmeticShares.shares FiatField.curve25519 k :=
  [ffun i : 'I_k => decode_word (@read Word k a (val i))].

Definition get {var} k (i : 'I_k) : fn var (Shares k) Word :=
  Fn (fun a => quartz_eexpr:(
    let i := $(expr.Const (t := Bits (index_width k)) (index_bits k i)) in
    return #a[#i])).

Definition put {var} k (i : 'I_k) : fn var (Pair (Shares k) Word) (Shares k) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in
    let i := $(expr.Const (t := Bits (index_width k)) (index_bits k i)) in
    let a <- #a[#i] = #p .2 in
    return #a)).

Lemma get_interp k (i : 'I_k) a : fn.interp (get k i) a = @read Word k a (val i).
Proof.
  change (@read Word k a (Z.to_nat (Zmod.unsigned (index_bits k i))) = @read Word k a (val i)).
  rewrite index_unsigned Nat2Z.id. reflexivity.
Qed.

Lemma put_interp k (i : 'I_k) a w :
  fn.interp (put k i) (a,w) = domain.Vector.upd a (val i) (fun _ => w).
Proof.
  change (domain.Vector.upd a (Z.to_nat (Zmod.unsigned (index_bits k i))) (fun _ => w) =
    domain.Vector.upd a (val i) (fun _ => w)).
  rewrite index_unsigned Nat2Z.id. reflexivity.
Qed.

Lemma read_upd {t k} (a : Vector.t (type.interp t) k) i j w :
  Nat.lt j k ->
  @read t k (domain.Vector.upd a i (fun _ => w)) j =
  if Nat.eqb j i then w else @read t k a j.
Proof.
  revert i j. induction a as [|x k a IH]; intros i j Hj; [lia|].
  destruct i, j; simpl in *; try reflexivity.
  apply IH. lia.
Qed.

Local Opaque Core.arithmetic get put.

(* The source arrays stay immutable throughout the generated straight-line map. *)
Fixpoint map_steps {var} op k (indices : seq 'I_k) :
    fn var (Pair (Shares k) (Pair (Shares k) (Shares k))) (Shares k) :=
  match indices with
  | List.nil => Fn (fun p => quartz_eexpr:(return #p .2 .2))
  | i :: rest => Fn (fun p => quartz_eexpr:(
      let a := #p .1 in let b := #p .2 .1 in let c := #p .2 .2 in
      let x := {get k i} (#a) in let y := {get k i} (#b) in
      let w := {Core.arithmetic op} ((#x, #y)) in
      let c := {put k i} ((#c, #w)) in
      let result := {map_steps op k rest} ((#a, (#b, #c))) in
      return #result))
  end.

Definition share_map {var} op k : fn var (Pair (Shares k) (Shares k)) (Shares k) :=
  Fn (fun p => quartz_eexpr:(
    let c := $(expr.Const (t := Shares k) (type.default (Shares k))) in
    let result := {map_steps op k (enum 'I_k)} ((#p .1, (#p .2, #c))) in
    return #result)).

Lemma map_steps_interp op k indices a b c :
  fn.interp (map_steps op k indices) (a,(b,c)) =
  foldl (fun acc i => domain.Vector.upd acc (val i)
    (fun _ => fn.interp (Core.arithmetic op) (@read Word k a (val i), @read Word k b (val i))))
    c indices.
Proof.
  revert c. induction indices as [|i rest IH]; intro c; [reflexivity|].
  change (fn.interp (map_steps op k rest)
    (a,(b,fn.interp (put k i) (c,fn.interp (Core.arithmetic op)
      (fn.interp (get k i) a,fn.interp (get k i) b)))) =
    foldl (fun acc j => domain.Vector.upd acc (val j)
      (fun _ => fn.interp (Core.arithmetic op) (@read Word k a (val j), @read Word k b (val j))))
      c (i :: rest)).
  rewrite !get_interp put_interp. apply IH.
Qed.

Lemma map_steps_read op k indices a b c (j : 'I_k) :
  @read Word k (fn.interp (map_steps op k indices) (a,(b,c))) (val j) =
  if j \in indices then fn.interp (Core.arithmetic op)
    (@read Word k a (val j), @read Word k b (val j)) else @read Word k c (val j).
Proof.
  rewrite map_steps_interp. revert c.
  induction indices as [|i rest IH]; intro c; [reflexivity|].
  simpl foldl. rewrite IH in_cons.
  case Hrest: (j \in rest); simpl; [by rewrite orbT|].
  have Hj : Nat.lt (val j) k := elimT ltP (ltn_ord j).
  rewrite orbF (read_upd _ _ _ _ Hj).
  case E: (j == i).
  - move/eqP: E => ->. rewrite Nat.eqb_refl. reflexivity.
  - have Hneq : Nat.eqb (val j) (val i) = false.
    { apply Nat.eqb_neq. intro H. have Hij : j = i := val_inj H.
      subst i. rewrite eqxx in E. discriminate. }
    rewrite Hneq. reflexivity.
Qed.

Lemma share_map_refines op k a b :
  decode k (fn.interp (share_map op k) (a,b)) =
  [ffun i => field_operation op (decode k a i) (decode k b i)].
Proof.
  apply/ffunP => i. rewrite !ffunE.
  change (decode_word (@read Word k
    (fn.interp (map_steps op k (enum 'I_k)) (a,(b,type.default (Shares k)))) (val i)) =
    field_operation op (decode_word (@read Word k a (val i))) (decode_word (@read Word k b (val i)))).
  rewrite map_steps_read mem_enum. apply decode_arithmetic.
Qed.

Corollary add_refines k a b :
  decode k (fn.interp (share_map Core.Add k) (a,b)) = ArithmeticShares.add (decode k a) (decode k b).
Proof. exact (share_map_refines Core.Add k a b). Qed.

Corollary sub_refines k a b :
  decode k (fn.interp (share_map Core.Sub k) (a,b)) = ArithmeticShares.sub (decode k a) (decode k b).
Proof. exact (share_map_refines Core.Sub k a b). Qed.

(* Mapping Mul is the diagonal initialization, not multiplication of shared values. *)
Corollary diagonal_refines k a b :
  decode k (fn.interp (share_map Core.Mul k) (a,b)) = ArithmeticShares.diagonal (decode k a) (decode k b).
Proof. exact (share_map_refines Core.Mul k a b). Qed.

Definition canonical k (a : Vector.t (bits 255) k) :=
  forall i : 'I_k, 0 <= Zmod.unsigned (@read Word k a (val i)) < Core.prime.

Lemma share_map_canonical op k a b : canonical k (fn.interp (share_map op k) (a,b)).
Proof.
  intro i. change (0 <= Zmod.unsigned (@read Word k
    (fn.interp (map_steps op k (enum 'I_k)) (a,(b,type.default (Shares k)))) (val i)) < Core.prime).
  rewrite map_steps_read mem_enum. apply AC.arithmetic_canonical.
Qed.

Definition PairInput k := Pair (Shares k) (Pair (Shares k) (Pair (Shares k) Word)).

Definition pair_update {var} k (i j : 'I_k) : fn var (PairInput k) (Shares k) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let b := #p .2 .1 in
    let c := #p .2 .2 .1 in let r := #p .2 .2 .2 in
    let ai := {get k i} (#a) in let aj := {get k j} (#a) in
    let bi := {get k i} (#b) in let bj := {get k j} (#b) in
    let u := {Core.arithmetic Core.Mul} ((#ai,#bj)) in
    let v := {Core.arithmetic Core.Mul} ((#aj,#bi)) in
    let cross := {Core.arithmetic Core.Add} ((#u,#v)) in
    let masked := {Core.arithmetic Core.Add} ((#r,#cross)) in
    let ci := {get k i} (#c) in
    let ci := {Core.arithmetic Core.Sub} ((#ci,#r)) in
    let c := {put k i} ((#c,#ci)) in
    let cj := {get k j} (#c) in
    let cj := {Core.arithmetic Core.Add} ((#cj,#masked)) in
    let c := {put k j} ((#c,#cj)) in
    return #c)).

(* Reading the second accumulator entry after the first write matches the reference exactly. *)
Lemma decode_put k (i : 'I_k) a w (j : 'I_k) :
  decode k (fn.interp (put k i) (a,w)) j =
  if j == i then decode_word w else decode k a j.
Proof.
  have Hj : Nat.lt (val j) k := elimT ltP (ltn_ord j).
  rewrite /decode !ffunE put_interp (read_upd _ _ _ _ Hj).
  case E: (j == i).
  - move/eqP: E => ->. by rewrite Nat.eqb_refl.
  - have Hneq : Nat.eqb (val j) (val i) = false.
    { apply Nat.eqb_neq. intro H. have Hij : j = i := val_inj H.
      subst i. rewrite eqxx in E. discriminate. }
    by rewrite Hneq.
Qed.

Lemma decode_increment k (i : 'I_k) a w :
  decode k (fn.interp (put k i) (a,fn.interp (Core.arithmetic Core.Add) (fn.interp (get k i) a,w))) =
  ArithmeticShares.increment (decode k a) i (decode_word w).
Proof.
  apply/ffunP => j. rewrite decode_put /ArithmeticShares.increment !ffunE.
  case E: (j == i).
  - move/eqP: E => ->. rewrite decode_arithmetic get_interp. reflexivity.
  - by rewrite GRing.addr0.
Qed.

Lemma decode_decrement k (i : 'I_k) a w :
  decode k (fn.interp (put k i) (a,fn.interp (Core.arithmetic Core.Sub) (fn.interp (get k i) a,w))) =
  ArithmeticShares.increment (decode k a) i (- decode_word w)%R.
Proof.
  apply/ffunP => j. rewrite decode_put /ArithmeticShares.increment !ffunE.
  case E: (j == i).
  - move/eqP: E => ->. rewrite decode_arithmetic get_interp. reflexivity.
  - by rewrite GRing.addr0.
Qed.

Definition pair_result k (i j : 'I_k) a b c r :=
  let cross := fn.interp (Core.arithmetic Core.Add)
    (fn.interp (Core.arithmetic Core.Mul) (fn.interp (get k i) a,fn.interp (get k j) b),
     fn.interp (Core.arithmetic Core.Mul) (fn.interp (get k j) a,fn.interp (get k i) b)) in
  let masked := fn.interp (Core.arithmetic Core.Add) (r,cross) in
  let c := fn.interp (put k i) (c,fn.interp (Core.arithmetic Core.Sub) (fn.interp (get k i) c,r)) in
  fn.interp (put k j) (c,fn.interp (Core.arithmetic Core.Add) (fn.interp (get k j) c,masked)).

Lemma pair_update_interp k i j a b c r :
  fn.interp (pair_update k i j) (a,(b,(c,r))) = pair_result k i j a b c r.
Proof. reflexivity. Qed.

Lemma pair_update_refines k i j a b c r :
  decode k (fn.interp (pair_update k i j) (a,(b,(c,r)))) =
  ArithmeticShares.increment (ArithmeticShares.increment (decode k c) i (- decode_word r)%R) j
    (decode_word r + ArithmeticShares.cross (decode k a) (decode k b) (i,j))%R.
Proof.
  rewrite pair_update_interp /pair_result decode_increment decode_decrement.
  rewrite !decode_arithmetic !get_interp /ArithmeticShares.cross /decode !ffunE. reflexivity.
Qed.

Definition Masks k := Array (Shares k) k.
Definition decode_masks k (r : type.interp (Masks k)) : ArithmeticShares.masks FiatField.curve25519 k :=
  [ffun ij => decode_word (@read Word k (@read (Shares k) k r (val ij.1)) (val ij.2))].

Definition get_mask {var} k (ij : 'I_k * 'I_k) : fn var (Masks k) Word :=
  Fn (fun r => quartz_eexpr:(
    let i := $(expr.Const (t := Bits (index_width k)) (index_bits k ij.1)) in
    let j := $(expr.Const (t := Bits (index_width k)) (index_bits k ij.2)) in
    return #r[#i][#j])).

Lemma get_mask_interp k (ij : 'I_k * 'I_k) r :
  fn.interp (get_mask k ij) r = @read Word k (@read (Shares k) k r (val ij.1)) (val ij.2).
Proof.
  change (@read Word k
    (@read (Shares k) k r (Z.to_nat (Zmod.unsigned (index_bits k ij.1))))
    (Z.to_nat (Zmod.unsigned (index_bits k ij.2))) =
    @read Word k (@read (Shares k) k r (val ij.1)) (val ij.2)).
  by rewrite !index_unsigned !Nat2Z.id.
Qed.

Definition MultiplyInput k := Pair (Shares k) (Pair (Shares k) (Pair (Masks k) (Shares k))).

Fixpoint multiply_steps {var} k (pairs : seq ('I_k * 'I_k)) :
    fn var (MultiplyInput k) (Shares k) :=
  match pairs with
  | List.nil => Fn (fun p => quartz_eexpr:(return #p .2 .2 .2))
  | ij :: rest => Fn (fun p => quartz_eexpr:(
      let a := #p .1 in let b := #p .2 .1 in
      let r := #p .2 .2 .1 in let c := #p .2 .2 .2 in
      let mask := {get_mask k ij} (#r) in
      let c := {pair_update k ij.1 ij.2} ((#a,(#b,(#c,#mask)))) in
      let result := {multiply_steps k rest} ((#a,(#b,(#r,#c)))) in
      return #result))
  end.

Definition multiply {var} k : fn var (Pair (Shares k) (Pair (Shares k) (Masks k))) (Shares k) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let b := #p .2 .1 in let r := #p .2 .2 in
    let c := {share_map Core.Mul k} ((#a,#b)) in
    let result := {multiply_steps k (ArithmeticShares.pair_order k)} ((#a,(#b,(#r,#c)))) in
    return #result)).

Local Opaque pair_update get_mask share_map.

Lemma multiply_steps_refines k pairs a b r c :
  decode k (fn.interp (multiply_steps k pairs) (a,(b,(r,c)))) =
  foldl (ArithmeticShares.pair_update (decode k a) (decode k b) (decode_masks k r)) (decode k c) pairs.
Proof.
  revert c. induction pairs as [|ij rest IH]; intro c; [reflexivity|].
  change (decode k (fn.interp (multiply_steps k rest)
    (a,(b,(r,fn.interp (pair_update k ij.1 ij.2) (a,(b,(c,fn.interp (get_mask k ij) r))))))) =
    foldl (ArithmeticShares.pair_update (decode k a) (decode k b) (decode_masks k r))
      (decode k c) (ij :: rest)).
  rewrite IH pair_update_refines get_mask_interp. simpl foldl.
  congr (foldl _ _ rest).
  rewrite /ArithmeticShares.pair_update /decode_masks ffunE. reflexivity.
Qed.

Theorem multiply_refines k a b r :
  decode k (fn.interp (multiply k) (a,(b,r))) =
  ArithmeticShares.sequential_multiply (decode k a) (decode k b) (decode_masks k r).
Proof.
  change (decode k (fn.interp (multiply_steps k (ArithmeticShares.pair_order k))
    (a,(b,(r,fn.interp (share_map Core.Mul k) (a,b))))) =
    ArithmeticShares.sequential_multiply (decode k a) (decode k b) (decode_masks k r)).
  rewrite multiply_steps_refines diagonal_refines. reflexivity.
Qed.

Fixpoint anchor_steps {var} (subtract : fn var (Pair Word Word) Word) n (indices : seq 'I_n) :
    fn var (Pair Word (Shares n)) Word :=
  match indices with
  | List.nil => Fn (fun p => quartz_eexpr:(return #p .1))
  | i :: rest => Fn (fun p => quartz_eexpr:(
      let r := {get n i} (#p .2) in
      let h := {subtract} ((#p .1,#r)) in
      let result := {anchor_steps subtract n rest} ((#h,#p .2)) in
      return #result))
  end.

Definition refresh_anchor {var} n indices := @anchor_steps var (Core.arithmetic Core.Sub) n indices.

Lemma anchor_steps_cons subtract n i rest h r :
  fn.interp (anchor_steps subtract n (i :: rest)) (h,r) =
  fn.interp (anchor_steps subtract n rest) (fn.interp subtract (h,fn.interp (get n i) r),r).
Proof. reflexivity. Qed.

Fixpoint refresh_tail {var} n (indices : seq 'I_n) :
    fn var (Pair (Shares (S n)) (Pair (Shares n) (Shares (S n)))) (Shares (S n)) :=
  match indices with
  | List.nil => Fn (fun p => quartz_eexpr:(return #p .2 .2))
  | i :: rest => Fn (fun p => quartz_eexpr:(
      let a := #p .1 in let r := #p .2 .1 in let c := #p .2 .2 in
      let x := {get (S n) (lift ord0 i)} (#a) in
      let mask := {get n i} (#r) in
      let w := {Core.arithmetic Core.Add} ((#x,#mask)) in
      let c := {put (S n) (lift ord0 i)} ((#c,#w)) in
      let result := {refresh_tail n rest} ((#a,(#r,#c))) in
      return #result))
  end.

Definition refresh {var} n : fn var (Pair (Shares (S n)) (Shares n)) (Shares (S n)) :=
  Fn (fun p => quartz_eexpr:(
    let a := #p .1 in let r := #p .2 in
    let h := {get (S n) ord0} (#a) in
    let h := {refresh_anchor n (enum 'I_n)} ((#h,#r)) in
    let c := {refresh_tail n (enum 'I_n)} ((#a,(#r,#a))) in
    let c := {put (S n) ord0} ((#c,#h)) in
    return #c)).

Lemma refresh_anchor_cons n i rest h r :
  fn.interp (refresh_anchor n (i :: rest)) (h,r) =
  fn.interp (refresh_anchor n rest)
    (fn.interp (Core.arithmetic Core.Sub) (h,fn.interp (get n i) r),r).
Proof. apply anchor_steps_cons. Qed.

Lemma refresh_anchor_refines n indices h r :
  decode_word (fn.interp (refresh_anchor n indices) (h,r)) =
  (decode_word h - \sum_(i <- indices) decode n r i)%R.
Proof.
  revert h. induction indices as [|i rest IH]; intro h.
  - by rewrite big_nil GRing.subr0.
  - rewrite refresh_anchor_cons IH decode_arithmetic get_interp big_cons.
    rewrite /field_operation /decode !ffunE GRing.opprD GRing.addrA. reflexivity.
Qed.

Lemma refresh_tail_cons n i rest a r c :
  fn.interp (refresh_tail n (i :: rest)) (a,(r,c)) =
  fn.interp (refresh_tail n rest) (a,(r,fn.interp (put (S n) (lift ord0 i))
    (c,fn.interp (Core.arithmetic Core.Add)
      (fn.interp (get (S n) (lift ord0 i)) a,fn.interp (get n i) r)))).
Proof. reflexivity. Qed.

Lemma refresh_tail_anchor n indices a r c :
  decode (S n) (fn.interp (refresh_tail n indices) (a,(r,c))) ord0 = decode (S n) c ord0.
Proof.
  revert c. induction indices as [|i rest IH]; intro c; [reflexivity|].
  rewrite refresh_tail_cons IH decode_put.
  have Hneq : (ord0 == lift ord0 i) = false := negbTE (neq_lift ord0 i).
  by rewrite Hneq.
Qed.

Lemma refresh_tail_refines n indices a r c (j : 'I_n) :
  decode (S n) (fn.interp (refresh_tail n indices) (a,(r,c))) (lift ord0 j) =
  if j \in indices then (decode (S n) a (lift ord0 j) + decode n r j)%R
  else decode (S n) c (lift ord0 j).
Proof.
  revert c. induction indices as [|i rest IH]; intro c; [reflexivity|].
  rewrite refresh_tail_cons IH in_cons.
  case Hrest: (j \in rest); simpl; [by rewrite orbT|].
  rewrite orbF decode_put (eqtype.inj_eq (@lift_inj _ ord0)).
  case E: (j == i); last reflexivity.
  move/eqP: E => ->. rewrite decode_arithmetic !get_interp /decode !ffunE. reflexivity.
Qed.

Theorem refresh_refines n a r :
  decode (S n) (fn.interp (refresh n) (a,r)) = ArithmeticRefresh.refresh (decode (S n) a) (decode n r).
Proof.
  change (decode (S n) (fn.interp (put (S n) ord0)
    (fn.interp (refresh_tail n (enum 'I_n)) (a,(r,a)),
     fn.interp (refresh_anchor n (enum 'I_n)) (fn.interp (get (S n) ord0) a,r))) =
    ArithmeticRefresh.refresh (decode (S n) a) (decode n r)).
  apply/ffunP => i. rewrite decode_put.
  case: (unliftP ord0 i) => [j ->|->].
  - rewrite lift_eqF refresh_tail_refines mem_enum ArithmeticRefresh.refresh_tail. reflexivity.
  - rewrite eqxx refresh_anchor_refines get_interp ArithmeticRefresh.refresh_anchor.
    rewrite big_enum /decode !ffunE. reflexivity.
Qed.

Lemma put_canonical k (i : 'I_k) a w :
  canonical k a -> 0 <= Zmod.unsigned w < Core.prime ->
  canonical k (fn.interp (put k i) (a,w)).
Proof.
  intros Ha Hw j. have Hj : Nat.lt (val j) k := elimT ltP (ltn_ord j).
  rewrite put_interp (read_upd _ _ _ _ Hj).
  case: (Nat.eqb (val j) (val i)); [exact Hw | exact (Ha j)].
Qed.

Lemma pair_update_canonical k i j a b c r :
  canonical k c -> canonical k (fn.interp (pair_update k i j) (a,(b,(c,r)))).
Proof.
  intro Hc. rewrite pair_update_interp /pair_result.
  apply put_canonical; last apply AC.arithmetic_canonical.
  apply put_canonical; [exact Hc | apply AC.arithmetic_canonical].
Qed.

Lemma multiply_steps_cons k ij rest a b r c :
  fn.interp (multiply_steps k (ij :: rest)) (a,(b,(r,c))) =
  fn.interp (multiply_steps k rest)
    (a,(b,(r,fn.interp (pair_update k ij.1 ij.2) (a,(b,(c,fn.interp (get_mask k ij) r)))))).
Proof. reflexivity. Qed.

Lemma multiply_steps_canonical k pairs a b r c :
  canonical k c -> canonical k (fn.interp (multiply_steps k pairs) (a,(b,(r,c)))).
Proof.
  revert c. induction pairs as [|ij rest IH]; intros c Hc; [exact Hc|].
  rewrite multiply_steps_cons. apply IH. apply pair_update_canonical. exact Hc.
Qed.

Theorem multiply_canonical k a b r : canonical k (fn.interp (multiply k) (a,(b,r))).
Proof.
  change (canonical k (fn.interp (multiply_steps k (ArithmeticShares.pair_order k))
    (a,(b,(r,fn.interp (share_map Core.Mul k) (a,b)))))).
  apply multiply_steps_canonical. apply share_map_canonical.
Qed.

Lemma refresh_anchor_canonical n indices h r :
  0 <= Zmod.unsigned h < Core.prime ->
  0 <= Zmod.unsigned (fn.interp (refresh_anchor n indices) (h,r)) < Core.prime.
Proof.
  revert h. induction indices as [|i rest IH]; intros h Hh; [exact Hh|].
  rewrite refresh_anchor_cons. apply IH. apply AC.arithmetic_canonical.
Qed.

Lemma refresh_tail_canonical n indices a r c :
  canonical (S n) c -> canonical (S n) (fn.interp (refresh_tail n indices) (a,(r,c))).
Proof.
  revert c. induction indices as [|i rest IH]; intros c Hc; [exact Hc|].
  rewrite refresh_tail_cons. apply IH. apply put_canonical; [exact Hc | apply AC.arithmetic_canonical].
Qed.

(* For n=0 the single input share passes through unchanged, so canonicality is an input invariant. *)
Theorem refresh_canonical n a r :
  canonical (S n) a -> canonical (S n) (fn.interp (refresh n) (a,r)).
Proof.
  intro Ha.
  change (canonical (S n) (fn.interp (put (S n) ord0)
    (fn.interp (refresh_tail n (enum 'I_n)) (a,(r,a)),
     fn.interp (refresh_anchor n (enum 'I_n)) (fn.interp (get (S n) ord0) a,r)))).
  apply put_canonical.
  - apply refresh_tail_canonical. exact Ha.
  - apply refresh_anchor_canonical. rewrite get_interp. exact (Ha ord0).
Qed.

Corollary multiply_correct k a b r :
  ArithmeticShares.reconstruct (decode k (fn.interp (multiply k) (a,(b,r)))) =
  (ArithmeticShares.reconstruct (decode k a) * ArithmeticShares.reconstruct (decode k b))%R.
Proof. rewrite multiply_refines. apply ArithmeticShares.sequential_multiply_correct. Qed.

Corollary refresh_correct n a r :
  ArithmeticShares.reconstruct (decode (S n) (fn.interp (refresh n) (a,r))) =
  ArithmeticShares.reconstruct (decode (S n) a).
Proof. rewrite refresh_refines. apply ArithmeticRefresh.refresh_correct. Qed.

End MaskedArithmetic.

Print Assumptions MaskedArithmetic.add_refines.
Print Assumptions MaskedArithmetic.sub_refines.
Print Assumptions MaskedArithmetic.multiply_refines.
Print Assumptions MaskedArithmetic.refresh_refines.
Print Assumptions MaskedArithmetic.multiply_canonical.
Print Assumptions MaskedArithmetic.refresh_canonical.
Print Assumptions MaskedArithmetic.multiply_correct.
Print Assumptions MaskedArithmetic.refresh_correct.
