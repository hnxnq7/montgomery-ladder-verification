From Stdlib Require Import ZArith Bits List Vector String Lia.
From quartz.lang Require Import Syntax transform.
From LadderQuartz Require Import hamming_weight.
Import ListNotations Syntax.type.
Open Scope Z_scope.

Module PackedStorage.

Lemma app_bit_low n m (a : bits n) (b : bits m) i :
  0 <= n -> 0 <= m -> 0 <= i < n ->
  Z.testbit (Zmod.unsigned (Zmod.app a b)) i = Z.testbit (Zmod.unsigned a) i.
Proof.
  intros Hn Hm Hi. rewrite bits.unsigned_app by assumption.
  rewrite Z.lor_spec, Z.shiftl_spec by lia.
  rewrite (Z.testbit_neg_r (Zmod.unsigned b) (i - n)) by lia. apply Bool.orb_false_r.
Qed.

Lemma app_bit_high n m (a : bits n) (b : bits m) i :
  0 <= n -> 0 <= m -> 0 <= i ->
  Z.testbit (Zmod.unsigned (Zmod.app a b)) (n + i) = Z.testbit (Zmod.unsigned b) i.
Proof.
  intros Hn Hm Hi. rewrite bits.unsigned_app by assumption.
  rewrite Z.lor_spec, Z.shiftl_spec by lia.
  rewrite bits.testbit_high by lia.
  replace (n + i - n) with i by lia. reflexivity.
Qed.

Lemma bit_count_app n (w : bits n) xs ys :
  RegisterHW.bit_count w (xs ++ ys) =
    (RegisterHW.bit_count w xs + RegisterHW.bit_count w ys)%nat.
Proof. unfold RegisterHW.bit_count; induction xs; simpl in *; lia. Qed.

Lemma app_count_low n m (a : bits n) (b : bits m) xs :
  0 <= n -> 0 <= m -> List.Forall (fun i => Z.of_nat i < n) xs ->
  RegisterHW.bit_count (Zmod.app a b) xs = RegisterHW.bit_count a xs.
Proof.
  intros Hn Hm H. induction H; cbn [RegisterHW.bit_count List.fold_right]; auto.
  rewrite app_bit_low by lia. unfold RegisterHW.bit_count in IHForall. now rewrite IHForall.
Qed.

Lemma app_count_high n m (a : bits n) (b : bits m) xs :
  0 <= n -> 0 <= m ->
  RegisterHW.bit_count (Zmod.app a b) (List.map (fun i => (Z.to_nat n + i)%nat) xs) =
    RegisterHW.bit_count b xs.
Proof.
  intros Hn Hm. induction xs; cbn [List.map RegisterHW.bit_count List.fold_right]; auto.
  rewrite Nat2Z.inj_add, Z2Nat.id by assumption.
  rewrite app_bit_high by lia. unfold RegisterHW.bit_count in IHxs. now rewrite IHxs.
Qed.

Lemma seq_offset start len :
  List.seq start len = List.map (fun i => (start + i)%nat) (List.seq 0 len).
Proof.
  revert start. induction len; intros start; cbn; auto.
  rewrite Nat.add_0_r, IHlen.
  rewrite (IHlen 1%nat), List.map_map.
  f_equal. apply List.map_ext. intros; lia.
Qed.

Theorem word_HW_app n m (a : bits n) (b : bits m) :
  0 <= n -> 0 <= m ->
  RegisterHW.word_HW (Zmod.app a b) = (RegisterHW.word_HW a + RegisterHW.word_HW b)%nat.
Proof.
  intros Hn Hm. unfold RegisterHW.word_HW.
  rewrite Z2Nat.inj_add by assumption.
  rewrite List.seq_app, bit_count_app.
  rewrite app_count_low by (try assumption; apply List.Forall_forall; intros i Hi;
    apply List.in_seq in Hi; rewrite <- (Z2Nat.id n Hn); lia).
  rewrite Nat.add_0_l, (seq_offset (Z.to_nat n) (Z.to_nat m)), app_count_high by assumption.
  reflexivity.
Qed.

Fixpoint fields_plain (p : Syntax.type.type -> Prop) (fs : list (string * Syntax.type.type)) : Prop :=
  match fs with [] => True | nt :: rest => p (snd nt) /\ fields_plain p rest end.

Fixpoint plain (t : Syntax.type.type) : Prop :=
  match t with
  | Bits n => 0 <= n
  | Pair a b => plain a /\ plain b
  | Either _ _ => False
  | Struct _ fs => fields_plain plain fs
  | Array t _ => plain t
  end.

Section FieldSum.
  Variable hw : forall t : Syntax.type.type, Syntax.type.interp t -> nat.
  Fixpoint struct_HW (fs : list (string * Syntax.type.type)) :
      List.fold_right (fun nt T => (Syntax.type.interp (snd nt) * T)%type) unit fs -> nat :=
    match fs return List.fold_right
      (fun nt T => (Syntax.type.interp (snd nt) * T)%type) unit fs -> nat with
    | [] => fun _ => 0%nat
    | nt :: rest => fun v => (hw (snd nt) (fst v) + struct_HW rest (snd v))%nat
    end.
  Fixpoint array_HW t n (v : Vector.t (Syntax.type.interp t) n) : nat :=
    match v with
    | Vector.nil _ => 0%nat
    | Vector.cons _ x _ rest => (hw t x + array_HW t _ rest)%nat
    end.
End FieldSum.

(* Every field and every array element contributes, including inactive stored values. *)
Fixpoint storage_HW (t : Syntax.type.type) : Syntax.type.interp t -> nat :=
  match t return Syntax.type.interp t -> nat with
  | Bits _ => fun v => RegisterHW.word_HW v
  | Pair a b => fun v => (storage_HW a (fst v) + storage_HW b (snd v))%nat
  | Either a b => fun v => match v with inl x => storage_HW a x | inr x => storage_HW b x end
  | Struct _ fs => struct_HW storage_HW fs
  | Array t n => array_HW storage_HW t n
  end.

Theorem pack_HW_and_size t : plain t ->
  0 <= transform.type.size t /\ forall v : Syntax.type.interp t,
    RegisterHW.word_HW (transform.type.pack v) = storage_HW t v.
Proof.
  induction t using transform.type.type_ind; cbn [plain]; intros Hplain.
  - split; auto.
  - destruct Hplain as [Ha Hb]. destruct (IHt1 Ha) as [Hsa Hwa].
    destruct (IHt2 Hb) as [Hsb Hwb]. split; cbn [transform.type.size]; try lia.
    intros [a b]. cbn [transform.type.pack storage_HW].
    rewrite word_HW_app, Hwa, Hwb by assumption. lia.
  - contradiction.
  - induction H.
    + split; [cbn; lia | intros []; reflexivity].
    + destruct x as [fname field]. destruct Hplain as [Hfield Htail]. cbn in *.
      destruct (H Hfield) as [Hsize Hword].
      destruct (IHForall Htail) as [Hrest HWrest].
      split; [cbn; lia | intros [v rest]].
      cbn [transform.type.pack transform.type.pack_struct storage_HW struct_HW].
      rewrite word_HW_app by assumption. rewrite Hword, HWrest. lia.
  - destruct (IHt Hplain) as [Hsize Hword].
    assert (Hiter : forall n, 0 <= Nat.iter n (Z.add (transform.type.size t)) 0).
    { intro count. induction count.
      - change (0 <= 0); lia.
      - change (0 <= transform.type.size t + Nat.iter count (Z.add (transform.type.size t)) 0).
        lia. }
    split; [apply Hiter | intros v].
    induction v; cbn [transform.type.pack transform.type.pack_array storage_HW array_HW].
    + reflexivity.
    + pose proof (word_HW_app _ _ (transform.type.pack h)
        (transform.type.pack_array (@transform.type.pack) n v) Hsize (Hiter n)) as Hcat.
      rewrite Hword in Hcat.
      change (RegisterHW.word_HW (transform.type.pack_array (@transform.type.pack) n v) =
        array_HW storage_HW t n v) in IHv.
      rewrite IHv in Hcat. exact Hcat.
Qed.

Theorem pack_HW t (v : Syntax.type.interp t) : plain t ->
  RegisterHW.word_HW (transform.type.pack v) = storage_HW t v.
Proof. intros H; exact (proj2 (pack_HW_and_size t H) v). Qed.

End PackedStorage.

Print Assumptions PackedStorage.word_HW_app.
Print Assumptions PackedStorage.pack_HW.
