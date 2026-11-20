From quartz.lang Require Import domain Syntax.
From LadderQuartz Require Import accelerator.
From Stdlib Require Import ZArith Bits Lia.
Import LadderAccelerator.
Import (coercions) type domain.Zmod.
Open Scope Z_scope.

Module AcceleratorCorrectness.
  Definition radix : Z := 2^255.
  Definition fold (x : Z) : Z :=
    x mod radix + 19 * (x / radix).

  Lemma radix_positive : 0 < radix.
  Proof. vm_compute. reflexivity. Qed.

  Lemma prime_positive : 0 < prime.
  Proof. vm_compute. reflexivity. Qed.

  Lemma fold_bound x q :
    0 <= x < q * radix -> 0 <= fold x < radix + 19*q.
  Proof.
    intros Hx. pose proof radix_positive.
    pose proof (Z.mod_pos_bound x radix H).
    assert (0 <= x / radix) by (apply Z.div_pos; lia).
    assert (x / radix < q) by (apply Z.div_lt_upper_bound; lia).
    unfold fold. lia.
  Qed.

  Lemma fold_mod x : fold x mod prime = x mod prime.
  Proof.
    pose proof (Z.div_mod x radix ltac:(pose proof radix_positive; lia)) as H.
    assert (E : fold x = x - (x / radix) * prime).
    { unfold fold, radix, prime in *. lia. }
    rewrite E, Zminus_mod, Z_mod_mult, Z.sub_0_r, Z.mod_mod
      by (pose proof prime_positive; lia).
    reflexivity.
  Qed.

  Lemma fold_512_bound x :
    0 <= x < 2^512 -> 0 <= fold x < 77 * radix.
  Proof.
    intros Hx.
    assert (E : 2^512 = 2^257 * radix) by (vm_compute; reflexivity).
    rewrite E in Hx.
    pose proof (fold_bound x (2^257) Hx) as H.
    assert (F : radix + 19*2^257 = 77*radix) by (vm_compute; reflexivity).
    rewrite F in H. exact H.
  Qed.

  Lemma three_folds_bound x :
    0 <= x < 2^512 -> 0 <= fold (fold (fold x)) < 2*prime.
  Proof.
    intros Hx.
    pose proof (fold_512_bound x Hx) as H1.
    pose proof (fold_bound (fold x) 77 H1) as H2.
    assert (H3 : 0 <= fold (fold x) < 2*radix).
    { assert (1500 < radix) by (vm_compute; reflexivity). lia. }
    pose proof (fold_bound (fold (fold x)) 2 H3).
    assert (prime = radix - 19) by reflexivity.
    assert (100 < radix) by (vm_compute; reflexivity). lia.
  Qed.

  Lemma fold255_correct (x : bits 512) :
    Zmod.unsigned (fn.interp fold255 x) = fold (Zmod.unsigned x).
  Proof.
    change (Zmod.unsigned
      (Zmod.add
        (bits.of_Z 512 (Zmod.unsigned (Zmod.firstn 255 (Zmod.skipn 0 x))))
        (bits.of_Z 512 (Zmod.unsigned (Zmod.sru x (Zmod.unsigned (bits.of_Z 512 255))) *
          Zmod.unsigned (bits.of_Z 512 19)))) = fold (Zmod.unsigned x)).
    rewrite bits.unsigned_add, !bits.unsigned_of_Z, bits.unsigned_firstn,
      bits.unsigned_skipn by lia.
    rewrite Z.div_1_r.
    change (255 mod 2^512) with 255.
    change (19 mod 2^512) with 19.
    rewrite Zmod.unsigned_sru, Z.shiftr_div_pow2 by lia.
    rewrite Z.mod_small with (a := Zmod.unsigned x mod 2^255)
      by (pose proof (Z.mod_pos_bound (Zmod.unsigned x) (2^255) ltac:(compute; reflexivity)); lia).
    pose proof (bits.unsigned_range x ltac:(lia)) as Hx.
    pose proof (fold_512_bound (Zmod.unsigned x) Hx) as Hf.
    pose proof (Z.div_pos (Zmod.unsigned x) (2^255) ltac:(lia) ltac:(compute; reflexivity)).
    unfold fold, radix in Hf |- *.
    rewrite Z.mod_small with (a := Zmod.unsigned x / 2^255 * 19) by
      (pose proof (Z.mod_pos_bound (Zmod.unsigned x) (2^255) ltac:(compute; reflexivity)); lia).
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma subtract_once c :
    0 <= c < 2*prime ->
    (if c >=? prime then c-prime else c) = c mod prime.
  Proof.
    intros Hc. pose proof prime_positive.
    destruct (Z.geb_spec c prime).
    - apply Z.mod_unique with (q := 1); lia.
    - symmetry. apply Z.mod_small. lia.
  Qed.

  Theorem reduce_correct (x : bits 512) :
    Zmod.unsigned (fn.interp reduce x) = Zmod.unsigned x mod prime.
  Proof.
    set (c := fn.interp fold255 (fn.interp fold255 (fn.interp fold255 x))).
    change (Zmod.unsigned (bits.of_Z 255 (Zmod.unsigned
      (if Zmod.nonzero (Zmod.embed_bool
        (Zmod.unsigned c >=? Zmod.unsigned (bits.of_Z 512 prime)))
       then Zmod.sub c (bits.of_Z 512 prime) else c))) = Zmod.unsigned x mod prime).
    rewrite Zmod.nonzero_bool.
    rewrite bits.unsigned_of_Z_small with (z := prime) by
      (unfold prime; lia).
    assert (Ec : Zmod.unsigned c = fold (fold (fold (Zmod.unsigned x)))).
    { unfold c. rewrite !fold255_correct. reflexivity. }
    pose proof (three_folds_bound _ (bits.unsigned_range x ltac:(lia))) as Hc.
    rewrite <-Ec in Hc.
    assert (Hr : 0 <= Zmod.unsigned x mod prime < prime) by
      (apply Z.mod_pos_bound, prime_positive).
    assert (Em : Zmod.unsigned c mod prime = Zmod.unsigned x mod prime).
    { rewrite Ec, !fold_mod. reflexivity. }
    rewrite bits.unsigned_of_Z.
    destruct (Z.geb_spec (Zmod.unsigned c) prime).
    - rewrite bits.unsigned_sub, bits.unsigned_of_Z_small with (z := prime) by
        (unfold prime; lia).
      rewrite Z.mod_small with (a := Zmod.unsigned c - prime) by
        (unfold prime in *; lia).
      rewrite Z.mod_small by (unfold prime in *; lia).
      rewrite <-Em. apply Z.mod_unique with (q := 1); lia.
    - rewrite Z.mod_small by (unfold prime in *; lia).
      rewrite <-Em. symmetry. apply Z.mod_small. lia.
  Qed.
  Definition field_operation (op : operation) (a b : Z) : Z :=
    (match op with Add => a+b | Sub => a-b | Mul => a*b end) mod prime.

  Definition wide_operation op (a b : bits 255) : bits 512 :=
      match op with
       | Add => Zmod.add (bits.of_Z 512 (Zmod.unsigned a)) (bits.of_Z 512 (Zmod.unsigned b))
       | Sub => Zmod.sub
           (Zmod.add (bits.of_Z 512 (Zmod.unsigned a)) (bits.of_Z 512 (2*prime)))
           (bits.of_Z 512 (Zmod.unsigned b))
       | Mul => bits.of_Z 512
           (Zmod.unsigned (bits.of_Z 512 (Zmod.unsigned a)) *
            Zmod.unsigned (bits.of_Z 512 (Zmod.unsigned b)))
       end.

  Lemma arithmetic_interp op (a b : bits 255) :
    fn.interp (arithmetic op) (a,b) = fn.interp reduce (wide_operation op a b).
  Proof. destruct op; reflexivity. Qed.

  Theorem arithmetic_correct op (a b : bits 255) :
    Zmod.unsigned (fn.interp (arithmetic op) (a,b)) =
    field_operation op (Zmod.unsigned a) (Zmod.unsigned b).
  Proof.
    pose proof (bits.unsigned_range a ltac:(lia)) as Ha.
    pose proof (bits.unsigned_range b ltac:(lia)) as Hb.
    rewrite arithmetic_interp, reduce_correct.
    unfold wide_operation.
    destruct op; unfold field_operation.
    - rewrite bits.unsigned_add, !bits.unsigned_of_Z_small by lia.
      rewrite (Z.mod_small (Zmod.unsigned a + Zmod.unsigned b) (2^512)) by lia.
      reflexivity.
    - rewrite bits.unsigned_sub, bits.unsigned_add, !bits.unsigned_of_Z_small
        by (unfold prime; lia).
      rewrite Z.mod_small with (a := Zmod.unsigned a + 2*prime) by (unfold prime; lia).
      rewrite Z.mod_small with (a := Zmod.unsigned a + 2*prime - Zmod.unsigned b)
        by (unfold prime; lia).
      replace (Zmod.unsigned a + 2*prime - Zmod.unsigned b)
        with (Zmod.unsigned a - Zmod.unsigned b + 2*prime) by ring.
      apply Z.mod_add. pose proof prime_positive. lia.
    - rewrite !bits.unsigned_of_Z.
      rewrite (Z.mod_small (Zmod.unsigned a) (2^512)) by lia.
      rewrite (Z.mod_small (Zmod.unsigned b) (2^512)) by lia.
      rewrite Z.mod_small with (a := Zmod.unsigned a * Zmod.unsigned b) by nia.
      reflexivity.
  Qed.

  Corollary arithmetic_canonical op (a b : bits 255) :
    0 <= Zmod.unsigned (fn.interp (arithmetic op) (a,b)) < prime.
  Proof.
    rewrite arithmetic_correct. unfold field_operation.
    apply Z.mod_pos_bound, prime_positive.
  Qed.
  Definition ladder_formula {A : Type} (add sub mul : A -> A -> A)
    (a24 x1 x2 z2 x3 z3 : A) : (A*A)*(A*A) :=
    let u := add x2 z2 in let v := sub x2 z2 in
    let w := add x3 z3 in let t := sub x3 z3 in
    let uu := mul u u in let vv := mul v v in
    let ut := mul u t in let vw := mul v w in
    let s := add ut vw in let d := sub ut vw in
    let e := sub uu vv in
    ((mul uu vv, mul e (add vv (mul a24 e))), (mul s s, mul (mul d d) x1)).

  Local Opaque arithmetic.

  Lemma ladder_schedule x1 x2 z2 x3 z3 :
    fn.interp output (run 18 (initial x1 x2 z2 x3 z3)) =
    ladder_formula
      (fun a b => fn.interp (arithmetic Add) (a,b))
      (fun a b => fn.interp (arithmetic Sub) (a,b))
      (fun a b => fn.interp (arithmetic Mul) (a,b))
      (bits.of_Z 255 121666) (bits.of_Z 255 x1)
      (bits.of_Z 255 x2) (bits.of_Z 255 z2) (bits.of_Z 255 x3) (bits.of_Z 255 z3).
  Proof. reflexivity. Qed.

  Definition output_Z (s : State) : (Z*Z)*(Z*Z) :=
    let '((x2,z2),(x3,z3)) := fn.interp output s in
    ((Zmod.unsigned x2, Zmod.unsigned z2), (Zmod.unsigned x3, Zmod.unsigned z3)).

  Theorem ladder_step_correct x1 x2 z2 x3 z3 :
    0 <= x1 < 2^255 -> 0 <= x2 < 2^255 -> 0 <= z2 < 2^255 ->
    0 <= x3 < 2^255 -> 0 <= z3 < 2^255 ->
    output_Z (run 18 (initial x1 x2 z2 x3 z3)) =
    ladder_formula (field_operation Add) (field_operation Sub) (field_operation Mul)
      121666 x1 x2 z2 x3 z3.
  Proof.
    intros H1 H2 H3 H4 H5. unfold output_Z.
    rewrite ladder_schedule. unfold ladder_formula.
    cbv beta iota zeta.
    rewrite !arithmetic_correct, !bits.unsigned_of_Z_small by lia.
    reflexivity.
  Qed.
End AcceleratorCorrectness.
