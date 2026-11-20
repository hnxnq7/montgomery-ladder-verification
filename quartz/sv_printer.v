From Stdlib Require Import String List Decimal DecimalString DecimalNat.
From quartz.lang Require Import Syntax transform pp sv.

Module SVExprDList.
Local Open Scope string_scope.

Definition builder := string -> string.
Lemma append_assoc a b c : (a ++ b) ++ c = a ++ (b ++ c).
Proof. induction a; cbn; [reflexivity|]. now rewrite IHa. Qed.
Lemma append_empty_r a : a ++ "" = a.
Proof. induction a; cbn; [reflexivity|]. now rewrite IHa. Qed.

Record counter := Counter { number : nat; digits : Decimal.uint }.
Definition valid (c : counter) := digits c = Nat.to_little_uint (number c) Decimal.zero.
Definition initial n := Counter n (Nat.to_little_uint n Decimal.zero).
Definition bump c := Counter (S (number c)) (Decimal.Little.succ (digits c)).
Definition counter_text c := DecimalString.NilZero.string_of_uint (Decimal.rev (digits c)).

Lemma initial_valid n : valid (initial n).
Proof. reflexivity. Qed.

Lemma bump_valid c : valid c -> valid (bump c).
Proof.
  unfold valid, bump; cbn. intro H. rewrite H.
  change (Decimal.Little.succ (Nat.to_little_uint (number c) Decimal.zero) =
    Nat.to_little_uint (number c) (Decimal.Little.succ Decimal.zero)).
  symmetry. apply DecimalNat.Unsigned.to_little_uint_succ.
Qed.

Lemma counter_text_correct c : valid c -> counter_text c = pp.nat (number c).
Proof. unfold valid, counter_text, pp.nat, Nat.to_uint. intro H. now rewrite H. Qed.

(* The cached digits advance with the original counter; only string assembly changes. *)
Fixpoint build_cached {t} (ind : string) (e : eexpr.eexpr sv.var sv.fn t)
    (out : string) (c : counter) : builder * counter :=
  match e with
  | eexpr.Ret exp =>
      (fun tail => ind ++ out ++ " = " ++ sv.pp_expr exp ++ ";" ++ tail, c)
  | @eexpr.Let _ _ hint tx a _ k =>
      let name := hint ++ "_" ++ counter_text c in
      let prefix := ind ++ sv.valid_ident hint ++ "begin " ++ sv.pp_type tx ++ " " ++
        name ++ " = " ++ sv.pp_expr a ++ ";" in
      let '(body, next) := build_cached ind (k name) out (bump c) in
      (fun tail => prefix ++ "" ++ pp.LF ++ body (" end" ++ tail), next)
  | @eexpr.Bind _ _ hint tx a _ k =>
      let name := hint ++ "_" ++ counter_text c in
      let prefix := ind ++ sv.valid_ident hint ++ "begin " ++ sv.pp_type tx ++ " " ++ name ++ ";" in
      let '(first, middle) := build_cached ind a name (bump c) in
      let '(second, next) := build_cached ind (k name) out middle in
      (fun tail => prefix ++ "" ++ pp.LF ++ first ("" ++ pp.LF ++ second (" end" ++ tail)), next)
  | eexpr.If cond a b =>
      let nested := ind ++ "  " in
      let '(ltext, middle) := build_cached nested a out c in
      let '(rtext, next) := build_cached nested b out middle in
      (fun tail => ind ++ "if (" ++ sv.pp_expr cond ++ ") begin" ++ pp.LF ++
        ltext ("" ++ pp.LF ++ ind ++ "end else begin" ++ pp.LF ++
          rtext ("" ++ pp.LF ++ ind ++ "end" ++ tail)), next)
  | @eexpr.Case _ _ l r cond _ lbranch rbranch =>
      let lname := "left_" ++ counter_text c in
      let rname := "right_" ++ counter_text c in
      let case_ind := ind ++ "  " in
      let nested := case_ind ++ "  " in
      let '(lbody, middle) := build_cached nested (lbranch lname) out (bump c) in
      let '(rbody, next) := build_cached nested (rbranch rname) out middle in
      (fun tail => ind ++ "case (" ++ sv.pp_expr cond ++ ") matches" ++ pp.LF ++
        case_ind ++ "tagged left ." ++ lname ++ " : begin" ++ pp.LF ++
        lbody ("" ++ pp.LF ++ case_ind ++ "end" ++ pp.LF ++
          case_ind ++ "tagged right ." ++ rname ++ " : begin" ++ pp.LF ++
          rbody ("" ++ pp.LF ++ case_ind ++ "end" ++ pp.LF ++ ind ++ "endcase" ++ tail)), next)
  | @eexpr.Upd _ _ context index _ source value =>
      (fun tail => ind ++ out ++ " = " ++ sv.pp_expr source ++ ";" ++ pp.LF ++ ind ++
        sv.pp_hole_upd context out (sv.pp_expr index) ++ " = " ++ sv.pp_expr value ++ ";" ++ tail, c)
  end.

Definition matches (b : builder * counter) (p : string * nat) : Prop :=
  number (snd b) = snd p /\ valid (snd b) /\
  forall suffix, fst b suffix = fst p ++ suffix.

Ltac finish_text :=
  cbn [fst snd]; repeat rewrite append_assoc; reflexivity.

Theorem build_cached_correct t (e : eexpr.eexpr sv.var sv.fn t) :
  forall ind out c, valid c ->
  matches (build_cached ind e out c) (sv.pp_eexpr ind e out (number c)).
Proof.
  induction e as [t exp | hint tx a t k IH | hint tx a IHa t k IHk |
    t cond a IHa b IHb | l r cond t kl IHl kr IHr | context index t source value];
    intros ind out c V.
  - cbn [build_cached sv.pp_eexpr]. split; [reflexivity|]. split; [exact V|].
    intro suffix. finish_text.
  - cbn [build_cached sv.pp_eexpr]. rewrite (counter_text_correct c V).
    pose proof (IH (hint ++ "_" ++ pp.nat (number c)) ind out (bump c) (bump_valid c V)) as K.
    cbn [number bump] in K.
    destruct (build_cached ind (k (hint ++ "_" ++ pp.nat (number c))) out (bump c)) as [f d].
    destruct (sv.pp_eexpr ind (k (hint ++ "_" ++ pp.nat (number c))) out (S (number c))) as [s j].
    destruct K as [E [W T]]. cbn in E, W, T. subst j.
    split; [reflexivity|]. split; [exact W|]. intro suffix. cbn [fst snd]. rewrite T. finish_text.
  - cbn [build_cached sv.pp_eexpr]. rewrite (counter_text_correct c V).
    pose proof (IHa ind (hint ++ "_" ++ pp.nat (number c)) (bump c) (bump_valid c V)) as K.
    cbn [number bump] in K.
    destruct (build_cached ind a (hint ++ "_" ++ pp.nat (number c)) (bump c)) as [f d].
    destruct (sv.pp_eexpr ind a (hint ++ "_" ++ pp.nat (number c)) (S (number c))) as [s j].
    destruct K as [E [W T]]. cbn in E, W, T. subst j.
    pose proof (IHk (hint ++ "_" ++ pp.nat (number c)) ind out d W) as K.
    destruct (build_cached ind (k (hint ++ "_" ++ pp.nat (number c))) out d) as [g d2].
    destruct (sv.pp_eexpr ind (k (hint ++ "_" ++ pp.nat (number c))) out (number d)) as [s2 j2].
    destruct K as [E2 [W2 T2]]. cbn in E2, W2, T2. subst j2.
    split; [reflexivity|]. split; [exact W2|]. intro suffix. cbn [fst snd]. rewrite T, T2. finish_text.
  - cbn [build_cached sv.pp_eexpr].
    pose proof (IHa (ind ++ "  ") out c V) as K.
    destruct (build_cached (ind ++ "  ") a out c) as [f d].
    destruct (sv.pp_eexpr (ind ++ "  ") a out (number c)) as [s j].
    destruct K as [E [W T]]. cbn in E, W, T. subst j.
    pose proof (IHb (ind ++ "  ") out d W) as K.
    destruct (build_cached (ind ++ "  ") b out d) as [g d2].
    destruct (sv.pp_eexpr (ind ++ "  ") b out (number d)) as [s2 j2].
    destruct K as [E2 [W2 T2]]. cbn in E2, W2, T2. subst j2.
    split; [reflexivity|]. split; [exact W2|]. intro suffix. cbn [fst snd]. rewrite T, T2. finish_text.
  - cbn [build_cached sv.pp_eexpr]. rewrite (counter_text_correct c V).
    pose proof (IHl ("left_" ++ pp.nat (number c)) ((ind ++ "  ") ++ "  ") out
      (bump c) (bump_valid c V)) as K.
    cbn [number bump] in K.
    destruct (build_cached ((ind ++ "  ") ++ "  ") (kl ("left_" ++ pp.nat (number c)))
      out (bump c)) as [f d].
    destruct (sv.pp_eexpr ((ind ++ "  ") ++ "  ") (kl ("left_" ++ pp.nat (number c)))
      out (S (number c))) as [s j].
    destruct K as [E [W T]]. cbn in E, W, T. subst j.
    pose proof (IHr ("right_" ++ pp.nat (number c)) ((ind ++ "  ") ++ "  ") out d W) as K.
    destruct (build_cached ((ind ++ "  ") ++ "  ") (kr ("right_" ++ pp.nat (number c)))
      out d) as [g d2].
    destruct (sv.pp_eexpr ((ind ++ "  ") ++ "  ") (kr ("right_" ++ pp.nat (number c)))
      out (number d)) as [s2 j2].
    destruct K as [E2 [W2 T2]]. cbn in E2, W2, T2. subst j2.
    split; [reflexivity|]. split; [exact W2|]. intro suffix. cbn [fst snd]. rewrite T, T2. finish_text.
  - cbn [build_cached sv.pp_eexpr]. split; [reflexivity|]. split; [exact V|].
    intro suffix. finish_text.
Qed.

Definition build {t} ind (e : eexpr.eexpr sv.var sv.fn t) out id : builder * nat :=
  let '(f, c) := build_cached ind e out (initial id) in (f, number c).

Theorem build_correct t (e : eexpr.eexpr sv.var sv.fn t) ind out id suffix :
  (fst (build ind e out id) suffix, snd (build ind e out id)) =
  (fst (sv.pp_eexpr ind e out id) ++ suffix, snd (sv.pp_eexpr ind e out id)).
Proof.
  pose proof (build_cached_correct t e ind out (initial id) (initial_valid id)) as K.
  cbn [number initial] in K.
  unfold build. destruct (build_cached ind e out (initial id)) as [f c].
  destruct (sv.pp_eexpr ind e out id) as [s j].
  destruct K as [E [V T]]. cbn in E, T. now rewrite T, E.
Qed.

Definition render {t} ind (e : eexpr.eexpr sv.var sv.fn t) out id : string * nat :=
  let '(f, next) := build ind e out id in (f "", next).

Corollary render_correct t (e : eexpr.eexpr sv.var sv.fn t) ind out id :
  render ind e out id = sv.pp_eexpr ind e out id.
Proof.
  pose proof (build_correct t e ind out id "") as H.
  unfold render. destruct (build ind e out id) as [f next].
  destruct (sv.pp_eexpr ind e out id) as [s j]. cbn in H |- *.
  now rewrite append_empty_r in H.
Qed.

End SVExprDList.
Print Assumptions SVExprDList.build_cached_correct.
Print Assumptions SVExprDList.build_correct.
Print Assumptions SVExprDList.render_correct.

Module SVPrinterDList.
Local Open Scope string_scope.

Lemma append_assoc a b c : (a ++ b) ++ c = a ++ (b ++ c).
Proof. induction a; cbn; congruence. Qed.

Lemma append_nil a : a ++ "" = a.
Proof. induction a; cbn; congruence. Qed.

Definition function_text {a b} (name arg : string)
    (body : sv.var a -> eexpr.eexpr sv.var sv.fn b) : string -> string :=
  fun tail => "function automatic " ++ sv.pp_type b ++ " " ++ name ++ " (" ++ pp.LF ++
    "  input " ++ sv.pp_type a ++ " " ++ arg ++ ");" ++ pp.LF ++
    fst (SVExprDList.build "  " (body arg) name 0) (pp.LF ++ "endfunction" ++ pp.LF ++ tail).

Lemma function_text_correct a b name arg
    (body : sv.var a -> eexpr.eexpr sv.var sv.fn b) tail :
  function_text name arg body tail = sv.pp_fn name arg body ++ tail.
Proof.
  pose proof (f_equal (@fst string nat)
    (@SVExprDList.build_correct b (body arg) "  " name 0
      (pp.LF ++ "endfunction" ++ pp.LF ++ tail))) as H.
  cbn [fst] in H.
  unfold function_text, sv.pp_fn.
  rewrite H.
  repeat rewrite append_assoc.
  reflexivity.
Qed.

Fixpoint functions_text {a b} (fs : fns.fns sv.var sv.fn a b) : string -> string :=
  match fs with
  | fns.Let name arg body rest =>
      fun tail => function_text name arg body ("" ++ pp.LF ++ functions_text (rest name) tail)
  | fns.Ret name arg body => function_text name arg body
  end.

Lemma functions_text_correct a b (fs : fns.fns sv.var sv.fn a b) tail :
  functions_text fs tail = sv.pp_fns fs ++ tail.
Proof.
  revert tail.
  induction fs as [a' b' name arg body rest IH | name arg body]; intro tail.
  - cbn [functions_text sv.pp_fns].
    rewrite function_text_correct, IH.
    repeat rewrite append_assoc.
    reflexivity.
  - apply function_text_correct.
Qed.

Definition preamble := "// Generated from Rocq by Quartz (experimental prototype version)
typedef enum bit { tt } unit; // no zero-size types in SystemVerilog :/

class Pair #(parameter type A, parameter type B);
  typedef struct packed { A fst; B snd; } t;
  static function A fst (t p); return p.fst; endfunction
  static function B snd (t p); return p.snd; endfunction
  static function t mk (A a, B b); return t'{a, b}; endfunction
endclass

class Either #(parameter type A, parameter type B);
  typedef union tagged packed { A left; B right; } t;
  static function t left(A a); return tagged left a; endfunction
  static function t right(B b); return tagged right b; endfunction
endclass".

Definition raw {a b} (fs : fns.fns sv.var sv.fn a b) : string :=
  preamble ++ pp.LF ++ pp.LF ++
  sv.pp_typedefs (pp.topsort (pp.typeannots_fns fs nil)) ++ "" ++ pp.LF ++ functions_text fs "".

Theorem raw_correct a b (fs : fns.fns sv.var sv.fn a b) : raw fs = sv.ppRaw fs.
Proof.
  unfold raw, sv.ppRaw, preamble.
  rewrite functions_text_correct, append_nil.
  reflexivity.
Qed.

Definition render {a b} (fs : fns.fns sv.var sv.fn a b) : string :=
  (match b with
   | type.Unit => "`error ""top-level return type cannot be unit"" " ++ pp.LF
   | _ => ""
   end) ++ raw (fns.rmap
     (fun _ e => expr.unresizesame (expr.unapp0l (expr.unapp0r e)))
     (fun _ => id) (fun a b => id) fs).

Theorem render_correct a b (fs : fns.fns sv.var sv.fn a b) : render fs = sv.pp fs.
Proof. unfold render, sv.pp. rewrite raw_correct. reflexivity. Qed.
End SVPrinterDList.

Print Assumptions SVPrinterDList.function_text_correct.
Print Assumptions SVPrinterDList.functions_text_correct.
Print Assumptions SVPrinterDList.raw_correct.
Print Assumptions SVPrinterDList.render_correct.
