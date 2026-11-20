From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From quartz.lang Require Import domain Syntax transform.
From LadderQuartz Require Import masked_arithmetic_native masked_controller_native
  masked_controller_rtl_export masked_arithmetic_rtl_export hamming_weight masked_controller_storage.
From Stdlib Require Import String NArith ZArith Bits.
Import Syntax.fn Syntax.type.
Local Open Scope string_scope.
Set Default Timeout 10.

Module ControllerNativeRuntimeLeaves256.
Module D := ControllerNativeBank.
Module RL := RuntimeLoad.
Module C := MaskedControllerRTL.C.
Module B := C.B.
Module M := C.M.
Module A := MaskedArithmeticRTL.
Module H := MaskedArithmeticHierarchy.
Module Core := M.Core.

Definition field_add {var func} := fns.package_global_fns'' var func (@H.field_add).
Definition field_sub {var func} := fns.package_global_fns'' var func (@H.field_sub).
Definition field_mul {var func} := fns.package_global_fns'' var func (@H.field_mul).

Lemma field_add_correct : fns.interp field_add = fn.interp (Core.arithmetic Core.Add).
Proof. reflexivity. Qed.
Lemma field_sub_correct : fns.interp field_sub = fn.interp (Core.arithmetic Core.Sub).
Proof. reflexivity. Qed.
Lemma field_mul_correct : fns.interp field_mul = fn.interp (Core.arithmetic Core.Mul).
Proof. reflexivity. Qed.

Definition anchor256 {var} : fn var M.Word (M.Shares 256) :=
  ltac2:(let c := eval cbv beta iota zeta delta -[Zmod.of_Z type.default] in (@C.anchor var 255) in
    let c := H.hierarchical @controller_anchor c in exact $c).

Ltac2 rec leaf_calls c :=
  let c := Constr.Unsafe.map leaf_calls c in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App head args =>
    if Constr.equal head '(@C.anchor) then
      let v := Array.get args 0 in constr:(@anchor256 $v)
    else c
  | _ => c
  end.

Ltac2 normalize prefix c :=
  let c := eval cbv beta iota zeta delta
    -[Zmod.of_Z type.default M.index_bits M.index_width Core.arithmetic M.get M.put B.get B.put
      C.anchor A.static_refresh] in $c in
  let c := leaf_calls c in
  H.hierarchical prefix c.

Definition operand256 {var} : fn var (Pair (C.Bank 255) (Bits 9)) (M.Shares 256) :=
  ltac2:(let c := normalize @controller_operand constr:(@C.read_operand var 255) in exact $c).
Definition decode256 {var} : fn var C.Control C.Instruction :=
  ltac2:(let c := normalize @controller_decode constr:(@C.decode var) in exact $c).
Definition collect256 {var} : fn var (C.Bank 255) (C.Bank 255) :=
  ltac2:(let c := normalize @controller_collect constr:(@C.collect var 255) in exact $c).
Definition control256 {var} : fn var (Pair C.Control (Pair Bool Bool)) C.Control :=
  ltac2:(let c := normalize @controller_control constr:(@C.next_control var) in exact $c).
Definition ready256 {var} : fn var (C.State 255) Bool :=
  ltac2:(let c := normalize @controller_ready constr:(@C.ready var 255) in exact $c).
Definition output256 {var} : fn var (C.State 255) (M.Shares 256) :=
  ltac2:(let c := normalize @controller_output constr:(@C.output var 255) in exact $c).

Definition operand {var func} := fns.package_global_fns'' var func (@operand256).
Definition anchor {var func} := fns.package_global_fns'' var func (@anchor256).
Definition load {var func}
    (add : func (Pair M.Word M.Word) M.Word)
    (anchor : func M.Word (M.Shares 256)) : fns.fns var func C.Load (C.Bank 255) :=
  RL.library 255 add anchor.
Definition decode {var func} := fns.package_global_fns'' var func (@decode256).
Definition collect {var func} := fns.package_global_fns'' var func (@collect256).
Definition control {var func} := fns.package_global_fns'' var func (@control256).
Definition refresh {var func} (add sub : func (Pair M.Word M.Word) M.Word) :
    fns.fns var func (Pair (C.Bank 255) (C.Coins 255)) (C.Bank 255) :=
  D.library 255 C.groups add sub.
Definition ready {var func} := fns.package_global_fns'' var func (@ready256).
Definition output {var func} := fns.package_global_fns'' var func (@output256).

Lemma operand_correct : fns.interp operand = fn.interp (C.read_operand 255).
Proof. reflexivity. Qed.
Lemma anchor_correct : fns.interp anchor = fn.interp (C.anchor 255).
Proof. reflexivity. Qed.
Lemma load_correct p :
  fns.interp (load (fn.interp (Core.arithmetic Core.Add)) (fn.interp (C.anchor 255))) p =
  fn.interp (C.load_bank 255) p.
Proof. apply RL.library_correct. Qed.
Lemma decode_correct : fns.interp decode = fn.interp C.decode.
Proof. reflexivity. Qed.
Lemma collect_correct : fns.interp collect = fn.interp (C.collect 255).
Proof. reflexivity. Qed.
Lemma control_correct : fns.interp control = fn.interp C.next_control.
Proof. reflexivity. Qed.
Lemma refresh_correct a r :
  fns.interp (refresh (fn.interp (Core.arithmetic Core.Add))
    (fn.interp (Core.arithmetic Core.Sub))) (a,r) = fn.interp (B.refresh 255 C.groups) (a,r).
Proof. apply D.library_correct. Qed.
Lemma ready_correct : fns.interp ready = fn.interp (C.ready 255).
Proof. reflexivity. Qed.
Lemma output_correct : fns.interp output = fn.interp (C.output 255).
Proof. reflexivity. Qed.

End ControllerNativeRuntimeLeaves256.
Print Assumptions ControllerNativeRuntimeLeaves256.field_add_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.field_sub_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.field_mul_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.operand_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.anchor_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.load_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.decode_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.collect_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.control_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.refresh_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.ready_correct.
Print Assumptions ControllerNativeRuntimeLeaves256.output_correct.

Module ControllerNativeSafeLeaves256.
Module L := ControllerNativeRuntimeLeaves256.
Module A := L.A.
Module C := L.C.
Module Core := L.Core.

(* Sanitize each closed leaf before composing the controller library. *)

Definition field_add {var func} := A.safe_names (@L.field_add var func).

Lemma field_add_sanitized p : fns.interp field_add p = fns.interp L.field_add p.
Proof. reflexivity. Qed.

Lemma field_add_correct p : fns.interp field_add p = fn.interp (Core.arithmetic Core.Add) p.
Proof. rewrite field_add_sanitized. rewrite L.field_add_correct. reflexivity. Qed.

Definition field_sub {var func} := A.safe_names (@L.field_sub var func).

Lemma field_sub_sanitized p : fns.interp field_sub p = fns.interp L.field_sub p.
Proof. reflexivity. Qed.

Lemma field_sub_correct p : fns.interp field_sub p = fn.interp (Core.arithmetic Core.Sub) p.
Proof. rewrite field_sub_sanitized. rewrite L.field_sub_correct. reflexivity. Qed.

Definition field_mul {var func} := A.safe_names (@L.field_mul var func).

Lemma field_mul_sanitized p : fns.interp field_mul p = fns.interp L.field_mul p.
Proof. reflexivity. Qed.

Lemma field_mul_correct p : fns.interp field_mul p = fn.interp (Core.arithmetic Core.Mul) p.
Proof. rewrite field_mul_sanitized. rewrite L.field_mul_correct. reflexivity. Qed.

Definition operand {var func} := A.safe_names (@L.operand var func).

Lemma operand_sanitized p : fns.interp operand p = fns.interp L.operand p.
Proof. reflexivity. Qed.

Lemma operand_correct p : fns.interp operand p = fn.interp (C.read_operand 255) p.
Proof. rewrite operand_sanitized. rewrite L.operand_correct. reflexivity. Qed.

Definition anchor {var func} := A.safe_names (@L.anchor var func).

Lemma anchor_sanitized p : fns.interp anchor p = fns.interp L.anchor p.
Proof. reflexivity. Qed.

Lemma anchor_correct p : fns.interp anchor p = fn.interp (C.anchor 255) p.
Proof. rewrite anchor_sanitized. rewrite L.anchor_correct. reflexivity. Qed.

Definition decode {var func} := A.safe_names (@L.decode var func).

Lemma decode_sanitized p : fns.interp decode p = fns.interp L.decode p.
Proof. reflexivity. Qed.

Lemma decode_correct p : fns.interp decode p = fn.interp (C.decode) p.
Proof. rewrite decode_sanitized. rewrite L.decode_correct. reflexivity. Qed.

Definition collect {var func} := A.safe_names (@L.collect var func).

Lemma collect_sanitized p : fns.interp collect p = fns.interp L.collect p.
Proof. reflexivity. Qed.

Lemma collect_correct p : fns.interp collect p = fn.interp (C.collect 255) p.
Proof. rewrite collect_sanitized. rewrite L.collect_correct. reflexivity. Qed.

Definition control {var func} := A.safe_names (@L.control var func).

Lemma control_sanitized p : fns.interp control p = fns.interp L.control p.
Proof. reflexivity. Qed.

Lemma control_correct p : fns.interp control p = fn.interp (C.next_control) p.
Proof. rewrite control_sanitized. rewrite L.control_correct. reflexivity. Qed.

Definition ready {var func} := A.safe_names (@L.ready var func).

Lemma ready_sanitized p : fns.interp ready p = fns.interp L.ready p.
Proof. reflexivity. Qed.

Lemma ready_correct p : fns.interp ready p = fn.interp (C.ready 255) p.
Proof. rewrite ready_sanitized. rewrite L.ready_correct. reflexivity. Qed.

Definition output {var func} := A.safe_names (@L.output var func).

Lemma output_sanitized p : fns.interp output p = fns.interp L.output p.
Proof. reflexivity. Qed.

Lemma output_correct p : fns.interp output p = fn.interp (C.output 255) p.
Proof. rewrite output_sanitized. rewrite L.output_correct. reflexivity. Qed.

End ControllerNativeSafeLeaves256.
Print Assumptions ControllerNativeSafeLeaves256.field_add_correct.
Print Assumptions ControllerNativeSafeLeaves256.field_sub_correct.
Print Assumptions ControllerNativeSafeLeaves256.field_mul_correct.
Print Assumptions ControllerNativeSafeLeaves256.operand_correct.
Print Assumptions ControllerNativeSafeLeaves256.anchor_correct.
Print Assumptions ControllerNativeSafeLeaves256.decode_correct.
Print Assumptions ControllerNativeSafeLeaves256.collect_correct.
Print Assumptions ControllerNativeSafeLeaves256.control_correct.
Print Assumptions ControllerNativeSafeLeaves256.ready_correct.
Print Assumptions ControllerNativeSafeLeaves256.output_correct.

Module MaskedControllerNativeExport.
Module C := ControllerNativeContexts.C.
Module M := ControllerNativeContexts.M.
Module R := ControllerNativeContexts.R.
Module Core := ControllerNativeContexts.Core.

Definition with_maps {var func} n
    (operand : func (Pair (C.Bank n) (Bits 9)) (M.Shares (S n)))
    (load : func C.Load (C.Bank n))
    (decode : func C.Control C.Instruction)
    (collect : func (C.Bank n) (C.Bank n))
    (control : func (Pair C.Control (Pair Bool Bool)) C.Control)
    (refresh : func (Pair (C.Bank n) (C.Coins n)) (C.Bank n))
    (ready : func (C.State n) Bool)
    (output : func (C.State n) (M.Shares (S n)))
    (field_add field_sub : func (Pair M.Word M.Word) M.Word)
    (mul : func (ControllerNativeContexts.MulInput n) (M.Shares (S n))) :
    fns.fns var func (C.Input n) (R.Response n) :=
  fns.Let "shared_add" "request" (RuntimeSafeLibraries.diagonal_body (S n) field_add) (fun add =>
  fns.Let "shared_sub" "request" (RuntimeSafeLibraries.diagonal_body (S n) field_sub) (fun sub =>
    ControllerNativeSafe.assemble n operand load decode collect control refresh ready output add sub mul)).

Lemma with_maps_correct n operand load decode collect control refresh ready output field_add field_sub mul
    (Hop : forall x, operand x = fn.interp (C.read_operand n) x)
    (Hl : forall x, load x = fn.interp (C.load_bank n) x)
    (Hd : forall x, decode x = fn.interp C.decode x)
    (Hc : forall x, collect x = fn.interp (C.collect n) x)
    (Hctl : forall x, control x = fn.interp C.next_control x)
    (Hrefresh : forall x, refresh x = fn.interp (C.B.refresh n C.groups) x)
    (Hr : forall x, ready x = fn.interp (C.ready n) x)
    (Ho : forall x, output x = fn.interp (C.output n) x)
    (Ha : forall x, field_add x = fn.interp (Core.arithmetic Core.Add) x)
    (Hs : forall x, field_sub x = fn.interp (Core.arithmetic Core.Sub) x)
    (Hm : forall x, mul x = fn.interp (M.multiply (S n)) x) p :
  fns.interp (with_maps n operand load decode collect control refresh ready output
    field_add field_sub mul) p = fn.interp (R.cycle n) p.
Proof.
  cbn [with_maps fns.interp].
  apply ControllerNativeSafe.assemble_correct; try assumption.
  - intro x. apply RuntimeSafeLibraries.map_body_correct. exact Ha.
  - intro x. apply RuntimeSafeLibraries.map_body_correct. exact Hs.
Qed.

Definition linked {var func} : fns.fns var func (C.Input 255) (R.Response 255) :=
  ControllerFnsLink.link ControllerNativeSafeLeaves256.field_add (fun field_add =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.field_sub (fun field_sub =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.field_mul (fun field_mul =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.operand (fun operand =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.anchor (fun anchor =>
  ControllerFnsLink.link (RuntimeSafeLoad.load_library 255 field_add anchor) (fun load =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.decode (fun decode =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.collect (fun collect =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.control (fun control =>
  ControllerFnsLink.link (RuntimeSafeLibraries.refresh_library 255 field_add field_sub) (fun share_refresh =>
  ControllerFnsLink.link (ControllerNativeSafe.bank_library 255 C.groups share_refresh) (fun refresh =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.ready (fun ready =>
  ControllerFnsLink.link ControllerNativeSafeLeaves256.output (fun output =>
  ControllerFnsLink.link (RuntimeSafeLibraries.arithmetic_library 256 field_add field_sub field_mul)
    (fun multiply => with_maps 255 operand load decode collect control refresh ready output
      field_add field_sub multiply)))))))))))))).

Theorem linked_correct p : fns.interp linked p = fn.interp (R.cycle 255) p.
Proof.
  unfold linked. repeat rewrite ControllerFnsLink.link_interp.
  apply with_maps_correct.
  - intro x. apply ControllerNativeSafeLeaves256.operand_correct.
  - intro x. apply RuntimeSafeLoad.load_library_contract.
    + intro y. apply ControllerNativeSafeLeaves256.field_add_correct.
    + intro y. apply ControllerNativeSafeLeaves256.anchor_correct.
  - intro x. apply ControllerNativeSafeLeaves256.decode_correct.
  - intro x. apply ControllerNativeSafeLeaves256.collect_correct.
  - intro x. apply ControllerNativeSafeLeaves256.control_correct.
  - intros [a r]. apply ControllerNativeSafe.bank_library_correct.
    intro x. apply RuntimeSafeLibraries.refresh_library_contract.
    + intro y. apply ControllerNativeSafeLeaves256.field_add_correct.
    + intro y. apply ControllerNativeSafeLeaves256.field_sub_correct.
  - intro x. apply ControllerNativeSafeLeaves256.ready_correct.
  - intro x. apply ControllerNativeSafeLeaves256.output_correct.
  - intro x. apply ControllerNativeSafeLeaves256.field_add_correct.
  - intro x. apply ControllerNativeSafeLeaves256.field_sub_correct.
  - intro x. apply RuntimeSafeLibraries.arithmetic_library_contract.
    + intro y. apply ControllerNativeSafeLeaves256.field_add_correct.
    + intro y. apply ControllerNativeSafeLeaves256.field_sub_correct.
    + intro y. apply ControllerNativeSafeLeaves256.field_mul_correct.
Qed.

Fixpoint entry_name {var func a b} (name : string) (fs : fns.fns var func a b) :=
  match fs with
  | @fns.Let _ _ _ _ _ _ hint arg body rest =>
      fns.Let hint arg body (fun f => entry_name name (rest f))
  | @fns.Ret _ _ _ _ _ arg body => fns.Ret name arg body
  end.

Lemma entry_name_correct a b name (fs : fns.fns type.interp type.interpfn a b) :
  fns.interp (entry_name name fs) = fns.interp fs.
Proof. induction fs; cbn [entry_name fns.interp]; auto. Qed.

Definition native256 {var func} : fns.fns var func (C.Input 255) (R.Response 255) :=
  MaskedArithmeticHierarchy.unique_functions 0%N (entry_name "cycle256" (@linked var func)).

Theorem native256_correct p : fns.interp native256 p = fn.interp (R.cycle 255) p.
Proof.
  unfold native256. rewrite MaskedArithmeticHierarchy.unique_functions_correct. rewrite entry_name_correct.
  apply linked_correct.
Qed.

Corollary native256_next p : fst (fns.interp native256 p) = fn.interp (C.tick 255) p.
Proof. rewrite native256_correct. apply R.cycle_next. Qed.

Corollary native256_ready p :
  fst (snd (fns.interp native256 p)) = fn.interp (C.ready 255) (fst p).
Proof. rewrite native256_correct. apply R.cycle_ready. Qed.

Corollary native256_output p :
  snd (snd (fns.interp native256 p)) = fn.interp (R.gated_output 255) (fst p).
Proof. rewrite native256_correct. apply R.cycle_output. Qed.

Corollary native256_packed_next p :
  @transform.type.pack (C.State 255) (fst (fns.interp native256 p)) =
  @transform.type.pack (C.State 255) (fn.interp (C.tick 255) p).
Proof. rewrite native256_next. reflexivity. Qed.

Corollary native256_storage p :
  RegisterHW.word_HW (@transform.type.pack (C.State 255) (fst (fns.interp native256 p))) =
  MaskedControllerStorage.state_HW 255 (fn.interp (C.tick 255) p).
Proof. rewrite native256_correct. apply R.cycle_storage. Qed.

End MaskedControllerNativeExport.
Print Assumptions MaskedControllerNativeExport.native256_correct.
Print Assumptions MaskedControllerNativeExport.native256_next.
Print Assumptions MaskedControllerNativeExport.native256_ready.
Print Assumptions MaskedControllerNativeExport.native256_output.
Print Assumptions MaskedControllerNativeExport.native256_packed_next.
Print Assumptions MaskedControllerNativeExport.native256_storage.
