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

(* Uniform masking via equally weighted copies. The security proof is unfinished. *)
Section TwoRegProb.
  Variable n : N.

  Record two_state := mk_two_state { r0 : bv n; r1 : bv n }.

  (* false selects r0; true selects r1. *)
  Inductive two_instr :=
    | T_Add   (rd rs1 rs2 : bool)
    | T_GenRV (rd : bool).

  (* Ensemble: list of equally-probable states *)
  Definition Ensemble :=
    list two_state.

  Definition read_r (s : two_state) (r : bool) : bv n :=
    if r then s.(r1) else s.(r0).

  Definition write_r (s : two_state) (r : bool) (v : bv n) : two_state :=
    if r then mk_two_state s.(r0) v else mk_two_state v s.(r1).

  (* Each n-bit value appears once. *)
  Definition all_bv : list (bv n) :=
    map (fun k => Z_to_bv n (Z.of_nat k)) (seq 0 (Z.to_nat (2 ^ Z.of_N n))).

  (* Add has one successor; GenRV forks into 2^n equally weighted successors. *)
  Definition interp_two (s : two_state) (e : two_instr) : list two_state :=
    match e with
    | T_Add rd rs1 rs2 => [write_r s rd (bv_add (read_r s rs1) (read_r s rs2))]
    | T_GenRV rd => map (fun v => write_r s rd v) all_bv
    end.

  (* Lift one step over the full ensemble *)
  Definition step_two (ens : Ensemble) (e : two_instr) : Ensemble :=
    flat_map (fun s => interp_two s e) ens.

  Fixpoint run_two (ens : Ensemble) (prog : list two_instr) : Ensemble :=
    match prog with
    | []        => ens
    | e :: rest => run_two (step_two ens e) rest
    end.

  Definition HW2 (a : bv n) : nat :=
    fold_left (fun (acc : nat) (b : bool) => if b then (acc + 1)%nat else acc) (bv_to_bits a) 0%nat.

  (* TODO: compare HW distributions, not just their sums. *)
  Definition total_HW_r1 (ens : Ensemble) : nat :=
    fold_left (fun (acc : nat) (s : two_state) => (acc + HW2 s.(r1))%nat) ens 0%nat.

  (* r0 holds the secret; r1 receives a fresh mask, then secret + mask. *)
  Definition mask_prog : list two_instr :=
    [ T_GenRV true
    ; T_Add   true false true ].

  (* Equal sums alone do not establish leakage independence. *)
  Lemma mask_security (s1 s2 : bv n) :
    total_HW_r1 (run_two [mk_two_state s1 (bv_0 n)] mask_prog) =
    total_HW_r1 (run_two [mk_two_state s2 (bv_0 n)] mask_prog).
  Proof.
    (* TODO: show that addition by a fixed secret permutes all_bv. *)
  Admitted.

End TwoRegProb.
