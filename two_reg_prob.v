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

(* ══════════════════════════════════════════════════════════════════════════════
   Probabilistic Two-Register Model
   - masking a secret register with a fresh uniform random value leaks no information through Hamming-weight side channels.

   Machine: two n-bit registers — r0 (secret, unknown to attacker), r1 (random).
   Ensemble semantics: GenRV forks the current state into 2^n copies, one per possible value of the target register, modelling uniform sampling. 
    The key property is that bv_add secret is a permutation on bv n, so after
      GenRV r1 ; Add r1 r0 r1
   the multiset of r1 values across the ensemble is {0,..,2^n-1} regardless of
   the secret in r0 — the total Hamming weight is therefore constant.
   ══════════════════════════════════════════════════════════════════════════════ *)
Section TwoRegProb.
  Variable n : N.

  (* State - two registers *)
  Record two_state := mk_two_state { r0 : bv n; r1 : bv n }.

  (* Instruction set *)
  (* Register index: false = r0 (secret),  true = r1 (random) *)
  Inductive two_instr :=
    | T_Add   (rd rs1 rs2 : bool)  (* rd ← rs1 + rs2                          *)
    | T_GenRV (rd : bool).         (* rd := uniform random (forks the ensemble) *)

  (* Ensemble: list of equally-probable states *)
  Definition Ensemble := list two_state.

  Definition read_r (s : two_state) (r : bool) : bv n := if r then s.(r1) else s.(r0).

  Definition write_r (s : two_state) (r : bool) (v : bv n) : two_state := if r then mk_two_state s.(r0) v else mk_two_state v s.(r1).

  (* Every n-bit bitvector in order — the range GenRV samples uniformly. *)
  Definition all_bv : list (bv n) := map (fun k => Z_to_bv n (Z.of_nat k)) (seq 0 (Z.to_nat (2 ^ Z.of_N n))).

  
  (* Small-step semantics *)

  (* One instruction on one state produces a list of successor states.
     T_Add is deterministic (singleton list); T_GenRV forks into |all_bv| = 2^n copies *)
  Definition interp_two (s : two_state) (e : two_instr) : list two_state :=
    match e with
    | T_Add rd rs1 rs2 => [write_r s rd (bv_add (read_r s rs1) (read_r s rs2))]
    | T_GenRV rd => map (fun v => write_r s rd v) all_bv
    end.

  (* Lift one step over the full ensemble *)
  Definition step_two (ens : Ensemble) (e : two_instr) : Ensemble := flat_map (fun s => interp_two s e) ens.

  (* Run a program to completion *)
  Fixpoint run_two (ens : Ensemble) (prog : list two_instr) : Ensemble :=
    match prog with
    | []        => ens
    | e :: rest => run_two (step_two ens e) rest
    end.


  (* Security metric *)

  (* Hamming weight of a single bitvector. *)
  Definition HW2 (a : bv n) : nat := fold_left (fun (acc : nat) (b : bool) => if b then (acc + 1)%nat else acc) (bv_to_bits a) 0%nat.

  (* todo: instead of summing over ensemble, state equivalence between distribution of copies. *)
  Definition total_HW_r1 (ens : Ensemble) : nat := fold_left (fun (acc : nat) (s : two_state) => (acc + HW2 s.(r1))%nat) ens 0%nat.

  (* Masking program *)

  (* Step 1: GenRV r1 — fork into 2^n copies, each with a distinct r1 value.
     Step 2: Add r1 r0 r1 — mask r1 with the secret in r0. *)
  Definition mask_prog : list two_instr :=
    [ T_GenRV true               (* r1 := uniform random                       *)
    ; T_Add   true false true ]. (* r1 ← r0 + r1  (mask secret with random)    *)

  (* Key security lemma *)
  (* After mask_prog, total_HW_r1 is the same for any two secrets.
     Proof outline:
       • After T_GenRV: r1 ∈ {0,..,2^n-1} → total_HW = ∑_v HW(v) = n·2^(n-1).
       • T_Add maps r1 ↦ secret + r1; since bv_add secret is a permutation,
         {secret+v | v ∈ all_bv} = all_bv as multisets.
       • Hence total_HW_r1 is unchanged ⟹ independent of secret.            *)
  Lemma mask_security (s1 s2 : bv n) : total_HW_r1 (run_two [mk_two_state s1 (bv_0 n)] mask_prog) = total_HW_r1 (run_two [mk_two_state s2 (bv_0 n)] mask_prog).
  Proof.
    (* Needs: bv_add is a permutation (bv arithmetic) + sum HW over all_bv is constant. *)
  Admitted.

  (* InfoTheo library *)
End TwoRegProb.

(* dual circuit / each module doesn't have full info *)

