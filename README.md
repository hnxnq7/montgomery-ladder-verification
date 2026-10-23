# Montgomery Ladder Verification

Rocq formalization of the Montgomery ladder, complementary-register protection, and power-side-channel leakage.

## Goal

Prove that the fetch/execute/writeback processor computes the correct Curve25519 scalar-multiplication x-coordinate and produces equal modeled leakage traces for any two secret scalars with the same public input. The intended output is released separately from the leakage trace.

## Files

| File | Contents |
| --- | --- |
| [ladder_math.v](ladder_math.v) | Mathematical ladder definitions, field identities, branching/CSwap equivalence, and loop correctness under an abstract projective specification. |
| [dual_circuit.v](dual_circuit.v) | Field operations on bitvectors, register-machine instructions, complementary-register HW proofs, and a probability-label sketch. |
| [state_machine.v](state_machine.v) | Processor state, instruction encoding, fetch/execute/writeback semantics, LadderStep and complete-iteration correctness, and processor leakage proofs. |
| [processor_refinement.v](processor_refinement.v) | Instruction correspondence and full-loop/affine correctness for continuous processor execution. |
| [ladder_machine.v](ladder_machine.v) | Instruction-level implementation of the full ladder and affine conversion, with correctness and aggregate-register HW proofs. |
| [curve25519.v](curve25519.v) | Connection to Fiat-Crypto's Curve25519 model and the combined processor correctness/security theorem. |
| [two_reg_prob.v](two_reg_prob.v) | Two-register masking experiment using ensembles; the aggregate-HW security statement is unfinished. |
| [montgomery_ladder.v](montgomery_ladder.v) | Convenience imports for the core models. |
| [state_machine_tests.v](state_machine_tests.v), [processor_refinement_tests.v](processor_refinement_tests.v), [ladder_machine_tests.v](ladder_machine_tests.v), [curve25519_tests.v](curve25519_tests.v) | Regression examples, assumption checks, register-coverage and latch tests. |
| [check.sh](check.sh), [setup_fiat_crypto.sh](setup_fiat_crypto.sh), [_CoqProject](_CoqProject) | Build configuration and pinned Fiat-Crypto dependency setup. |

## Verified Results

- **Mathematics:** both ladder formulations return `X0([k]P)` for a Curve25519 point `P` and a scalar within the chosen bit width. Zero encodes infinity. The proof uses Fiat-Crypto's curve theory.
- **Processor:** in-bounds instruction encodings round-trip at widths of at least 21 bits. Arithmetic, Copy, GetBit, Xor, and CSwap have checked three-cycle correctness proofs, including aliased operands. All 32 registers and both execution-result latches remain paired throughout execution, including when inactive. Their combined HW is always `34 * n` for `n`-bit words.
- **Processor LadderStep:** `ladder_block_correct` identifies the four output registers after 54 cycles with the mathematical `LadderStep`, for any initial register file, a positive represented modulus, and word widths of at least 21 bits. Scratch registers need not start at zero; `ladder_result_correct` specializes this to the supplied initializer.
- **Processor iteration:** `iteration_correct` proves that a standalone 27-instruction, 81-cycle program implements `MontLadderCSwap_step`, including bit extraction, conditional swaps, and copying coordinates back. It preserves the scalar and public inputs, saves the current bit, and finishes in Fetch at instruction 27. The bit index must be below 256 and the incoming previous-bit register must contain 0 or 1; the same width and modulus requirements apply.
- **Processor leakage:** `processor_trace_independent` proves equal full state-HW traces for arbitrary initial register values, the same instruction memory, and the same cycle budget. The trace includes the initial state and every subsequent cycle; public control and instruction-bus fields remain equal across runs.
- **Full processor program:** `ProcessorRefinement.projective_program_correct` and `ProcessorRefinement.affine_program_correct` prove the initialized loop, final swap, and affine conversion over continuous processor cycles. `run_code_correct` connects shared-memory execution to instruction semantics, with explicit register, bit-index, and program-counter bounds.
- **Combined result:** `Curve25519Processor.protected_ladder_correct_and_secure` proves correct Curve25519 outputs and equal full state-HW traces for any two 255-bit scalars and the same public curve point. The 7,400-instruction program runs for 22,200 cycles; its trace contains 22,201 observations, including the initial state. `program_boundary` places the final state in Fetch at instruction 7,400. The output is read separately after this fixed budget; the model has no halt instruction.

These results have checked proofs independent of the remaining admitted declarations. The repository as a whole still contains unfinished proofs.

## Leakage Scope

Complementary registers balance the combined Hamming weight of a value and its bitwise complement. The instruction-level theorem assumes equally weighted bits, atomic paired updates, and observation of the aggregate register HW at instruction boundaries. It assumes the initial pairs are already loaded. It does not establish security for separate register observations, Hamming distance, arithmetic internals, glitches, buses, or physical power.

The processor has its own state-HW observation, including instruction memory, bus payloads, and both execution-result latches, even when inactive. Stage, valid bits, write enables, and natural-number destination indices are not counted. `state_HW_decomposition` proves that a valid state's HW equals the contribution of the program counter, instruction memory, and instruction buses plus `34 * n` from protected storage. CSwap reads its control and both operands before writing and assumes two atomic paired writes in one WriteBack cycle, regardless of the control value.

The processor models field arithmetic as one Execute-stage operation; it is not a verified RTL implementation. X25519 byte encoding, scalar clamping, and twist inputs are outside the current correctness result.

## To Do

1. Refine the processor into hardware with explicit arithmetic internals and justify or replace the atomic paired-update assumption.
2. Extend the leakage specification if targeting Hamming distance, separate observations, or physical power.
3. Complete the separate random-masking model with distributional security; it is not used by the dual-register processor theorem.

## Build

With the configured Rocq environment active:

```sh
bash check.sh
```

The script checks the models and tests and sets up the pinned Fiat-Crypto dependencies. A successful build accepts remaining `Admitted` declarations; the test files also print assumptions for the checked results.
