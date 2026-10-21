# Montgomery Ladder Verification

Rocq formalization of the Montgomery ladder, complementary-register protection, and power-side-channel leakage.

## Goal

Prove that the fetch/execute/writeback processor computes the correct Curve25519 scalar-multiplication x-coordinate and produces equal modeled leakage traces for any two secret scalars with the same public input. The intended output is released separately from the leakage trace.

## Files

| File | Contents |
| --- | --- |
| [ladder_math.v](ladder_math.v) | Mathematical ladder definitions, field identities, branching/CSwap equivalence, and loop correctness under an abstract projective specification. |
| [dual_circuit.v](dual_circuit.v) | Field operations on bitvectors, register-machine instructions, complementary-register HW proofs, and a probability-label sketch. |
| [state_machine.v](state_machine.v) | Processor state, instruction encoding, fetch/execute/writeback semantics, arithmetic-cycle correctness, and processor leakage definitions. |
| [ladder_machine.v](ladder_machine.v) | Instruction-level implementation of the full ladder and affine conversion, with correctness and aggregate-register HW proofs. |
| [curve25519.v](curve25519.v) | Connection to Fiat-Crypto's Curve25519 model and the combined instruction-level correctness/security theorem. |
| [two_reg_prob.v](two_reg_prob.v) | Two-register masking experiment using ensembles; the aggregate-HW security statement is unfinished. |
| [montgomery_ladder.v](montgomery_ladder.v) | Convenience imports for the core models. |
| [state_machine_tests.v](state_machine_tests.v), [ladder_machine_tests.v](ladder_machine_tests.v), [curve25519_tests.v](curve25519_tests.v) | Regression examples, assumption checks, register-coverage and latch tests. |
| [check.sh](check.sh), [setup_fiat_crypto.sh](setup_fiat_crypto.sh), [_CoqProject](_CoqProject) | Build configuration and pinned Fiat-Crypto dependency setup. |

## Verified Results

- **Mathematics:** both ladder formulations return `X0([k]P)` for a Curve25519 point `P` and a scalar within the chosen bit width. Zero encodes infinity. The proof uses Fiat-Crypto's curve theory.
- **Processor:** in-bounds instruction encodings round-trip at widths of at least 17 bits. Addition, subtraction, and multiplication compute the correct field result after three cycles. All 32 registers and the execution-result latch remain paired throughout execution, including when the latch is inactive. Their combined HW is always `33 * n` for `n`-bit words; `power_independence` proves equal initial state HW for arbitrary register values and the same instruction memory.
- **Instruction-level model:** `Curve25519Machine.protected_ladder_correct_and_secure` proves full-ladder correctness and a constant aggregate-register HW trace, including affine conversion. This is not yet a theorem about the processor.

These results have checked proofs independent of the remaining admitted declarations. The repository as a whole still contains unfinished proofs.

## Leakage Scope

Complementary registers balance the combined Hamming weight of a value and its bitwise complement. The instruction-level theorem assumes equally weighted bits, atomic paired updates, and observation of the aggregate register HW at instruction boundaries. It assumes the initial pairs are already loaded. It does not establish security for separate register observations, Hamming distance, arithmetic internals, glitches, buses, or physical power.

The processor has its own state-HW observation, including instruction memory, bus payloads, and the execution-result latch, even when inactive. Stage, valid bits, write enable, and the natural-number destination index are not counted. `state_HW_decomposition` proves that a valid state's HW equals the contribution of the program counter, instruction memory, and instruction buses plus `33 * n` from protected storage. Full trace security still requires proving that those public-field observations agree across secrets throughout execution.

The processor models field arithmetic as one Execute-stage operation; it is not a verified RTL implementation. X25519 byte encoding, scalar clamping, and twist inputs are outside the current correctness result.

## To Do

1. Implement scalar-bit handling and swaps in the processor while preserving register and latch protection.
2. Prove the complete ladder and affine conversion directly over processor cycles.
3. Prove equality of the full processor leakage traces across secrets, including their lengths and public control/bus behavior.

## Build

With the configured Rocq environment active:

```sh
bash check.sh
```

The script checks the models and tests and sets up the pinned Fiat-Crypto dependencies. A successful build accepts remaining `Admitted` declarations; the test files also print assumptions for the checked results.
