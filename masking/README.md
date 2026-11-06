# Random masking

This development studies additive shares with Infotheo finite probability distributions. The attacker observes only the designated final share `Y`, not both shares, masks, intermediate values, or an execution trace.

For a secret `s` and a uniform mask `r`, the shares are `(r, s - r)`. Their sum is `s`; either share alone is uniform. Seeing both shares reveals `s`.

Reconstruction is used to state correctness; it is not included in the attacker's observation. For Curve25519, uniform means uniform over the prime field, not over all 255-bit strings.

## Files

- `finite_masking.v`: uniform masking, the equally weighted copies view, reconstruction, share refresh, and output-distribution independence over a finite additive group.
- `word_masking.v`: arbitrary word widths, using arithmetic modulo `2^width` for positive widths and a singleton for zero bits, with explicit two-bit copies examples.
- `shared_ladder.v`: shared arithmetic and the 18-operation LadderStep formula.
- `ladder_distribution.v`: random operation masks, a separate final refresh, and joint distributional security for the four-coordinate vector `Y`.
- `shared_power.v`: shared square-and-multiply and affine conversion, with reconstruction proofs.
- `shared_loop.v`: shared CSwap, the fixed-width loop, final swap, affine conversion, and final-share refresh.
- `fiat_field.v`: MathComp finite-ring structure on Fiat-Crypto's existing field values and operations.
- `ladder_bridge.v`: correspondence with the mathematical LadderStep, full CSwap loop, and exponentiation.
- `masked_curve25519.v`: Curve25519 correctness and final-`Y` distribution independence.
- `tests.v`: small examples, excluded observation models, and assumption checks.
- `curve_tests.v`: zero-width, zero-scalar, 255-bit specialization, and curve-theorem assumption checks.

## Scope

Main results: `WordMasking.every_width_independent`, `SharedLadder.shared_step_correct`, and `MaskedLadder.correct_and_output_independent`. The last theorem combines correct reconstruction with equality of the joint final-output distribution for any two inputs. It uses Infotheo probability distributions, not equality of average Hamming weights.

The generic arithmetic distinguishes word arithmetic modulo `2^width` from Curve25519 arithmetic modulo `2^255 - 19`. `MaskedCurve25519.correct_and_output_independent` connects the shared full loop to Fiat-Crypto: for any curve point `P` and scalars `0 <= k1,k2 < 2^m`, reconstruction returns `X0([ki]P)` and the final share `Y` has the same distribution in both runs. Zero encodes infinity. Affine conversion uses shared exponentiation by `p - 2`, including the zero-denominator case.

Intermediate operations are not covered by the observation theorem. In particular, the shared multiplication formula is not claimed to be a probing-secure or glitch-secure multiplication gadget. Final-output masking does not establish power security for a processor executing the computation.

The LadderStep final refresh uses four independent masks, not one mask reused across coordinates. The complete ladder returns a single affine field value in two shares, followed by a fresh scalar mask. Final refresh establishes output secrecy independently of the preceding computation; the separate correctness proofs establish the intended result. CSwap is an abstract permutation of both shares, not a verified constant-time implementation.

Quartz remains the implementation target. These files contain probability and arithmetic models, not another processor. Refinement to Quartz, randomness delivery, and an observation model covering actual execution remain separate obligations.

## Build

The masking environment is separate from the original and Quartz environments. Versions: Rocq 9.1.0, Stdlib 9.1.0, MathComp 2.6.0, MathComp Analysis 1.19.0, Infotheo 0.9.9.

```sh
bash masking/setup.sh
opam exec --switch="$PWD/.deps/masking-toolchain" -- bash masking/check.sh
```

The build reuses the root's pinned Fiat-Crypto version and curve-only proof module, compiling them under `.deps/masking-curve` to keep the two Stdlib versions' artifacts separate. It also runs `rocqchk` on the combined theorem and tests.

The probability proofs use MathComp's existing propositional extensionality, dependent functional extensionality, and constructive indefinite description axioms. The shared arithmetic/LadderStep correctness proofs are closed under the global context. No new admits or project-specific axioms are introduced; the test files print the assumption reports.

Use this same opam environment for the editor. `masking/_CoqProject` supplies the local load path; the root project's environment does not include Infotheo.
