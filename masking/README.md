# Random masking

This development studies additive shares with Infotheo finite probability distributions. The attacker observes only the designated final share `Y`, not both shares, masks, intermediate values, or an execution trace.

For a secret `s` and a uniform mask `r`, the shares are `(r, s - r)`. Their sum is `s`; either share alone is uniform. Seeing both shares reveals `s`.

Reconstruction is used to state correctness; it is not included in the attacker's observation.

## Files

- `finite_masking.v`: uniform masking, the equally weighted copies view, reconstruction, share refresh, and output-distribution independence over a finite additive group.
- `word_masking.v`: arbitrary word widths, using arithmetic modulo `2^width` for positive widths and a singleton for zero bits, with explicit two-bit copies examples.
- `shared_ladder.v`: shared arithmetic and the 18-operation LadderStep formula.
- `ladder_distribution.v`: random operation masks, a separate final refresh, and joint distributional security for the four-coordinate vector `Y`.
- `tests.v`: small examples, excluded observation models, and assumption checks.

## Scope

Main results: `WordMasking.every_width_independent`, `SharedLadder.shared_step_correct`, and `MaskedLadder.correct_and_output_independent`. The last theorem combines correct reconstruction with equality of the joint final-output distribution for any two inputs. It uses Infotheo probability distributions, not equality of average Hamming weights.

The generic arithmetic distinguishes word arithmetic modulo `2^width` from Curve25519 arithmetic modulo `2^255 - 19`. Correctness of the shared LadderStep means reconstruction agrees with its unshared arithmetic formula. It does not yet connect this new MathComp representation to the existing Fiat-Crypto curve theorem.

Intermediate operations are not covered by the observation theorem. In particular, the shared multiplication formula is not claimed to be a probing-secure or glitch-secure multiplication gadget. Final-output masking does not establish power security for a processor executing the computation.

The final refresh uses four independent masks, not one mask reused across coordinates. It establishes output secrecy independently of the preceding computation; the separate correctness proof establishes that reconstruction still produces the intended LadderStep result.

Quartz remains the implementation target. These files contain probability and arithmetic models, not another processor. Refinement to Quartz, randomness delivery, and an observation model covering actual execution remain separate obligations.

## Build

The masking environment is separate from the original and Quartz environments. Versions: Rocq 9.1.0, Stdlib 9.1.0, MathComp 2.6.0, MathComp Analysis 1.19.0, Infotheo 0.9.9.

```sh
bash masking/setup.sh
opam exec --switch="$PWD/.deps/masking-toolchain" -- bash masking/check.sh
```

The probability proofs use MathComp's existing propositional extensionality, dependent functional extensionality, and constructive indefinite description axioms. The shared arithmetic/LadderStep correctness proofs are closed under the global context. No new admits or project-specific axioms are introduced; `tests.v` prints the assumption reports.

Use this same opam environment for the editor. `masking/_CoqProject` supplies the local load path; the root project's environment does not include Infotheo.
