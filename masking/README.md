# Random masking

This development studies additive shares with Infotheo finite probability distributions. It proves final-`Y` and refreshed-checkpoint secrecy for the shared ladder, and combined Curve25519 correctness and quantitative aggregate-HW security for actual clocked Quartz execution. The execution result counts all stored controller bits; it is separate from the narrower checkpoint contracts. Secure-instance RTL validation remains open.

For a secret `s` and a uniform mask `r`, the shares are `(r, s - r)`. Their sum is `s`; either share alone is uniform. Seeing both shares reveals `s`.

Reconstruction is used to state correctness; it is not included in the attacker's observation. For Curve25519, uniform means uniform over the prime field, not over all 255-bit strings.

Masking and dual storage use a common quantitative noisy-leakage contract with the same aggregate-HW observer and additive-noise channel. Execution length and repetition limits are explicit. The checkpoint results below are not proofs of this stronger contract. See [the contract and roadmap](../VERIFICATION_NOTES.md#common-noisy-leakage-target).

## Files

- `finite_masking.v`: uniform masking, the equally weighted copies view, reconstruction, share refresh, and output-distribution independence over a finite additive group.
- `word_masking.v`: arbitrary word widths, using arithmetic modulo `2^width` for positive widths and a singleton for zero bits, with explicit two-bit copies examples.
- `shared_ladder.v`: shared arithmetic and the 18-operation LadderStep formula.
- `arithmetic_shares.v`: variable-share-count arithmetic and sequential pairwise multiplication, with reconstruction proofs over any finite commutative ring.
- `arithmetic_control.v`: arithmetic-share XOR and CSwap with explicit multiplication masks; neither reconstructs its control bit. Functional correctness only.
- `arithmetic_ladder.v`: variable-share-count LadderStep using the existing mathematical specification, with reconstruction correctness for arbitrary multiplication masks.
- `arithmetic_privacy.v`: joint privacy when one share is omitted, and random-probe/channel-simulation snapshot bounds.
- `arithmetic_refresh.v`: value-preserving star refresh using exactly one fewer masks than shares; exact canonical-sharing and joint-prior laws with explicit fresh independent draws.
- `arithmetic_bank_refresh.v`: simultaneous independent refresh of every sharing group, with exact joint bank laws preserving arbitrary prior context and correlations among represented values.
- `arithmetic_product_bound.v`: joint independent-product TV bounded by the sum of coordinate TVs.
- `curve_bank_bound.v`: fresh whole-bank HW bounds for arbitrary correlated prior banks, with explicit additive-noise capacity preventing clipping.
- `curve_bank_history.v`: connects a per-state fresh-bank emission contract to execution-derived histories, including an explicit initial observation.
- `quartz_masked_execution.v`: discharges that contract for actual Quartz ticks, retaining the actual controller state and including initialization, arbitrary prior correlations, and independent repeated runs.
- `quartz_masked_budget.v`: at 256 shares, bounds all 8681 observations by TV `2^-66`, and up to `2^32` independent runs by `2^-34`; includes a non-clipping capacity condition and the checked public schedule.
- `quartz_masked_ladder_security.v`: combines those bounds with correct Curve25519 outputs, completion, and canonical storage for the actual randomized controller; compilation and full recursive kernel checking passed.
- `arithmetic_aggregate.v`: exact conditional and tuple-counting laws for canonical arithmetic shares and any whole-vector observation; shares remain dependent under the secret-sum constraint.
- `noisy_common_mass.v`: total-variation bounds from a common channel subdistribution.
- `arithmetic_channel.v`: exact simulation of independent per-share channels by random probing, yielding `(1-alpha)^(n+1)` for `n+1` canonical arithmetic shares when the channel has common mass `alpha`. Includes normalization endpoints; a concrete aggregate-noise instantiation and useful parameters are separate obligations.
- `history_semantics.v`: posterior kernels derived from actual execution, with explicit zero-probability defaults; connects execution traces to the history-weighted TV budget. A small numerical budget remains a separate obligation.
- `arithmetic_noisy_snapshot.v`: exact noisy-channel/probing equality and a `2^-(n+1)` aggregate snapshot bound for `n+1` arithmetic shares with a Boolean-valued observer; specialized to actual F3 HW. It uses one fair noise bit per share, not a fixed total noise budget or a Curve25519 observer.
- `curve_noise_feasibility.py`: exact conditional common-mass certificates at a fixed total noise budget; does not certify the required execution invariant or calibrate physical noise.
- `arithmetic_aggregate_experiment.py`: exact small-modulus aggregate-HW distributions using tuple-count convolution, checked against exhaustive canonical sharing. Snapshot results only, not full execution or Curve25519 bounds.
- `dyadic_phase.v`: exact Curve25519 modular phase-separation lemma for the proposed aggregate Fourier analysis. This is an arithmetic prerequisite, not a leakage bound.
- `cube_spectral.v`: complex unit-circle estimates and a whole-product bound from one separated pair of factors. The actual field-character and aggregate-distribution instantiations remain separate obligations.
- `cube_roots.v`, `cube_bound.v`: a nontrivial-root witness and a uniform `31/32` bound on the rotated binary product.
- `cube_strong_bound.v`: a tighter `3/4` rotated-product bound at width 255, independent of the chosen unit weight-frequency phase.
- `cube_encoding.v`, `cube_field_bound.v`: the weighted binary-product identity, its canonical `Z.testbit` HW interpretation, and a `32/33` coefficient bound after removing the 19 excluded field encodings. Distributional and execution-level bounds remain separate.
- `cyclic_characters.v`: concrete finite-character orthogonality and normalized transform energy for any primitive-root modulus, including composite observation grids.
- `field_coefficient.v`: concrete canonical-HW character coefficients, normalized energy, and an exponentially decreasing share-count spectrum bound. The exact aggregate-distribution identity remains separate.
- `curve_coefficient.v`: the stronger `49/64` coefficient bound and `2*(49/64)^(N-2)` spectrum estimate for the Curve25519 residue range.
- `arithmetic_spectral.v`: conditional coefficient bounds, finite Parseval/Cauchy estimates, and a rational-mass adapter to Infotheo TV. Concrete character orthogonality and the actual HW distribution must still discharge its premises.
- `ladder_distribution.v`: random operation masks, a separate final refresh, and joint distributional security for the four-coordinate vector `Y`.
- `shared_power.v`: shared square-and-multiply and affine conversion, with reconstruction proofs.
- `shared_loop.v`: shared CSwap, the fixed-width loop, final swap, affine conversion, and final-share refresh.
- `trace_masking.v`: joint-trace composition from a state-independent conditional observation law, with execution-state erasure.
- `ladder_trace.v`: instruments the existing loop at refreshed LadderStep boundaries and records final `Y`; erasure recovers the original program.
- `leakage_counterexamples.v`: exhaustive one-bit HW/multiplication counterexamples and a temporal joint-distribution counterexample.
- `aggregate_hw_limit.v`: a distributional obstruction to exact aggregate-HW independence for ordinary additive shares over any finite additive group with a zero-detecting HW function.
- `noisy_leakage.v`: total variation, a common finite observation channel, and quantitative leakage bounds. Infotheo's L1 distance is divided by two.
- `noisy_bit_example.v`: a small encoding comparison with nonwrapping additive noise; not a masked arithmetic circuit or physical-noise calibration.
- `xor_shares.v`: arbitrary positive numbers of XOR shares, with reconstruction and aggregate-HW bounds.
- `noisy_shares.v`: arbitrary-share exponential leakage bounds, explicit share/observation erasure, and extra additive noise.
- `noisy_channel_bridge.v`: exact equality to raw aggregate HW plus independent binomial noise; the dual encoding uses the same scalar channel.
- `quartz_noise_bridge.v`: actual dual-storage Quartz Curve25519 correctness and zero-TV noisy trace security, with explicit channel capacity preventing clipping at every snapshot. Built separately with `check_quartz_noise.sh`.
- `quartz_hw_encoding.v`: exact equality between canonical bit counts and Quartz word, bank, and packed-array HW; checked in the same compatible Quartz/Infotheo build.
- `quartz_masked_hw.v`: actual Quartz bank HW equals decoded field-element HW when every stored word is canonical; arbitrary modulo-equivalent encodings are not interchangeable.
- `noisy_words.v`: independent-bit word snapshots, a 255-bit specialization, and aggregate noisy-HW bounds.
- `noisy_trace.v`: conditional bounds for correlated execution traces and independent repeated runs.
- `noisy_history_budget.v`: trace bounds weighted by history probabilities, rather than a uniform worst-case bound at every history.
- `noisy_tests.v`: exact one-observation comparison, zero-observation and repeated-execution budget checks.
- `field_refresh.v`: complete refreshed output-pair laws for arithmetic operations, including squaring.
- `field_mul_gadget.v`: arithmetic multiplication candidate with independent operand refreshes, reconstruction correctness, and a 17-snapshot stored-state trace.
- `field_linear_gadget.v`: addition/subtraction candidates with reconstruction proofs and six-snapshot stored-state traces.
- `field_mul_leakage.v`: full multiplication-bank HW with independent binomial measurement noise, arbitrary operand beliefs, and correlated squaring inputs.
- `field_history.v`: refreshed-output contracts for arbitrary operand beliefs and conditional output-boundary trace bounds.
- `field_mul_tests.v`: independent refresh laws, aliased squaring, and arithmetic regressions.
- `field_leakage_tests.v`: exact noisy one-bit intermediate counterexample despite final-share uniformity.
- `field_mul_attack_tests.v`: projects the actual complete squaring trace to its first observation and proves a TV lower bound of `3/4` in F2 with two noise bits.
- `field_trace_bound.v`: full operation-trace bounds under an explicit channel-diameter premise; a noise-only baseline, not a masking improvement.
- `arithmetic_experiment.py`: exact small-odd-prime experiments with variable share counts, operand reuse, and observed clearing. Reports projection lower bounds, not a full-trace upper bound or a Rocq theorem.
- `fiat_field.v`: MathComp finite-ring structure on Fiat-Crypto's existing field values and operations.
- `field_characters.v`, `field_aggregate_spectral.v`: concrete Fiat-field characters, exact rational observation masses, and the aggregate generating-function identity with a non-aliasing HW grid.
- `curve_snapshot.v`: actual Infotheo snapshot-TV bounds from those exact masses, including common-channel noise contraction and an explicit epsilon-budget form. This is not a circuit or execution theorem.
- `curve25519_snapshot.v`: direct specialization to Fiat-Crypto's Curve25519 field, with its concrete modulus equality discharged symbolically.
- `curve_snapshot_budget.v`: exact single-snapshot certificates: 128 arithmetic shares give TV at most `2^-40`, and 256 give `2^-88`. These are not full-execution bounds or selected hardware parameters.
- `curve_trace_budget.v`: exact numerical discharge rules for history-conditioned trace bounds, including independent repetitions. Actual controller coverage and observation counts remain premises to prove.
- `ladder_bridge.v`: correspondence with the mathematical LadderStep, full CSwap loop, and exponentiation.
- `masked_curve25519.v`: Curve25519 correctness with final-`Y` and checkpoint-trace distribution independence.
- `tests.v`: small examples, excluded observation models, and assumption checks.
- `curve_tests.v`: zero-width, zero-scalar, 255-bit specialization, and curve-theorem assumption checks.

## Scope

Main results: `WordMasking.every_width_independent`, `SharedLadder.shared_step_correct`, and `MaskedLadder.correct_and_output_independent`. The last theorem combines correct reconstruction with equality of the joint final-output distribution for any two inputs. It uses Infotheo probability distributions, not equality of average Hamming weights.

The generic arithmetic distinguishes word arithmetic modulo `2^width` from Curve25519 arithmetic modulo `2^255 - 19`. `MaskedCurve25519.correct_and_output_independent` connects the shared full loop to Fiat-Crypto: for any curve point `P` and scalars `0 <= k1,k2 < 2^m`, reconstruction returns `X0([ki]P)` and the final share `Y` has the same distribution in both runs. Zero encodes infinity. Affine conversion uses shared exponentiation by `p - 2`, including the zero-denominator case.

`MaskedCurve25519.correct_and_checkpoint_independent` combines the same curve correctness with equality of the entire checkpoint trace distribution. `checkpoint_erasure` proves instrumentation does not change the final-share distribution. The trace includes one refreshed four-coordinate vector per loop iteration and the final affine share; it excludes the initial state, the 18 field operations within each LadderStep, CSwap control, and affine-conversion intermediates. The public width fixes the observation count.

This is not processor power security. Checked one-bit examples distinguish secrets through combined-share HW, unrefreshed multiplication values, and a squaring cross product. `temporal_joint_distinguishes` also shows why uniform individual observations do not imply a secure joint trace. The current multiplication is not a probing-secure or glitch-secure gadget.

The LadderStep final refresh uses four independent masks, not one mask reused across coordinates. The complete ladder returns a single affine field value in two shares, followed by a fresh scalar mask. Final refresh establishes output secrecy independently of the preceding computation; the separate correctness proofs establish the intended result. CSwap is an abstract permutation of both shares, not a verified constant-time implementation.

The foundational files contain probability and arithmetic models, not another processor. The `quartz_masked_*` modules connect them to the actual Quartz controller. Randomness delivery remains an explicit input assumption, not a verified RNG implementation.

## Noisy-Channel Milestone

The single-observation bit example uses the same channel for every encoding: aggregate stored-bit HW plus two independent fair noise bits. Noise is added without wraparound. The proofs calculate exact Infotheo distributions, not only means or variances.

| Encoding | TV between secrets 0 and 1 | Theorem |
| --- | --- | --- |
| Unmasked bit | `1/2` | `NoisyBitExample.plain_TV` |
| Two XOR shares | `1/4` | `NoisyBitExample.masked_TV` |
| Bit and complement | `0` | `NoisyBitExample.dual_TV` |

`masked_reconstruct` checks that the XOR shares encode the intended bit. `masked_laws_distinct` explicitly rules out perfect secrecy for the masked observation. No complementary storage is added to masking.

`NoisyLeakage.channel_TV_contraction` proves that a common finite channel cannot increase TV. `iid_TV_bound` bounds `q` independent executions by `q` times the single-execution distance. `noisy_tests.v` specializes this to a masked upper bound of `q/4` for any two secret bits and zero distance for dual storage. TV is also at most 1; the repeated bound can become uninformative and is not an exact repeated-execution distance.

The parameterized development uses `n=d+1` XOR shares. `NoisyShares.aggregate_TV_bound` gives TV at most `2^-n` with `n+e` independent fair noise bits. `NoisyWords.aggregate_word_TV_bound` gives `w*2^-n` for a `w`-bit snapshot with `w*n+e` noise bits, including `w=255`. Hold total noise fixed when comparing share counts; keeping `e` fixed does not do that.

`NoisyTrace.trace_pair_bound` gives `2*T*epsilon` for two `T`-step runs, provided every step's observation law is within `epsilon` of a common reference for every hidden state. It retains state/observation correlations; callers must supply this stronger premise, not merely a bound on initial marginals.

`NoisyTrace.history_trace_bound` instead requires a bound between the next-observation laws at every shared observation history and gives `T*epsilon`. `HistorySemantics` connects this bound to execution-derived posterior kernels. `QuartzMaskedExecution` discharges the controller's emission contract using fresh whole-bank refresh at every tick; fresh snapshot bounds alone would not suffice.

The XOR construction differs from the additive prime-field implementation. The latter's combined Quartz correctness/security theorem uses 256 shares and capacity `18,408,976 + noise_count <= bound`. It observes stored state only: input buses, combinational/glitch/transition leakage, RNG internals, and separate digital share outputs are excluded. Physical noise calibration and masked-controller RTL validation remain open.

## Arithmetic Operation Traces

The circuit candidates keep arithmetic shares over the field. Multiplication independently refreshes both operands, then uses a fresh mask in its cross-term accumulator. `FieldMulGadget.trace_correct` proves reconstruction for every mask choice, including squaring. Addition and subtraction have the corresponding `FieldLinearGadget.trace_correct` result. These are operation-level models, not a second processor or Quartz implementations.

The common 12-slot bank stores both operands, the current mask, products, accumulator, and outputs. Traces include the initial bank and every modeled write, including partially refreshed inputs and stale temporaries. Multiplication has 17 snapshots; addition/subtraction have six. The multiplication noise model samples three masks once per execution and fresh binomial measurement noise per snapshot. Squaring starts with one sharing copied into both operand slots, not independent initial sharings. Noise addition is proved not to wrap.

`FieldHistory.gadget_history_trace_bound` connects refreshed output-pair laws to the history-composition theorem under an explicit canonical-channel bound. It observes only completed output pairs: it does not establish a bound for the stored-state traces above. `FieldLeakageTests.intermediate_TV` proves that an earlier squaring intermediate in F2 still has TV `1/4` under two fair noise bits, despite uniform final `Y`.

These standalone candidates have no useful full-trace upper bound; the checked Quartz controller uses a different whole-bank refresh schedule. Operand beliefs may contain correlations from earlier observations, but these candidates' scratch slots start at zero. Caller registers, buses, combinational signals, and RNG internals are not covered by their traces. The Boolean snapshot bounds cannot be substituted for an arithmetic-gadget security proof.

The parameterized arithmetic experiment uses pairwise random product corrections without reconstructing the secret. It refreshes the second operand while copying, then clears dead operands and temporaries with each write observed. The number of observations increases with share count. Its exact projection distances are attack lower bounds for the Python model; a smaller lower bound does not prove a smaller full-trace distance. Run `python3 masking/arithmetic_experiment.py --test` and `python3 masking/arithmetic_experiment.py` for exhaustive small-field checks and fixed-noise comparisons. The two-share circuit's initial duplicated operand is already problematic: `FieldMulAttackTests.full_trace_TV_lower_bound` proves distance at least `3/4` for its complete F2 squaring trace with two noise bits. This does not assert an attack on Curve25519.

## Build

The masking environment is separate from the original and Quartz environments. Versions: Rocq 9.1.0, Stdlib 9.1.0, MathComp 2.6.0, MathComp Analysis 1.19.0, Infotheo 0.9.9.

```sh
bash masking/setup.sh
opam exec --switch="$PWD/.deps/masking-toolchain" -- bash masking/check.sh
```

The build reuses the root's pinned Fiat-Crypto version and curve-only proof module, compiling them under `.deps/masking-curve` to keep the two Stdlib versions' artifacts separate. It also runs `rocqchk` on the combined theorem and tests.

For the standalone noisy-leakage development, without rebuilding the curve bridge:

```sh
opam exec --switch="$PWD/.deps/masking-toolchain" -- bash masking/check_noisy.sh
```

The probability proofs use MathComp's existing propositional extensionality, dependent functional extensionality, and constructive indefinite description axioms. The shared arithmetic/LadderStep correctness proofs are closed under the global context. No new admits or project-specific axioms are introduced; the test files print the assumption reports.

For the actual Quartz-to-Infotheo bridge, run `bash masking/check_quartz_noise.sh`. It rebuilds pinned Quartz and Fiat-Crypto sources under the masking toolchain in `.deps/quartz-noise`; compiled artifacts from the separate Quartz environment are not interchangeable. This check includes full recursive kernel validation of `QuartzNoiseBridge.protected_curve_correct_and_noisy_secure`.

The full masked-controller proof stack has a separate source-snapshot check:

```sh
JOBS=1 bash quartz/check_masked_arithmetic.sh --with-ladder-security
```

It includes `QuartzMaskedLadderSecurity.ladder_correct_and_noisy_secure_256`, its full controller dependencies, and layout regressions. The script records source hashes and exact checked targets, then runs a recursive kernel check. All 24 selected targets passed both compilation from fresh sources and recursive checking. RTL validation is a separate gate.

Use this same opam environment for the editor. `masking/_CoqProject` supplies the local load path; the root project's environment does not include Infotheo.
