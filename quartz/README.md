# Quartz Integration

This integration reuses `mit-plv/quartz` at commit `7db2fa703550655e0c578607da42bc3a63c37307`, including the processor in `examples/Processor.v`. The dedicated Quartz ladder controller has a Curve25519 correctness proof; full execution through the CPU/MMIO interface and RTL refinement remain open.

## Checked Components

- `field_words.v`: eight native 32-bit words represent a Curve25519 field element without loss (`Curve25519Words.field_roundtrip`). This is a representation proof, not a field-arithmetic implementation.
- `memory.v`: an executable environment around Quartz's actual CPU interface, instruction queues, and data-memory queues. Requests are serviced before the next CPU tick when the response queue has room. Scratch memory is a bounded word list; out-of-range reads return zero and writes are ignored. Programs must separately establish aligned, in-bounds, public addresses.
- `constant_time_multiplier.patch`: removes Quartz's zero-operand early completion. Multiplication now waits for the counter regardless of operands.
- `processor_tests.v`: proves one-step multiplier readiness depends only on its control flags and counter (`ready_tick_independent`); checks zero/nonzero latency and products; executes ADDI, MUL, SW, and LW through the actual Quartz pipeline (`native_cpu_multiply_store_load`).

The new proofs contain no admits or additional axioms. Tests check functionality and one multiplier control property, not whole-processor leakage security.

## Dedicated Accelerator

`accelerator.v` implements an 18-cycle LadderStep datapath directly in Quartz's typed DSL, independently of the 32-bit CPU software path. It uses 255-bit field storage, explicit 512-bit arithmetic, three pseudo-Mersenne folds, and a final conditional subtraction. Multiplication is combinational in this model; 18 ticks is not a measured hardware timing result. No opaque field-operation axioms are introduced.

- `tick_phase_independent` and `run_phase_independent`: control-phase evolution is independent of the entire data bank.
- `ready_after_step`: every initialized input finishes after 18 ticks.
- `accelerator_tests.v`: boundary arithmetic/reduction tests, four LadderStep vectors against an independent integer formula, readiness checks, and `completed_state_stable`.
- `accelerator_correctness.v`: universal correctness of the actual DSL reduction for every 512-bit input, all field operations for every pair of 255-bit operands, and the complete 18-tick LadderStep.
- `accelerator_ladder_bridge.v`: `ladder_step_matches_math` connects the accelerator to the existing `ladder_math.LadderStep` for canonical field inputs.
- `accelerator_correctness_tests.v`: full-width reduction, subtraction and multiplication regressions, LadderStep examples, and assumption checks.
- `accelerator_leakage.v`: explicit aggregate bank-HW observation and canonical input states with identical control phases but different initial bank HW.
- `hamming_weight.v`: word and vector HW-complement identities for Quartz's bitvectors.
- `protected_accelerator.v`: actual DSL complementary storage, paired start/reset/tick updates, and core-erasure proofs.
- `protected_accelerator_security.v`: LadderStep correctness and equal register-HW traces, including the public phase. Valid paired data banks contribute exactly 8160 HW.
- `accelerator_cpu_security.v`: preservation of device pairing through the existing native CPU/MMIO adapter.
- `protected_accelerator_tests.v`: initial/reset HW, trace length, protected-input equality, and CPU-run device-bank checks.

`start` accepts five 255-bit coordinates and clears scratch storage (`start_initial`). A new start replaces an active request; callers must serialize requests. `reset` clears all storage and enters a non-ready idle phase (`reset_clears`, `reset_is_idle`). Read outputs only when `ready` holds; completed states retain their output. The host-side `initial` truncates integers to 255 bits, so curve-level callers must establish canonical input bounds. Outputs are slots 19/23 (doubling) and 16/18 (differential addition).

`accelerator_cpu.v` connects the protected device to the actual `Processor.v` CPU through its existing MMIO port, with no CPU source changes. `accelerator_cpu_tests.v` executes native stores and loads to start a LadderStep and copy its result to RAM (`native_cpu_accelerator_step`). The environment services instruction/data memory using the existing adapter, advances the device each cycle, and retains an MMIO response until the CPU can accept it. This host-side environment is executable Rocq, not yet synthesized bus logic.

The MMIO base is `0x1000`; offsets below are bytes. Only aligned accesses are accepted; other reads return zero and other writes are ignored.

| Offset | Meaning |
| --- | --- |
| 0..159 | Five input coordinates, each eight little-endian 32-bit words |
| 160 | Write 1 to start, 0 to reset (also clears input staging) |
| 164 | Read completion status: 0 or 1 |
| 168..295 | Four result coordinates, each eight little-endian words; zero until ready |

Input writes alter staging only, not an active computation. Start replaces an active request using a snapshot of staging. The top bit of each 256-bit input slot is truncated; callers must supply canonical field elements. Completed output remains available until start/reset. No input or output marshaling correctness theorem is claimed yet.

The original core alone is unprotected: `initial_bank_HW_distinguishes` refutes bank-HW independence over arbitrary canonical coordinate inputs despite fixed scheduling. This is not a proved attack on two full scalar executions. The protected wrapper stores complements of all 32 data words. Its aggregate-register-HW theorem assumes valid initialization, equal initial public phase, equally weighted bits, and atomic paired updates at tick boundaries. Reset pairs zero main words with all-one complements; an all-zero default state is not valid. Combinational intermediates, glitches, Hamming distance, CPU registers, staging RAM, and interface queues are outside this theorem.

## Full Ladder Controller

`ladder_controller.v` implements the 255-bit scalar loop, final swap, and affine conversion in Quartz's DSL. Each iteration invokes the actual 18-tick datapath. Projective evaluation takes 5101 ticks; the fixed square/multiply conversion takes another 511 ticks. These are model cycles, not measured hardware latency.

- `LadderController.projective_refines_cswap`: the complete projective execution matches the mathematical CSwap ladder.
- `LadderController.affine_refines_power`: affine conversion computes the field inverse using exponent `p-2`, including zero-denominator behavior.
- `LadderControllerCurveBridge.controller_curve25519_correct`: after 5612 ticks, the output is the x-coordinate of scalar multiplication in Fiat-Crypto's Curve25519 model, with zero encoding infinity.

`controller_protection.v` pairs every stored controller field, including the scalar, previous-bit flag, coordinates, affine accumulator, and accelerator scratch. `state_HW_storage` connects packed HW to the sum over actual fields using `packed_storage.v`; `trace_independent` covers the initial state and every tick, including retained output storage. The assumptions remain equally weighted stored bits and atomic paired updates, excluding combinational and interface leakage. Output-value release is not part of this power observer.

`ControllerProtection.protected_ladder_correct_and_secure` combines correct Curve25519 outputs for two scalars with equal 5612-tick protected traces. The trace contains 5613 observations, including initialization. This is the dedicated circuit theorem, not the CPU/MMIO or generated-RTL theorem.

The internal `output` accessor reads the affine accumulator even before readiness. A hardware interface must gate pre-ready output; the stored-HW theorem does not protect an unmodeled output bus. Likewise, complementary storage does not make transition/Hamming-distance leakage constant.

## Remaining Work

1. Prove CPU/MMIO marshaling and execution correspondence for the full controller.
2. Define leakage and public equivalence across CPU, accelerator, and memory interfaces; protect secret-bearing data throughout that scope.
3. Prove relational leakage-trace independence and validate the synthesized datapath and bus integration.

Quartz's example uses 32-bit arithmetic and a restricted instruction subset. The existing project's 255-bit atomic-field processor theorems do not automatically transfer. Initial RAM contents, output release, address bounds, and leakage from inactive buffers require explicit treatment.

## RTL Validation

`rtl_export.v` exports the protected LadderStep through Quartz's native SystemVerilog printer. `export_rtl.sh` retains the raw output and checks that simulator compatibility changes only remove an unused helper and introduce reversible type aliases. It then runs `rtl_smoke.sv` with Verilator 5.054.

```sh
bash quartz/export_rtl.sh
```

The testbench uses an independent 512-bit modular-arithmetic reference. It checks 30 cases, including field boundaries, deterministic random inputs, and restart while busy: 552 tick/output comparisons, 657 complement/HW boundaries, and three reset/idle scenarios. Logs and emitted files are under `.deps/quartz-rtl`. `--emit-only` skips validation.

`controller_rtl_export.v` extends the export to the complete protected controller. `native_circuit_correct` proves that static function packaging and name sanitization preserve the Quartz clock-transition semantics. `output_before_ready` gates the external result until completion; reset creates a valid paired idle state.

```sh
bash quartz/export_controller_rtl.sh
```

`controller_rtl_smoke.sv` passed ten complete 5612-clock cases against an independent branching-ladder and modular-power reference, with 66568 control/gating checks and 66625 whole-state complement/HW checks. It also checks busy restarts during both projective and affine execution, reset, changed input pins, and retained outputs. Artifacts and logs are under `.deps/quartz-controller-rtl`.

The reviewed clock wrapper stores exactly `ControllerProtection.State` in `state_q`. Each rising edge stores `cycle.next_device`, matching `cycle_next`: reset has priority over start, otherwise one protected tick executes. `ready` and the gated result describe the current stored state, not the next state. Tests compare the native packed layout with Quartz's actual pack function. The protected observation interval begins with a completed reset/start edge; uninitialized power-up state is not a valid paired state.

This meets the generation-and-validation milestone under an explicit trust boundary: the SystemVerilog printer, reversible simulator compatibility edits, handwritten clock wrapper, and simulator are trusted. The proof reaches the pre-printer Quartz functions; simulation supplies bounded RTL evidence. Formal printer/wrapper equivalence, synthesis-preservation checks, and physical validation are optional stronger assurance, not claims established here.

## Arithmetic-Shared Implementation

- `masked_arithmetic.v`: actual Quartz addition, subtraction, pairwise masked multiplication, and refresh; functional refinement and canonical-output proofs.
- `masked_ladder.v`: shared XOR, CSwap, and LadderStep; checked functional refinement without reconstructing secret control bits. The combinational LadderStep is a reference, not a replacement for observing clocked intermediates.
- `masked_bank.v`: simultaneous refresh of every sharing group, with exact decoded correspondence and canonicality preservation.
- `masked_controller.v`: clocked field-operation schedule, shared scalar-bit storage, and refresh on reset, idle, and done edges.
- `masked_controller_schedule.v`: checked public-control schedule: 8680 clock edges from initialization through affine completion, or 8681 observations including the initial state.
- `masked_controller_storage.v`: packed-state HW equals public-control HW plus every bank word; includes a raw-HW capacity bound and relational public-control independence.
- `masked_controller_program.v`: checked field-level meaning of the controller's actual microinstructions, LadderStep and swaps, with lossless instruction-encoding bounds. The clock-by-clock correspondence is a separate obligation.
- `masked_controller_functional.v`, `masked_controller_tick_program.v`: actual load, operand, and collection reconstruction; checked 32-clock iteration and 8-clock final-swap correspondence with the instruction-refinement premise discharged.
- `masked_controller_loop.v`, `masked_controller_curve.v`: complete actual loop and affine conversion, with correct reconstructed Curve25519 output for every scalar `0 <= k < 2^255`.
- `../masking/quartz_masked_bank_security.v`: checked correspondence between actual Quartz refresh observations and the finite-distribution bound, including public-control HW and unclipped noise.
- `../masking/quartz_masked_execution.v`, `quartz_masked_budget.v`: actual full-state execution bounds, including initialization and repeated runs. At 256 shares, 8681 samples have TV at most `2^-66`; up to `2^32` independent runs have TV at most `2^-34`.
- `../masking/quartz_masked_ladder_security.v`: combined Curve25519 correctness, readiness, canonical storage, and noisy-trace security for the actual randomized controller. Compilation and full recursive kernel checking passed.
- `masked_controller_layout_tests.v`: checked pair/array/control packing and certified-instance storage/randomness-interface sizes.
- `masked_arithmetic_rtl_export.v`: semantics-preserving static specialization and native packaging. Small-instance export validation does not certify a full secure controller instance.
- `masked_controller_rtl_export.v`: checked clock interface using the actual controller tick, current-state readiness, and gated shared output.
- `masked_arithmetic_native.v`, `masked_controller_native.v`, `masked_controller_native_export.v`: native function packaging and preservation proofs for the complete 256-share controller (`MaskedControllerNativeExport.native256_correct`). Compilation and full recursive kernel checking passed; generated RTL validation remains open.
- `sv_printer.v`: cached decimal counters and difference-list string assembly, with exact output equality to Quartz's printer (`SVPrinterDList.render_correct`). Compilation and full recursive kernel checking passed; full-size RTL printing remains to be validated.
- `controller_native_validate.py`, `controller_native_adapter.py`, `controller_native_signature.py`: bounded export/simulation checks, reversible printer compatibility changes, and port-width checks against the emitted types. Signature-only checks do not validate controller execution.

The selected leakage model observes all modeled stored state at clock boundaries. Raw input buses, combinational signals, switching, glitches, and Hamming-distance leakage are outside it. Output shares are not separate digital observations. Fresh uniform field coins are explicit inputs, not a verified RNG implementation.

Remaining: validate the corresponding 256-share RTL. The masking proof environment is distinct from the base Quartz switch below; `check_masked_arithmetic.sh --with-ladder-security` passed a fresh-source build and full recursive kernel check of all 24 selected targets. The narrower bank-security target does not include the full-execution modules.

The full-size optimized print stopped with a Rocq stack overflow before emitting RTL. No 256-share RTL simulation has run. `masked_controller_native_print.v` and `prepare_masked_controller_export.py` retain the full-instance export entry point and bounded-run preparation. `record_kernel_evidence.py` records checked targets and input hashes; wiring it into the source-build script remains pending. The new common-budget comparison compiles, but its recursive recheck stopped at the memory-pressure guard. The expanded combined build has not yet been rerun end to end.

## Build

Use a separate switch so the existing project's toolchain remains unchanged:

```sh
opam switch create "$PWD/.deps/quartz-toolchain" ocaml-base-compiler.5.3.0 --no-switch -y
opam install --switch="$PWD/.deps/quartz-toolchain" dune.3.21.1 rocq-core.9.1.0 rocq-stdlib.9.1.0 coq-core.9.1.0 -y
opam exec --switch="$PWD/.deps/quartz-toolchain" -- bash quartz/check.sh
```

`setup.sh` clones the pinned source and applies the tracked multiplier patch before building Quartz. `setup_math.sh` builds the pinned Fiat-Crypto dependency and shared mathematical specification separately under `.deps/quartz-math`, leaving root build artifacts untouched. The check script also kernel-checks the accelerator correctness, bridge, and leakage regression proofs. `coq-core.9.1.0` supplies compatibility commands needed by Fiat-Crypto's build; it is not the legacy `coq.9.1.0` metapackage, which pins an older standard library.

For the masked controller and its combined Curve25519 theorem, use the [masking environment](../masking/README.md#build):

```sh
JOBS=1 bash quartz/check_masked_arithmetic.sh --with-ladder-security
```

This builds a fresh source snapshot and recursively kernel-checks the selected targets. Each snapshot records source hashes, checked modules, load paths, compiler/package versions, and logs under `.deps/quartz-masked-arithmetic`. The full source-only check passed; it checks proofs, not generated RTL.

Append `--with-native-export` to include the native-export proofs and exact-output printer optimization. This checks their proofs; it does not run the RTL printer or simulator.

Run the native-validation tooling's lightweight tests separately:

```sh
python3 -B -m unittest discover -s quartz -p test_controller_native.py -v
```

The SystemVerilog fixture test is opt-in via `QUARTZ_SIGNATURE_SV_AUDIT`, a new output directory. It checks acceptance of correct port widths and rejection of an input or output shortened by one bit, not full controller behavior.
