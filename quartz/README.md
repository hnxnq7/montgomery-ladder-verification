# Quartz Integration

This integration reuses `mit-plv/quartz` at commit `7db2fa703550655e0c578607da42bc3a63c37307`, including the processor in `examples/Processor.v`. It is not yet a verified Curve25519 implementation on Quartz.

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

`start` accepts five 255-bit coordinates and clears scratch storage (`start_initial`). A new start replaces an active request; callers must serialize requests. `reset` clears all storage and enters a non-ready idle phase (`reset_clears`, `reset_is_idle`). Read outputs only when `ready` holds; completed states retain their output. The host-side `initial` truncates integers to 255 bits, so curve-level callers must establish canonical input bounds. Outputs are slots 19/23 (doubling) and 16/18 (differential addition).

`accelerator_cpu.v` connects the device to the actual `Processor.v` CPU through its existing MMIO port, with no CPU source changes. `accelerator_cpu_tests.v` executes native stores and loads to start a LadderStep and copy its result to RAM (`native_cpu_accelerator_step`). The environment services instruction/data memory using the existing adapter, advances the device each cycle, and retains an MMIO response until the CPU can accept it. This host-side environment is executable Rocq, not yet synthesized bus logic.

The MMIO base is `0x1000`; offsets below are bytes. Only aligned accesses are accepted; other reads return zero and other writes are ignored.

| Offset | Meaning |
| --- | --- |
| 0..159 | Five input coordinates, each eight little-endian 32-bit words |
| 160 | Write 1 to start, 0 to reset (also clears input staging) |
| 164 | Read completion status: 0 or 1 |
| 168..295 | Four result coordinates, each eight little-endian words; zero until ready |

Input writes alter staging only, not an active computation. Start replaces an active request using a snapshot of staging. The top bit of each 256-bit input slot is truncated; callers must supply canonical field elements. Completed output remains available until start/reset. No input or output marshaling correctness theorem is claimed yet.

This accelerator is unprotected: neither its data bank nor arithmetic intermediates have complementary storage. Public control scheduling is not power-leakage security. General modular-arithmetic correctness, a universal LadderStep correspondence theorem, the scalar loop, MMIO refinement, synthesis validation, and leakage security remain open. The original CPU adapter and its existing tests are unchanged.

## Remaining Work

1. Prove the accelerator's field arithmetic and LadderStep correct for all canonical inputs.
2. Add the full scalar loop and affine conversion, then prove CPU/MMIO marshaling and execution correspondence.
3. Define leakage and public equivalence across CPU, accelerator, and memory interfaces; protect secret-bearing data throughout that scope.
4. Prove relational leakage-trace independence and validate the synthesized datapath and bus integration.

Quartz's example uses 32-bit arithmetic and a restricted instruction subset. The existing project's 255-bit atomic-field processor theorems do not automatically transfer. Initial RAM contents, output release, address bounds, and leakage from inactive buffers require explicit treatment.

## Build

Use a separate switch so the existing project's toolchain remains unchanged:

```sh
opam switch create "$PWD/.deps/quartz-toolchain" ocaml-base-compiler.5.3.0 --no-switch -y
opam install --switch="$PWD/.deps/quartz-toolchain" dune.3.21.1 rocq-core.9.1.0 rocq-stdlib.9.1.0 -y
opam exec --switch="$PWD/.deps/quartz-toolchain" -- bash quartz/check.sh
```

`setup.sh` clones the pinned source and applies the tracked multiplier patch before building Quartz. The legacy `coq.9.1.0` metapackage pins an older standard library; use the Rocq packages above. The original project's `check.sh` remains unchanged.
