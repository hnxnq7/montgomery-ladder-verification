# Quartz Integration

This integration reuses `mit-plv/quartz` at commit `7db2fa703550655e0c578607da42bc3a63c37307`, including the processor in `examples/Processor.v`. It is not yet a verified Curve25519 implementation on Quartz.

## Checked Components

- `field_words.v`: eight native 32-bit words represent a Curve25519 field element without loss (`Curve25519Words.field_roundtrip`). This is a representation proof, not a field-arithmetic implementation.
- `memory.v`: an executable environment around Quartz's actual CPU interface, instruction queues, and data-memory queues. Requests are serviced before the next CPU tick when the response queue has room. Scratch memory is a bounded word list; out-of-range reads return zero and writes are ignored. Programs must separately establish aligned, in-bounds, public addresses.
- `constant_time_multiplier.patch`: removes Quartz's zero-operand early completion. Multiplication now waits for the counter regardless of operands.
- `processor_tests.v`: proves one-step multiplier readiness depends only on its control flags and counter (`ready_tick_independent`); checks zero/nonzero latency and products; executes ADDI, MUL, SW, and LW through the actual Quartz pipeline (`native_cpu_multiply_store_load`).

The new proofs contain no admits or additional axioms. Tests check functionality and one multiplier control property, not whole-processor leakage security.

## Remaining Work

1. Implement and verify native multiword field addition, subtraction, multiplication, and reduction modulo `2^255 - 19`.
2. Compile LadderStep using fixed-address scratch storage. The old 18 field instructions are not native Quartz instructions.
3. Add secret metadata and complementary storage for registers, pipeline values, multiplier operands/results, and secret-bearing memory-interface data.
4. Define leakage and public equivalence; prove public schedules/addresses, complement preservation, and relational `processor_trace_independent` over Quartz execution.

Quartz's example uses 32-bit arithmetic and a restricted instruction subset. The existing project's 255-bit atomic-field processor theorems do not automatically transfer. Initial RAM contents, output release, address bounds, and leakage from inactive buffers require explicit treatment.

## Build

Use a separate switch so the existing project's toolchain remains unchanged:

```sh
opam switch create "$PWD/.deps/quartz-toolchain" ocaml-base-compiler.5.3.0 --no-switch -y
opam install --switch="$PWD/.deps/quartz-toolchain" dune.3.21.1 rocq-core.9.1.0 rocq-stdlib.9.1.0 -y
opam exec --switch="$PWD/.deps/quartz-toolchain" -- bash quartz/check.sh
```

`setup.sh` clones the pinned source and applies the tracked multiplier patch before building Quartz. The legacy `coq.9.1.0` metapackage pins an older standard library; use the Rocq packages above. The original project's `check.sh` remains unchanged.
