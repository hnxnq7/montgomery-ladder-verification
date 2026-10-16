# Montgomery Ladder Verification

This is the original Rocq development, recovered so we can work through it
one small step at a time. Its existing sections are now separate files;
the definitions, theorem statements, proof bodies, and TODOs are unchanged.
No later proof fixes, Lean port, memory extensions, or CPU integrations are included.

This is the main working repository. The larger development is preserved
separately in [montgomery-ladder-verification-expanded](https://github.com/hnxnq7/montgomery-ladder-verification-expanded).

## Files

| File | What it contains |
| --- | --- |
| [ladder_math.v](ladder_math.v) | Field arithmetic, LadderStep, the branching ladder, and CSwap equivalence. |
| [dual_circuit.v](dual_circuit.v) | The original `HammingWeight` section: bitvector operations, preliminary probability labels, abstract register machine, and complementary-register proofs. |
| [state_machine.v](state_machine.v) | The original `StateMachine` module: fetch/execute/writeback, register mapping, and processor invariants. Imports `dual_circuit.v`. |
| [two_reg_prob.v](two_reg_prob.v) | The original `TwoRegProb` section: two registers, `GenRV`, ensembles, masking program, and the mentor's distribution TODO. |
| [montgomery_ladder.v](montgomery_ladder.v) | A small entry file that exports all four modules. It contains no new definitions or proofs. |

`ladder_math.v`, `dual_circuit.v`, and `two_reg_prob.v` each use only library
dependencies. `state_machine.v` also needs `dual_circuit.v`. There is no new
connection between the models implied by grouping them together.

Existing short names remain available after `Require Import montgomery_ladder.`
Fully qualified names now belong to the new files; for example,
`montgomery_ladder.CSwap_eq` becomes `ladder_math.CSwap_eq`.

`check.sh` builds the files in dependency order; `_CoqProject` supplies editor
paths. No mathematical changes are part of this split.

## Original Snapshot

The starting file was an unchanged copy of VS Code local-history entry
`XYvn.v`, saved May 11, 2026 at 2:08:25 PM America/New_York (18:08:25 UTC).
It is the last available snapshot before the May 18 distributional edits.

The untouched file remains in [the initial commit](https://github.com/hnxnq7/montgomery-ladder-verification/blob/a16a220a4e91933cac8e7ed82c16a0eb98484871/montgomery_ladder.v).
Its mentor comment at original line 1756, now in `two_reg_prob.v`, reads:

```coq
(* todo: instead of summing over ensemble, state equivalence between distribution of copies. *)
```

The original `secret_map`, aggregate-HW statement, comments, and unfinished
proofs are preserved. Only file boundaries and imports changed.

SHA-256 of the untouched single-file snapshot (not the new entry file):

```text
279ab34591534657880d0a1fddf077f27ca00235c711d1a1cd8867cf13870ebb
```

## Checking It

On October 16, 2026, the unchanged file compiled with Rocq 9.1.0, OCaml 5.1.0,
Stdlib 9.0.0, std++/bitvector at `ec795ece9125d60d9974e15fc52f3dfe91ae3f4b`,
and record-update at `7b2645210331c3ec4ed75fa5ad0840a723f25151`.
These are the versions used for the recovery check, not a claim about the
original author's compiler version.

The split files also compile with this toolchain. Their extracted contents
reconstruct the original snapshot byte for byte, and the entry-file imports
were checked separately.

With those dependencies installed in the active environment:

```sh
bash check.sh
```

Compilation accepts the seven existing `Admitted` declarations. It does not
prove those obligations or audit the security claims. Generated build files
are excluded from Git.

## How We Will Work

Read a definition, agree on what it means, and discuss a proposed change before
implementing it. The larger development remains separate; its source files
have not been changed by the rename. The initial commit preserves the recovered baseline.
