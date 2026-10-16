# Montgomery Ladder Verification

This is the original single-file Rocq development, recovered so we can work
through it one small step at a time. No later proof changes, Lean port, memory
processor extensions, or CPU integrations are included.

This is the main working repository. The larger development is preserved
separately in [montgomery-ladder-verification-expanded](https://github.com/hnxnq7/montgomery-ladder-verification-expanded).

## Recovered Source

`montgomery_ladder.v` is an unchanged copy of VS Code local-history entry
`XYvn.v`, saved May 11, 2026 at 2:08:25 PM America/New_York (18:08:25 UTC).
It is the last available snapshot before the May 18 distributional edits.

It matches the original discussion: the mentor's comment at line 1756 reads:

```coq
(* todo: instead of summing over ensemble, state equivalence between distribution of copies. *)
```

The original `secret_map`, aggregate-HW statement, comments, and unfinished
proofs are preserved. No source formatting or proof repair was applied.

SHA-256 of the recovered file:

```text
279ab34591534657880d0a1fddf077f27ca00235c711d1a1cd8867cf13870ebb
```

## Checking It

On October 16, 2026, the unchanged file compiled with Rocq 9.1.0, OCaml 5.1.0,
Stdlib 9.0.0, std++/bitvector at `ec795ece9125d60d9974e15fc52f3dfe91ae3f4b`,
and record-update at `7b2645210331c3ec4ed75fa5ad0840a723f25151`.
These are the versions used for the recovery check, not a claim about the
original author's compiler version.

With those dependencies installed in the active environment:

```sh
coqc montgomery_ladder.v
```

Compilation accepts the seven existing `Admitted` declarations. It does not
prove those obligations or audit the security claims. Generated build files
are excluded from Git.

## How We Will Work

Read a definition, agree on what it means, and discuss a proposed change before
implementing it. The larger development remains separate; its source files
have not been changed by the rename. The initial commit preserves the recovered baseline.
