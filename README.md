# Atomic Features: Lean formalization

Lean proofs for **A Testable Theory of Atomic Features**. This repository
contains the paper's formalization and its required paper-local proof modules.
It depends on Mathlib; no private repository or AML dependency is required.

The current source-facing results cover rigidity, ordinary recovery, stability
across dictionary widths and populations, hierarchical activation recovery,
and six supporting appendix results. All eleven selected results have checked
proofs under the manuscript assumptions. See the [validation report](FINAL_VALIDATION_REPORT.md)
for the source comparison, mathematical conventions and verification scope.
This repository has not yet been anonymized for submission.

## Build

Install Lean's `elan` toolchain manager, then from this repository run:

```sh
lake exe cache get
lake build
```

The toolchain and every dependency revision are pinned in `lean-toolchain` and
`lake-manifest.json`. The build includes `SubmissionChecks.lean`, which imports
the public entrypoint, checks all eleven advertised proof/Spec pairs, and prints
their axiom dependencies.

## Read the formalization

Start with the [final validation report](FINAL_VALIDATION_REPORT.md) for what
is proved and how it matches the paper. Then read
[`PaperInterface.lean`](PKG26AtomicFeatures/PaperInterface.lean) for the precise
formal statements.

The source code is distributed under the Apache License 2.0; see [LICENSE](LICENSE).
