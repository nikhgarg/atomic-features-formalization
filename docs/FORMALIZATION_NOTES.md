# Mathematical scope

The formalization covers five main results and six named appendix results in
**A Testable Theory of Atomic Features**, using the September 25, 2026 manuscript
and its stated assumptions.

- **Theorem 1, Atomicness:** a Pareto-efficient competing nonnegative sparse
  representation is equal to the rich source up to permutation and scaling,
  or uses at least twice its sparsity. Both dictionaries have positive sparse
  stability; orthogonality is not required.
- **Theorem 2, Recovery:** for fixed sparsity and regularity parameters, every
  positive-prevalence feature whose prevalence is at least a constant times the
  discarded tail is recovered in direction and activation. A supporting stronger
  theorem uses one learned coordinate for both conclusions and a common positive
  activation threshold. Its constants are uniform in dictionary widths and
  ambient dimension.
  The source and learned columns are normalized, as in the proof appendix.
  Any confidence below one is allowed. No Zipf law is assumed.
- **Corollaries 1–2, P1/P2:** the guaranteed features give simultaneous
  injective signed-cosine matchings across larger widths and shared features
  across populations. Each population uses its own prevalence ranking and
  recoverable prefix; an empty prefix has length zero.
- **Theorem 3, Hierarchical recovery:** the parent and both children of every
  qualifying family are recovered in activation. Child choices and active
  coefficients may be correlated under the stated conditional balance and
  joint density bounds. Direction recovery of every child is not claimed.
- **Theorem 4, Generic rigidity:** for almost every unit-column source,
  every stable competing factorization with width $M'>d$ satisfies
  $K'\ge1+(d-1)(M-M')/M$ and $M'>M/2$.

The [theorem index](THEOREMS.md) includes all six appendix results and their
proof endpoints. The [validation report](../FINAL_VALIDATION_REPORT.md) records
source comparisons, proof routes and verification status. The
[mathematical notes](SOURCE_CLARIFICATIONS.md) explain the proof routes
and the appendix conventions inherited by the main statements.

The linear representation hypothesis is an assumption of the mathematical
model. These proofs do not establish that hypothesis empirically, certify
optimizer convergence, or formalize the illustrative molecular discussion.
