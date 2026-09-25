# Final Validation Report: A Testable Theory of Atomic Features

## 1. Human Verdict

The formalization covers the rigidity and recovery principles, their predictions
across widths and populations, hierarchical activation recovery, and six named
appendix results. All eleven conclusions are proved under the manuscript assumptions. Independent source-to-statement review passed.

## 2. Closeout Status

**Completion status:** Formalized. All eleven results have compiled proofs,
independent source review, and accepted strict closeout.

## 3. Source and Scope

The September 25, 2026 working manuscript, including its proof appendix, governs
this assessment. The scope is five main results and six appendix results, together
with their governing mathematical definitions. The linear representation hypothesis
is a model assumption, not a theorem about actual language models. Empirical
claims, optimization convergence and informal examples are outside this theorem
closeout.

## 4. Researcher Summary of Checked Results

Main results appear first; the second group supplies their named appendix support.

| Paper result | Comparison with source |
|---|---|
| Theorem 1: Atomicness | Exact |
| Theorem 2: Recovery Principle | Exact |
| Corollary 1: P1, Stability Across Size | Exact |
| Corollary 2: P2, Stability Across Data | Exact |
| Theorem 3: Hierarchical Recovery Principle | Exact |
| Lemma 3: Subspace inclusion | Exact |
| Lemma 4: Local-to-global Hall | Exact |
| Theorem 4: Generic rigidity | Exact |
| Lemma 5: Local support recovery | Exact |
| Lemma 6: Support intersections | Exact |
| Lemma 7: Activation transfer | Exact |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

Local support recovery is proved by a uniform sparse-incidence argument rather
than the appendix's nested-ball construction. Hierarchical activation recovery
uses a support-pattern argument with an upper density bound, so its conclusion
holds for the stated correlated child law without requiring independence.
Generic rigidity uses lower-dimensional chart images and their Hausdorff
measure, giving the same intrinsic spherical null-set conclusion as the source's
Sard argument. For arbitrary graphs, locally finite Hall extends the finite
argument. The [proof notes](docs/SOURCE_CLARIFICATIONS.md#proof-routes)
explain these routes and their theorem-level effects.

## 8. Proof Tricks Worth Reusing

Sparse stability turns approximate reconstruction into control of sparse codes.
A population loss bound identifies sufficiently accurate support spans, and
intersecting those spans isolates individual features. Comparing a feature's
prevalence with the discarded tail makes the resulting recovery guarantee
uniform in dictionary width. Local-to-global Hall converts small-set expansion
and bounded neighborhoods into a global matching.

## 9. Generalizations, Conjectures, and Extensions

A supporting uniform recovery theorem supplies one learned coordinate for both direction and activation,
with a positive activation threshold shared by all qualifying features and widths.
It includes the full-width endpoint, and the constants are uniform in ambient
dimension as well as dictionary widths. They may depend on fixed sparsity,
stability, regularity and approximation quality. See the
[precise scope](docs/SOURCE_CLARIFICATIONS.md#recovery-conventions).
The supporting generic dimension bound also holds for arbitrary competing widths
and sparsity budgets without competing-dictionary stability; see the
[generic dimension argument](docs/SOURCE_CLARIFICATIONS.md#proof-routes).

## 10. Source Clarifications and Exact Readings

Recovery uses the appendix's unit-column normalization and positive-prevalence
targets. At zero tail, absent features are not included in a guaranteed prefix.
The support-law conditions concern supports of cardinality K and distinct
features, with conditioning only on positive-probability events. Empty prefixes
have size zero. The matching definition pairs columns of its two arguments.
These readings do not introduce a new distribution family. The [source note](docs/SOURCE_CLARIFICATIONS.md#recovery-conventions)
states the corresponding mathematical conventions.

## 11. Paper Issues or Caveats

None.

## 12. Detailed Formalization Evidence

The eleven selected transparent propositions are in `PaperInterface.lean` and
have separate checked endpoints in `ProofInterface.lean`. Their names and
correspondence are listed in the [theorem index](docs/THEOREMS.md). The manuscript snapshot is
Overleaf revision `b35a90c4dcb1108aed44da2cbe85335226971bd2`.
The graph-bound review records eleven source matches and 53 governing
model/definition matches. The current accepted closure graph verifies this
source and proof surface.

## 13. Paper Assumption Provenance

The atomic model packages nonnegative sparse factorization and positive sparse
stability. Open richness governs rigidity. Recovery additionally uses normalized
columns, regular exact-size supports, two-sided conditional coefficient-density
bounds, and an actual expected-loss comparison with the infimum of the feasible
class. The hierarchy has exact-size parent sets, arbitrary joint child choices,
conditional child probabilities bounded below, and joint coefficient densities.
Generic rigidity uses stable competing dictionaries with width greater than the ambient dimension.

## 14. Displayed Formula Provenance

Displayed formulas are covered by the source-to-statement review and checked
proofs of their governing results. No separate formula corrections are needed.

## 15. Library Lift Pass

The exported proof closure contains 154 paper modules and uses pinned Mathlib.
No module from another paper or private AML dependency is required. The checked import closure retains the required paper-local general lemmas.

## 16. DAG Audit

The [dependency diagram](docs/DependencyDAG.pdf) shows the five main results,
six appendix results and their governing definitions. The two-page rendering
was visually inspected for readable labels, arrowheads and overlap.

## 17. Validation Checks

The focused current proof-interface build and the current standalone build
passed; the latter completed all 8,472 jobs. The initial extraction also passed
a clean GitHub Actions build. Its workflow rebuilds the published snapshot from
a clean checkout. The current eleven endpoint checks reported only `propext`, `Classical.choice` and
`Quot.sound`. The independent draft comparison passed all eleven result and
53 model/definition rows. That preflight is a repair screen, not accepting
semantic evidence. The current graph-bound review passed all eleven results and 53 governing
model/definition routes. The complete build of all 189 tracked paper modules,
fresh independent final adversarial audit, and all ten strict closeout gates
passed. The accepted closure record is current.
The pinned toolchain is Lean 4.30.0-rc2 and Mathlib revision
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## 18. Paper Definitions Checked

The source inventory distinguishes mathematical definitions and model assumptions
from local notation, computational descriptions and repeated presentations. The
current independent inventory has 18 normal definitions, four repeated
presentations, eleven local-notation records and sixteen computational records.
All 53 selected definition/model routes have current source-matching judgments.

## 19. Named Theorem Statements Checked

The selected set is Theorems 1–4, Corollaries 1–2, and Lemmas 3–7. The source's
linear representation postulate is a semantic prerequisite. Printed numbers
were checked using the manuscript's counter declarations and a rendered extract
of its active statements. Commented-out results and superseded source claims
receive no credit in this count.

## 20. Paper-Facing Statement Validator Ledger

The eleven proof-to-Spec assignments compile through the standalone import
surface. All eleven source-to-expanded-statement judgments are matches. Their separate
proof-to-Spec and axiom checks are current.

## 21. Source-Coverage Audit Ledger

The current source map binds eleven canonical result routes to the pinned source
and records governing definitions and source conventions. The independent result
and prerequisite reviews, final adversarial coverage assessment, and accepted
closure graph are current. Human annotations remain incomplete (0/11); agent
review has not been represented as human approval.
