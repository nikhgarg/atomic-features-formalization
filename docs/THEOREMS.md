# Theorem index

All names below are in namespace `PKG26AtomicFeatures`.

| Paper result | Statement | Proof |
|---|---|---|
| Theorem 1: Atomicness | `RigiditySpec` | `rigidity` |
| Theorem 2: Recovery Principle | `PositivePrevalenceRecoverySpec` | `positivePrevalenceRecovery` |
| Corollary 1: P1, Stability Across Size | `PositivePrevalenceSizeStabilitySpec` | `positivePrevalenceSizeStability` |
| Corollary 2: P2, Stability Across Data | `PositivePrevalenceDataStabilitySpec` | `positivePrevalenceDataStability` |
| Theorem 3: Hierarchical Recovery Principle | `HierarchicalRecoverySpec` | `hierarchicalRecovery` |
| Lemma 3: Subspace inclusion | `SubspaceInclusionSpec` | `subspaceInclusion` |
| Lemma 4: Local-to-global Hall | `LocalToGlobalHallSpec` | `localToGlobalHall` |
| Theorem 4: Generic rigidity | `GenericRigiditySpec` | `genericRigidity` |
| Lemma 5: Local support recovery | `ConditionalSpanRecoverySpec` | `conditionalSpanRecovery` |
| Lemma 6: Stable support intersections | `StableSupportIntersectionSpec` | `stableSupportIntersection` |
| Lemma 7: Activation transfer | `ActivationTransferSpec` | `activationTransfer` |

The first five are main-text results; the final six are appendix results.
Source and proof scope are described in [the notes](FORMALIZATION_NOTES.md).

## Supporting uniform constructions

These proved extensions give a common positive activation threshold across all
qualifying features and widths. Ordinary recovery also uses the same learned
coordinate for direction and activation. They supply the proofs of the source
statements above.

| Statement | Proof |
|---|---|
| `UniformPositivePrevalenceRecoverySpec` | `uniformPositivePrevalenceRecovery` |
| `UniformHierarchicalRecoverySpec` | `uniformHierarchicalRecovery` |
