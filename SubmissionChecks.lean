import AtomicFeatures

open PKG26AtomicFeatures

example : RigiditySpec := rigidity
#print axioms rigidity

example : PositivePrevalenceRecoverySpec := positivePrevalenceRecovery
#print axioms positivePrevalenceRecovery

example : PositivePrevalenceSizeStabilitySpec := positivePrevalenceSizeStability
#print axioms positivePrevalenceSizeStability

example : PositivePrevalenceDataStabilitySpec := positivePrevalenceDataStability
#print axioms positivePrevalenceDataStability

example : HierarchicalRecoverySpec := hierarchicalRecovery
#print axioms hierarchicalRecovery

example : SubspaceInclusionSpec := subspaceInclusion
#print axioms subspaceInclusion

example : LocalToGlobalHallSpec := localToGlobalHall
#print axioms localToGlobalHall

example : GenericRigiditySpec := genericRigidity
#print axioms genericRigidity

example : ConditionalSpanRecoverySpec := conditionalSpanRecovery
#print axioms conditionalSpanRecovery

example : StableSupportIntersectionSpec := stableSupportIntersection
#print axioms stableSupportIntersection

example : ActivationTransferSpec := activationTransfer
#print axioms activationTransfer
