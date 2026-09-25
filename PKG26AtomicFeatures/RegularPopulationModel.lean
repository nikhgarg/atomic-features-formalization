import PKG26AtomicFeatures.DensityBoundedCoefficients
import PKG26AtomicFeatures.SelectedSourceMaps
import PKG26AtomicFeatures.FeatureF1

/-!
# Regular sparse populations

These definitions retain the actual input distribution and actual source
feature map. Conditional laws are obtained by restricting that input measure
to an observed support; learned codes are not required to be functions of the
source coefficients. A zero-mass conditional law is set to the original
probability measure, and all density conditions explicitly exclude that case.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal

/-- A source support in the fixed-K population model. -/
abbrev ExactSourceSupport (M K : ℕ) := {S : Finset (Fin M) // S.card = K}

/-- An enumeration only supplies coordinates for the conditional K-cube
law; it introduces no order or computability assumption into the model. -/
noncomputable def sourceSupportEnumeration {M K : ℕ} (S : ExactSourceSupport M K) :
    Fin K ↪ Fin M :=
  (Fintype.equivFinOfCardEq (show Fintype.card S.1 = K by simpa using S.2)).symm.toEmbedding.trans
    (Function.Embedding.subtype fun i => i ∈ S.1)

theorem sourceSupportEnumeration_image {M K : ℕ} (S : ExactSourceSupport M K) :
    Finset.univ.image (sourceSupportEnumeration S) = S.1 := by
  classical
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ((Fintype.equivFinOfCardEq
      (show Fintype.card S.1 = K by simpa using S.2)).symm j).2
  · intro hi
    refine ⟨(Fintype.equivFinOfCardEq
      (show Fintype.card S.1 = K by simpa using S.2)) ⟨i, hi⟩, ?_⟩
    simp [sourceSupportEnumeration]

/-- The event on the original data domain that a given support is active. -/
def sourceSupportEvent {Ω : Type*} {M : ℕ}
    (z : Ω → FeatureVector M) (S : Finset (Fin M)) : Set Ω :=
  {x | nonzeroSupport (z x) = S}

/-- The actual conditional input law given a source support. The arbitrary
zero-mass branch is harmless because it receives zero mixture weight. -/
noncomputable def sourceSupportConditionalLaw
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (S : Finset (Fin M)) : Measure Ω :=
  if μ (sourceSupportEvent z S) = 0 then μ
  else (μ (sourceSupportEvent z S))⁻¹ • μ.restrict (sourceSupportEvent z S)

/-- Read the active coordinates in the enumeration of the observed support. -/
noncomputable def sourceSupportCoordinates {Ω : Type*} {M K : ℕ}
    (z : Ω → FeatureVector M) (S : ExactSourceSupport M K) :
    Ω → EuclideanRepresentation K :=
  fun x => representationToEuclidean K (fun j => z x (sourceSupportEnumeration S j))

/-- Source feature prevalence under the actual input distribution. -/
noncomputable def featurePrevalence
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (i : Fin M) : ℝ :=
  μ.real {x | 0 < z x i}

/-- The distributional primitives used in recovery: exact-K supports,
separation of distinct positive-prevalence features, and bounded conditional
joint densities. Bounds on densities are stated almost everywhere because
density versions differing on a null set define the same probability law.

The source's explicit pointwise density bounds imply these conditions.
Recovery statements must separately require the recovered feature's
prevalence to be positive; the separation clause does not identify absent
features. -/
def RegularSparsePopulation
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (ρ cLower cUpper : ℝ) : Prop :=
  Measurable z ∧
  (∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K) ∧
  (∀ i j : Fin M, i ≠ j → 0 < featurePrevalence μ z i →
    ρ * featurePrevalence μ z i ≤ μ.real {x | 0 < z x i ∧ z x j = 0}) ∧
  ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
    ∃ h : EuclideanRepresentation K → ℝ≥0∞, Measurable h ∧
      Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) =
        (uniformCubeCoefficientLaw K).withDensity h ∧
      (∀ᵐ w ∂uniformCubeCoefficientLaw K,
        ENNReal.ofReal cLower ≤ h w ∧ h w ≤ ENNReal.ofReal cUpper)

/-- Expected nonnegative squared reconstruction loss, retaining infinite
loss rather than using the zero convention for nonintegrable real integrals. -/
noncomputable def actualPopulationSquaredLoss
    {Ω : Type*} [MeasurableSpace Ω] {d M m : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖representationToEuclidean d (A.mulVec (z x)) -
    representationToEuclidean d (B.mulVec (u x))‖ ^ 2) ∂μ

/-- The revised paper's feasible normalized, stable, nonnegative K-sparse
dictionary class, including measurability of the actual feature map. -/
def IsFeasibleRecoveryPair
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m) (γ : ℝ) (K : ℕ) : Prop :=
  HasUnitEuclideanColumns B ∧ SparseLowerStable B γ (2 * K) ∧
    Measurable u ∧ KSparse (K := K) u ∧ ∀ x j, 0 ≤ u x j

/-- Constant-factor optimality quantified over the actual feasible pairs.
Equivalence to comparison with the infimum will be proved, rather than
assuming existence of an optimal dictionary. -/
def IsApproximatelyOptimalRecoveryPair
    {Ω : Type*} [MeasurableSpace Ω] {d M m : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m)
    (γ C : ℝ) (K : ℕ) : Prop :=
  IsFeasibleRecoveryPair B u γ K ∧
    ∀ (B' : Matrix (Fin d) (Fin m) ℝ) (u' : Ω → FeatureVector m),
      IsFeasibleRecoveryPair B' u' γ K →
      actualPopulationSquaredLoss μ A z B u ≤
        ENNReal.ofReal C * actualPopulationSquaredLoss μ A z B' u'

/-- The infimum of the actual loss over all feasible width-m dictionaries
and feature maps. No minimizer is postulated. -/
noncomputable def optimalRecoveryLoss
    {Ω : Type*} [MeasurableSpace Ω] {d M : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (γ : ℝ) (K m : ℕ) : ℝ≥0∞ :=
  ⨅ (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m)
    (_ : IsFeasibleRecoveryPair B u γ K), actualPopulationSquaredLoss μ A z B u

/-- The comparator formulation of approximate optimality is exactly the
paper's infimum formulation for a positive approximation factor. This also
handles a nonattained infimum and infinite losses. -/
theorem isApproximatelyOptimalRecoveryPair_iff_loss_le_infimum
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m)
    (γ C : ℝ) (hC : 0 < C) :
    IsApproximatelyOptimalRecoveryPair μ A z B u γ C K ↔
      IsFeasibleRecoveryPair B u γ K ∧
        actualPopulationSquaredLoss μ A z B u ≤
          ENNReal.ofReal C * optimalRecoveryLoss μ A z γ K m := by
  have hCzero : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  simp only [IsApproximatelyOptimalRecoveryPair, optimalRecoveryLoss,
    ENNReal.mul_iInf_of_ne hCzero ENNReal.ofReal_ne_top, le_iInf_iff]

/-- On every positive-mass source support, regularity gives the two
measure comparisons used by incidence and orientation. -/
theorem RegularSparsePopulation.coefficientLaw_bounds
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector M} {ρ cLower cUpper : ℝ}
    (hreg : RegularSparsePopulation (K := K) μ z ρ cLower cUpper)
    (S : ExactSourceSupport M K) (hS : μ (sourceSupportEvent z S.1) ≠ 0) :
    ENNReal.ofReal cLower • uniformCubeCoefficientLaw K ≤
        Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) ∧
      Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) ≤
        ENNReal.ofReal cUpper • uniformCubeCoefficientLaw K := by
  obtain ⟨h, _hmeas, hlaw, hbound⟩ := hreg.2.2.2 S hS
  rw [hlaw]
  constructor
  · simpa only [withDensity_const] using
      (withDensity_mono (hbound.mono (fun _ hz => hz.1)))
  · exact cube_withDensity_le_of_ae_bound K h _ (hbound.mono (fun _ hz => hz.2))

/-- Reducing the separation constant preserves regularity. In particular,
the bounded separation parameter min(ρ,1) introduces no extra assumption. -/
theorem RegularSparsePopulation.mono_separation
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector M} {ρ ρ' cLower cUpper : ℝ}
    (hreg : RegularSparsePopulation (K := K) μ z ρ cLower cUpper) (hρ : ρ' ≤ ρ) :
    RegularSparsePopulation (K := K) μ z ρ' cLower cUpper := by
  refine ⟨hreg.1, hreg.2.1, ?_, hreg.2.2.2⟩
  intro i j hij hpi
  exact (mul_le_mul_of_nonneg_right hρ hpi.le).trans (hreg.2.2.1 i j hij hpi)

end PKG26AtomicFeatures
