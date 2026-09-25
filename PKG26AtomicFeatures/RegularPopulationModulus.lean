import PKG26AtomicFeatures.UpperDensityModulus
import PKG26AtomicFeatures.MesoscalePopulationModel

/-!
# The regular population assumptions imply bounded modulus populations

Conditional absolute continuity with respect to the coefficient cube supplies
coordinate bounds on each positive-mass source support. Coordinates outside
that support vanish. The finite exact-support mixture then transfers these
bounds to the original population, without imposing pointwise source bounds.

Consequently the existing regular-population assumptions imply the bounded
core automatically, and their conditional upper density bound supplies the
explicit common modulus. Neither argument uses the lower density bound or
source-feature separation.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- On a positive-mass exact support, conditional absolute continuity with
respect to the cube bounds every source coordinate, including the zero
coordinates outside the selected support. -/
theorem sourceSupportConditionalLaw_ae_coefficient_bounds_of_cube_absoluteContinuity
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (hz : Measurable z)
    (S : ExactSourceSupport M K) (hS : μ (sourceSupportEvent z S.1) ≠ 0)
    (hac : Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) ≪
      uniformCubeCoefficientLaw K) :
    ∀ᵐ x ∂sourceSupportConditionalLaw μ z S.1, ∀ i, 0 ≤ z x i ∧ z x i ≤ 1 := by
  classical
  have hselected : ∀ᵐ x ∂sourceSupportConditionalLaw μ z S.1,
      ∀ j, 0 ≤ sourceSupportCoordinates z S x j ∧ sourceSupportCoordinates z S x j ≤ 1 :=
    ae_of_ae_map (measurable_sourceSupportCoordinates z hz S).aemeasurable
      (hac.ae_le (uniformCubeCoefficientLaw_ae_coordinate_bounds K))
  filter_upwards [hselected, sourceSupportConditionalLaw_ae_support_eq μ z hz S.1 hS]
    with x hx hsupp
  intro i
  by_cases hi : i ∈ S.1
  · have himage : i ∈ Finset.univ.image (sourceSupportEnumeration S) := by
      rwa [sourceSupportEnumeration_image]
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp himage
    exact hx j
  · have hzero : z x i = 0 := by
      by_contra hne
      have hmem := (mem_nonzeroSupport_iff (z x) i).mpr hne
      rw [hsupp] at hmem
      exact hi hmem
    simp only [hzero, le_refl, zero_le_one, and_self]

/-- Measurability, exact sparsity and conditional absolute continuity already
imply the bounded-population core. Finite support conditioning handles null
support events with zero mixture weight, so no assumption is made about their
arbitrary conditional-law branch. The original measure need only be finite. -/
theorem boundedSparsePopulation_of_conditional_cube_absoluteContinuity
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (z : Ω → FeatureVector M)
    (hz : Measurable z) (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (hac : ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
      Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) ≪
        uniformCubeCoefficientLaw K) :
    BoundedSparsePopulation (K := K) μ z := by
  classical
  refine ⟨hz, hexact, ?_⟩
  rw [measure_eq_sum_sourceSupportConditionalLaw μ z hz hexact, ae_finsetSum_measure_iff]
  intro S _
  by_cases hS : μ (sourceSupportEvent z S.1) = 0
  · simp only [Measure.real, hS, ENNReal.toReal_zero, ENNReal.ofReal_zero,
      zero_smul, ae_zero, Filter.eventually_bot]
  · exact Measure.ae_smul_measure
      (sourceSupportConditionalLaw_ae_coefficient_bounds_of_cube_absoluteContinuity
        μ z hz S hS (hac S hS)) _

/-- A common conditional upper measure bound supplies the bounded core.
This uses no lower density, separation, or extra source-coordinate premise. -/
theorem boundedSparsePopulation_of_conditional_cube_domination
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (z : Ω → FeatureVector M)
    (hz : Measurable z) (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (C : ℝ≥0∞)
    (hdom : ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
      Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) ≤
        C • uniformCubeCoefficientLaw K) :
    BoundedSparsePopulation (K := K) μ z :=
  boundedSparsePopulation_of_conditional_cube_absoluteContinuity μ z hz hexact
    (fun S hS => Measure.absolutelyContinuous_of_le_smul (hdom S hS))

/-- The current regular-population model already forces almost-sure source
coefficients in the unit cube. Its lower density and separation parameters do
not enter the derivation. -/
theorem RegularSparsePopulation.boundedSparsePopulation
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    {μ : Measure Ω} [IsFiniteMeasure μ] {z : Ω → FeatureVector M}
    {ρ cLower cUpper : ℝ}
    (hreg : RegularSparsePopulation (K := K) μ z ρ cLower cUpper) :
    BoundedSparsePopulation (K := K) μ z :=
  boundedSparsePopulation_of_conditional_cube_domination μ z hreg.1 hreg.2.1
    (ENNReal.ofReal cUpper) (fun S hS => (hreg.coefficientLaw_bounds S hS).2)

/-- An upper-density conditional model gives the common cube slab modulus
without a separate bounded-coefficient premise: those bounds follow from the
actual exact-support law and conditional domination. -/
theorem modulusSparsePopulation_of_conditional_upper_density
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (z : Ω → FeatureVector M)
    (hz : Measurable z) (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
      Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) ≤
        ENNReal.ofReal C • uniformCubeCoefficientLaw K) :
    ModulusSparsePopulation (K := K) μ z (fun s => C * uniformCubeSlabModulus K s) :=
  (boundedSparsePopulation_of_conditional_cube_domination μ z hz hexact
    (ENNReal.ofReal C) hdom).modulus_of_conditional_upper_density C hC hdom

/-- The original regular-population assumptions imply the explicit modulus
hypothesis used by density-free unsigned recovery. The same modulus is
uniform over every support and depends only on sparsity and the common upper
density bound. Its vanishing limit is `upperDensitySlabModulus_tendsto_zero`. -/
theorem RegularSparsePopulation.modulusSparsePopulation
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    {μ : Measure Ω} [IsFiniteMeasure μ] {z : Ω → FeatureVector M}
    {ρ cLower cUpper : ℝ}
    (hreg : RegularSparsePopulation (K := K) μ z ρ cLower cUpper) (hcUpper : 0 ≤ cUpper) :
    ModulusSparsePopulation (K := K) μ z (fun s => cUpper * uniformCubeSlabModulus K s) :=
  hreg.boundedSparsePopulation.modulus_of_conditional_upper_density cUpper hcUpper
    (fun S hS => (hreg.coefficientLaw_bounds S hS).2)

end PKG26AtomicFeatures
