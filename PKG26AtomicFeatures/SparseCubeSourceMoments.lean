import PKG26AtomicFeatures.RepresentationOptimizationModel
import PKG26AtomicFeatures.OrthonormalDictionaryTransport

/-!
# Source moments and finite optimal loss on the sparse unit cube

A nonnegative unit-cube code with at most K active coordinates has squared
Euclidean norm at most K. Measurable codes therefore have a finite second
moment under every probability law supported on that cube. For an
orthonormal source, an actual representation-dependent optimum has loss at
most K: its own feasible dictionary with a constant-zero encoder is an
admissible comparator. No separate dictionary-existence or width assumption
is needed for this comparison.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal BigOperators

/-- Every sparse unit-cube vector has squared Euclidean norm at most its
sparsity budget, including the zero-budget and zero-dimensional cases. -/
theorem norm_sq_le_of_mem_sparseUnitCube {M K : ℕ} {v : FeatureVector M}
    (hv : v ∈ SparseUnitCube M K) : ‖representationToEuclidean M v‖ ^ 2 ≤ (K : ℝ) := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ j, (v j) ^ 2) ≤ (K : ℝ)
  have hsum : (∑ j, (v j) ^ 2) = ∑ j ∈ nonzeroSupport v, (v j) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hz : v j = 0 := by simpa only [mem_nonzeroSupport_iff, not_not] using hj
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0)]
  rw [hsum]
  calc
    _ ≤ ∑ _j ∈ nonzeroSupport v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [(hv.2 j).1, (hv.2 j).2]
    _ = ((nonzeroSupport v).card : ℝ) := by simp
    _ ≤ (K : ℝ) := Nat.cast_le.mpr hv.1

/-- Bounded sparse source coefficients have a genuine integrable second
moment whenever their source map is measurable. -/
theorem integrable_norm_sq_of_ae_sparseUnitCube
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → FeatureVector M)
    (hz : Measurable z) (hcube : ∀ᵐ x ∂μ, z x ∈ SparseUnitCube M K) :
    Integrable (fun x => ‖representationToEuclidean M (z x)‖ ^ 2) μ := by
  have hm : Measurable (fun x => ‖representationToEuclidean M (z x)‖ ^ 2) :=
    ((representationToEuclidean M).continuous.measurable.comp hz).norm.pow_const 2
  apply (integrable_const (K : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [hcube] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_sq_le_of_mem_sparseUnitCube hx

/-- The nonnegative second-moment integral obeys the same sparsity bound;
this estimate itself needs no measurability hypothesis on the source map. -/
theorem lintegral_norm_sq_le_of_ae_sparseUnitCube
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → FeatureVector M)
    (hcube : ∀ᵐ x ∂μ, z x ∈ SparseUnitCube M K) :
    (∫⁻ x, ENNReal.ofReal (‖representationToEuclidean M (z x)‖ ^ 2) ∂μ) ≤ (K : ℝ≥0∞) := by
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (K : ℝ) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hcube] with x hx
      exact ENNReal.ofReal_le_ofReal (norm_sq_le_of_mem_sparseUnitCube hx)
    _ = (K : ℝ≥0∞) := by simp

/-- A zero encoder is feasible for any already normalized stable dictionary,
regardless of the map through which that constant encoder is composed. -/
theorem IsFeasibleRecoveryPair.zero_encoder
    {Ω : Type*} [MeasurableSpace Ω] {d m K : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {u : Ω → FeatureVector m} {γ : ℝ}
    (hfeas : IsFeasibleRecoveryPair B u γ K) (f : Ω → RepresentationVector d) :
    IsFeasibleRecoveryPair B ((fun _ : RepresentationVector d => (0 : FeatureVector m)) ∘ f) γ K := by
  refine ⟨hfeas.1, hfeas.2.1, measurable_const, ?_, ?_⟩
  · intro x
    simp [Function.comp_apply, nonzeroSupport]
  · intro x j
    exact le_rfl

/-- Exact representation-dependent optimality bounds loss by the source's
unreconstructed second moment, using the optimum's own dictionary. -/
theorem IsOptimalRepresentationPair.loss_le_source_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    {μ : Measure Ω} {A : Matrix (Fin d) (Fin M) ℝ}
    {z : Ω → FeatureVector M} {f : Ω → RepresentationVector d}
    {B : Matrix (Fin d) (Fin m) ℝ} {g : RepresentationVector d → FeatureVector m} {γ : ℝ}
    (hopt : IsOptimalRepresentationPair μ A z f B g γ K) :
    actualPopulationSquaredLoss μ A z B (g ∘ f) ≤
      ∫⁻ x, ENNReal.ofReal (‖representationToEuclidean d (A.mulVec (z x))‖ ^ 2) ∂μ := by
  have h := hopt.2 B (fun _ => 0) (hopt.1.zero_encoder f)
  simpa only [actualPopulationSquaredLoss, Function.comp_apply, Matrix.mulVec_zero,
    map_zero, sub_zero] using h

/-- For an orthonormal source, every actual primary optimum has loss at
most the sparse unit-cube budget. The observed representation may be arbitrary. -/
theorem IsOptimalRepresentationPair.loss_le_sparseUnitCube
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Matrix (Fin d) (Fin M) ℝ}
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    {z : Ω → FeatureVector M} {f : Ω → RepresentationVector d}
    {B : Matrix (Fin d) (Fin m) ℝ} {g : RepresentationVector d → FeatureVector m} {γ : ℝ}
    (hopt : IsOptimalRepresentationPair μ A z f B g γ K)
    (hcube : ∀ᵐ x ∂μ, z x ∈ SparseUnitCube M K) :
    actualPopulationSquaredLoss μ A z B (g ∘ f) ≤ (K : ℝ≥0∞) := by
  have h := hopt.loss_le_source_secondMoment
  simp_rw [orthonormalDictionary_synthesis_norm A hA] at h
  exact h.trans (lintegral_norm_sq_le_of_ae_sparseUnitCube μ z hcube)

/-- The actual loss of a primary optimum is finite under orthonormal sparse
unit-cube source assumptions, without an additional width restriction. -/
theorem IsOptimalRepresentationPair.loss_lt_top_of_sparseUnitCube
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Matrix (Fin d) (Fin M) ℝ}
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    {z : Ω → FeatureVector M} {f : Ω → RepresentationVector d}
    {B : Matrix (Fin d) (Fin m) ℝ} {g : RepresentationVector d → FeatureVector m} {γ : ℝ}
    (hopt : IsOptimalRepresentationPair μ A z f B g γ K)
    (hcube : ∀ᵐ x ∂μ, z x ∈ SparseUnitCube M K) :
    actualPopulationSquaredLoss μ A z B (g ∘ f) < ⊤ :=
  (hopt.loss_le_sparseUnitCube hA hcube).trans_lt (by simp)

end PKG26AtomicFeatures
