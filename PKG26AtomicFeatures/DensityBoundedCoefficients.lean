import PKG26AtomicFeatures.UniformCubeCoefficients
import PKG26AtomicFeatures.SparseSubspaceIncidence
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Uniform estimates for density-bounded coefficient laws

The revised draft permits a different conditional coefficient density on
every support, with one common upper bound. Domination by that upper bound
times the uniform cube measure gives constants uniform over all such laws.
This does not assume independent coordinates for the new conditional law.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped ENNReal

/-- A density bounded above by `C` gives measure domination by `C` times
the reference cube law. The density may correlate its coordinates. -/
theorem cube_withDensity_le_of_ae_bound
    (K : ℕ) (h : EuclideanRepresentation K → ℝ≥0∞) (C : ℝ≥0∞)
    (hbound : ∀ᵐ z ∂uniformCubeCoefficientLaw K, h z ≤ C) :
    (uniformCubeCoefficientLaw K).withDensity h ≤ C • uniformCubeCoefficientLaw K := by
  simpa only [withDensity_const] using withDensity_mono hbound

/-- One slab threshold works for every coefficient law with the same
upper density bound. The threshold is chosen before the law and direction. -/
theorem densityBoundedCube_uniform_slab_threshold
    (K : ℕ) (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ ν : Measure (EuclideanRepresentation K),
      ν ≤ ENNReal.ofReal C • uniformCubeCoefficientLaw K →
      ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
        ν.real {z | |inner ℝ v z| ≤ t} ≤ ε := by
  obtain ⟨t, ht, hslab⟩ := uniformCubeCoefficientLaw_uniform_slab_threshold K
    (show 0 < ENNReal.ofReal (ε / C) by exact ENNReal.ofReal_pos.mpr (div_pos hε hC))
  refine ⟨t, ht, ?_⟩
  intro ν hν v hv
  have hbound : ν {z | |inner ℝ v z| ≤ t} ≤ ENNReal.ofReal ε := by
    calc
      _ ≤ (ENNReal.ofReal C • uniformCubeCoefficientLaw K) {z | |inner ℝ v z| ≤ t} :=
        hν _
      _ = ENNReal.ofReal C * uniformCubeCoefficientLaw K {z | |inner ℝ v z| ≤ t} := by
        rw [Measure.smul_apply, smul_eq_mul]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (ε / C) :=
        mul_le_mul_right (hslab v hv).le _
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hC.le]
        congr 1
        field_simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hε.le)

/-- Domination transfers the cube's deterministic norm bound to the new
coefficient law. -/
theorem densityBoundedCube_ae_norm_le
    (K : ℕ) (ν : Measure (EuclideanRepresentation K)) (C : ℝ≥0∞)
    (hν : ν ≤ C • uniformCubeCoefficientLaw K) :
    ∀ᵐ z ∂ν, ‖z‖ ≤ (K : ℝ) + 1 :=
  (Measure.absolutelyContinuous_of_le_smul hν).ae_le
    (uniformCubeCoefficientLaw_ae_norm_le K)

/-- A random coefficient vector whose law obeys the density bound inherits
the same uniform slab estimate. The random input space is unrestricted. -/
theorem densityBoundedCube_random_slab_threshold
    (K : ℕ) (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ (Ω : Type*) [MeasurableSpace Ω]
      (μ : Measure Ω) (Z : Ω → EuclideanRepresentation K), Measurable Z →
      Measure.map Z μ ≤ ENNReal.ofReal C • uniformCubeCoefficientLaw K →
      ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
        μ.real {ω | |inner ℝ v (Z ω)| ≤ t} ≤ ε := by
  obtain ⟨t, ht, hslab⟩ := densityBoundedCube_uniform_slab_threshold K C ε hC hε
  refine ⟨t, ht, ?_⟩
  intro Ω _ μ Z hZ hbound v hv
  have h := hslab (Measure.map Z μ) hbound v hv
  have hmeas : MeasurableSet {z : EuclideanRepresentation K | |inner ℝ v z| ≤ t} :=
    measurableSet_le (continuous_const.inner continuous_id).abs.measurable measurable_const
  simpa only [Measure.real, Measure.map_apply hZ hmeas] using h

/-- Density-bounded conditional laws give a width-independent incidence
threshold. The same constant works for all input spaces, coefficient laws,
source maps, and learned dictionaries with the displayed primitive bounds.
No lower density bound is needed for this subspace conclusion. -/
theorem exists_density_bounded_sparse_subspace_incidence_threshold
    (K : ℕ) (γ C a b δ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hC : 0 < C)
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Z : Ω → EuclideanRepresentation K), Measurable Z →
        Measure.map Z μ ≤ ENNReal.ofReal C • uniformCubeCoefficientLaw K →
        ∀ (d M : ℕ) (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
          (B : Matrix (Fin d) (Fin M) ℝ) (code : Ω → FeatureVector M),
          Measurable code →
          (∀ z, a * ‖z‖ ≤ ‖F z‖) → (∀ z, ‖F z‖ ≤ b * ‖z‖) →
          (∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1) →
          SparseLowerStable B γ (2 * K) →
          (∀ ω, (nonzeroSupport (code ω)).card ≤ K) →
          (∫⁻ ω, ENNReal.ofReal
            (‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ^ 2) ∂μ)
              ≤ ENNReal.ofReal τ →
          ∃ T : Finset (Fin M), T.card = K ∧
            ‖(LinearMap.range F.toLinearMap).starProjection -
              (euclideanColumnSpan B T).starProjection‖ ≤ δ := by
  obtain ⟨N, hincidence⟩ := exists_uniform_sparse_subspace_incidence_threshold K γ hK hγ hγone
  obtain ⟨t, ht, hslab⟩ := densityBoundedCube_random_slab_threshold K C
    (1 / (4 * ((N : ℝ) + 1))) hC (by positivity)
  obtain ⟨τ, hτ, hthreshold⟩ := hincidence a b ((K : ℝ) + 1) t δ ha hb
    (by positivity) ht hδ hδone
  refine ⟨τ, hτ, ?_⟩
  intro Ω _ μ _ Z hZ hdom d M F B code hcode hlower hupper hunit hstable hsparse hloss
  have hbounded : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ (K : ℝ) + 1 := by
    have h := densityBoundedCube_ae_norm_le K (Measure.map Z μ) (ENNReal.ofReal C) hdom
    exact (ae_map_iff hZ.aemeasurable
      (measurableSet_le measurable_norm measurable_const)).mp h
  exact hthreshold Ω μ Z hZ hbounded (hslab Ω μ Z hZ hdom)
    d M F B code hcode hlower hupper hunit hstable hsparse hloss

end PKG26AtomicFeatures
