import PKG26AtomicFeatures.DensityBoundedCoefficients
import PKG26AtomicFeatures.ThresholdedFeatureRecovery
import PKG26AtomicFeatures.SignedLineGeometry

/-!
# Uniform conditional recovery scales

One activation threshold, one subspace tolerance and one positive loss
threshold work for all conditional laws with the stated density bounds.
They are chosen before the input space, ambient dimension, source width and
learned width. Each selected support has the prescribed span accuracy,
conditional activation-error bounds, and no wrongly oriented atom.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped ENNReal

/-- Uniform conditional recovery from the primitive decoding margin,
sparsity, density bounds and requested errors. The loss variable is the
actual conditional squared loss bound, not a geometric proxy. -/
theorem exists_uniform_conditional_recovery_scales
    (K : ℕ) (γ cLower cUpper ε δ₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper)
    (hε : 0 < ε) (hδ₀ : 0 < δ₀) :
    ∃ t δ τ : ℝ, 0 < t ∧ 0 < δ ∧ δ ≤ δ₀ ∧ 0 < τ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Z : Ω → EuclideanRepresentation K), Measurable Z →
        ENNReal.ofReal cLower • uniformCubeCoefficientLaw K ≤ Measure.map Z μ →
        Measure.map Z μ ≤ ENNReal.ofReal cUpper • uniformCubeCoefficientLaw K →
        ∀ (d m : ℕ) (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
          (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          Measurable code →
          (∀ z, γ * ‖z‖ ≤ ‖F z‖) → (∀ z, ‖F z‖ ≤ (K : ℝ) * ‖z‖) →
          (∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1) →
          SparseLowerStable B γ (2 * K) →
          (∀ ω, (nonzeroSupport (code ω)).card ≤ K) →
          (∀ ω j, 0 ≤ code ω j) →
          ∀ L : ℝ, 0 ≤ L → L ≤ τ →
          (∫⁻ ω, ENNReal.ofReal
            (‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ^ 2) ∂μ)
              ≤ ENNReal.ofReal L →
          ∃ T : Finset (Fin m), T.card = K ∧
            ‖(LinearMap.range F.toLinearMap).starProjection -
              (euclideanColumnSpan B T).starProjection‖ ≤ δ ∧
            (∀ j ∉ T, μ.real {ω | t < code ω j} ≤ 4 * L / (γ ^ 2 * t ^ 2)) ∧
            (∀ j ∈ T, μ.real {ω | code ω j ≤ t} ≤ 4 * L / (γ ^ 2 * t ^ 2) + ε) ∧
            ∀ i : Fin K, ∀ j ∈ T,
              γ / 2 < ‖F (coefficientBasisVector i) + representationToEuclidean d (B.col j)‖ := by
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  obtain ⟨s, hs, hslab⟩ := densityBoundedCube_random_slab_threshold K cUpper ε hcUpper hε
  let t := (γ / (2 * (K : ℝ))) * s / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hts : 2 * t / (γ / (2 * (K : ℝ))) = s := by dsimp [t]; field_simp
  let δ := min δ₀ (min (1 / 2 : ℝ) (min (γ / (2 * (K : ℝ)))
    (min (γ * t / (2 * (K : ℝ) * ((K : ℝ) + 1)))
      (γ / (16 * (K : ℝ) * ((K : ℝ) + 1))))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδsmall : δ * (K : ℝ) ≤ γ / 2 := by
    have h : δ ≤ γ / (2 * (K : ℝ)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (K : ℝ))).mp h
    nlinarith
  have hδproj : δ * (K : ℝ) * ((K : ℝ) + 1) ≤ γ * t / 2 := by
    have h : δ ≤ γ * t / (2 * (K : ℝ) * ((K : ℝ) + 1)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (K : ℝ) * ((K : ℝ) + 1))).mp h
    nlinarith
  have hδorient : δ * (K : ℝ) * ((K : ℝ) + 1) ≤ γ / 16 := by
    have h : δ ≤ γ / (16 * (K : ℝ) * ((K : ℝ) + 1)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * (K : ℝ) * ((K : ℝ) + 1))).mp h
    nlinarith
  obtain ⟨τ₀, hτ₀, hinc⟩ := exists_density_bounded_sparse_subspace_incidence_threshold
    K γ cUpper γ (K : ℝ) δ hK hγ hγone hcUpper hγ hKr hδ (by linarith)
  have hfloor := orientationLossFloor_pos hK γ (K : ℝ) cLower hγ hKr hcLower
  let τ := min τ₀ (orientationLossFloor K γ (K : ℝ) cLower / 2)
  have hτ : 0 < τ := lt_min hτ₀ (half_pos hfloor)
  refine ⟨t, δ, τ, ht, hδ, hδle, hτ, ?_⟩
  intro Ω _ μ _ Z hZ hdomLower hdomUpper d m F B code hcode hlower hupper hunit hstable
    hsparse hnonneg L hL hLτ hloss
  have hLτ₀ : L ≤ τ₀ := hLτ.trans (min_le_left _ _)
  obtain ⟨T, hT, hgap⟩ := hinc Ω μ Z hZ hdomUpper d m F B code hcode hlower hupper
    hunit hstable hsparse (hloss.trans (ENNReal.ofReal_le_ofReal hLτ₀))
  have hbounded : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ (K : ℝ) + 1 := by
    have h := densityBoundedCube_ae_norm_le K (Measure.map Z μ) (ENNReal.ofReal cUpper) hdomUpper
    exact (ae_map_iff hZ.aemeasurable
      (measurableSet_le measurable_norm measurable_const)).mp h
  have hslab' : ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
      μ.real {ω | |inner ℝ v (Z ω)| ≤ 2 * t / (γ / (2 * (K : ℝ)))} ≤ ε := by
    rw [hts]
    exact hslab Ω μ Z hZ hdomUpper
  have herr := thresholded_feature_error_probabilities_of_projector_bound μ Z hZ code hcode F B T
    γ (K : ℝ) γ δ ((K : ℝ) + 1) t ε L hK hγ hγ hδ.le ht hL hT hstable hunit
    hlower hupper hδsmall hgap hbounded hδproj hnonneg hsparse hslab' hloss
  refine ⟨T, hT, hgap, herr.1, herr.2, ?_⟩
  intro i j hj
  by_contra hwrong
  have hfloorLe := wrong_orientation_squared_loss_lower_bound μ Z hZ F B T code
    γ (K : ℝ) cLower δ hγ hKr hcLower hδ.le hdomLower hT.le hstable hupper hgap hδorient
    i j hj (le_of_not_gt hwrong) hsparse hnonneg
  have hLfloor : L < orientationLossFloor K γ (K : ℝ) cLower :=
    (hLτ.trans (min_le_right _ _)).trans_lt (half_lt_self hfloor)
  have hstrict : ENNReal.ofReal L < ENNReal.ofReal (orientationLossFloor K γ (K : ℝ) cLower) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hL).mpr hLfloor
  exact (not_le_of_gt hstrict) (hfloorLe.trans hloss)

end PKG26AtomicFeatures
