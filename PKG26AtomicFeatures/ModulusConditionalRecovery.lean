import PKG26AtomicFeatures.SparseSubspaceIncidence
import PKG26AtomicFeatures.ThresholdedFeatureRecovery

/-!
# Conditional recovery from homogeneous small-ball bounds

Two homogeneous slab estimates suffice for unsigned conditional recovery.
One supplies sparse-subspace incidence, and the other controls activation
errors through the projected coefficient functionals. The incidence count
is chosen before either slab scale or the requested projector accuracy.
The resulting constants are uniform over probability spaces, coefficient
laws, ambient dimensions, and learned widths.

A common small-ball modulus tending to zero supplies both scales. Neither
the two-scale result nor its modulus corollary assumes a density, independent
coefficients, or any orientation of the selected learned atoms.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The incidence count depends only on sparsity and the decoding margin.
After fixing two positive slab scales and a projector cap, one threshold and
one loss budget give the selected span and both conditional activation-error
bounds. The actual code and coefficients may depend separately on the random
outcome. The activation error parameter is constrained by its stated slab
bound and needs no separate positivity assumption. -/
theorem exists_uniform_conditional_recovery_scales_of_two_slabs
    (K : ℕ) (γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) :
    ∃ N : ℕ, ∀ sI sF ε δ₀ : ℝ, 0 < sI → 0 < sF → 0 < δ₀ →
      ∃ t δ τ : ℝ, 0 < t ∧ 0 < δ ∧ δ ≤ δ₀ ∧ 0 < τ ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Z : Ω → EuclideanRepresentation K), Measurable Z →
          (∀ᵐ ω ∂μ, ‖Z ω‖ ≤ (K : ℝ) + 1) →
          (∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
            μ.real {ω | |inner ℝ v (Z ω)| ≤ sI} ≤ 1 / (4 * ((N : ℝ) + 1))) →
          (∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
            μ.real {ω | |inner ℝ v (Z ω)| ≤ sF} ≤ ε) →
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
              (∀ j ∈ T, μ.real {ω | code ω j ≤ t} ≤ 4 * L / (γ ^ 2 * t ^ 2) + ε) := by
  obtain ⟨N, hincidence⟩ := exists_uniform_sparse_subspace_incidence_threshold K γ hK hγ hγone
  refine ⟨N, ?_⟩
  intro sI sF ε δ₀ hsI hsF hδ₀
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  let t := (γ / (2 * (K : ℝ))) * sF / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hts : 2 * t / (γ / (2 * (K : ℝ))) = sF := by dsimp [t]; field_simp
  let δ := min δ₀ (min (1 / 2 : ℝ) (min (γ / (2 * (K : ℝ)))
    (γ * t / (2 * (K : ℝ) * ((K : ℝ) + 1)))))
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
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (K : ℝ) * ((K : ℝ) + 1))).mp h
    nlinarith
  obtain ⟨τ, hτ, hinc⟩ := hincidence γ (K : ℝ) ((K : ℝ) + 1) sI δ
    hγ hKr (by positivity) hsI hδ (by linarith)
  refine ⟨t, δ, τ, ht, hδ, hδle, hτ, ?_⟩
  intro Ω _ μ _ Z hZ hbounded hslabI hslabF d m F B code hcode hlower hupper
    hunit hstable hsparse hnonneg L hL hLτ hloss
  obtain ⟨T, hT, hgap⟩ := hinc Ω μ Z hZ hbounded hslabI d m F B code hcode
    hlower hupper hunit hstable hsparse (hloss.trans (ENNReal.ofReal_le_ofReal hLτ))
  have hslab : ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
      μ.real {ω | |inner ℝ v (Z ω)| ≤ 2 * t / (γ / (2 * (K : ℝ)))} ≤ ε := by
    rw [hts]
    exact hslabF
  have herr := thresholded_feature_error_probabilities_of_projector_bound μ Z hZ code hcode F B T
    γ (K : ℝ) γ δ ((K : ℝ) + 1) t ε L hK hγ hγ hδ.le ht hL hT hstable hunit
    hlower hupper hδsmall hgap hbounded hδproj hnonneg hsparse hslab hloss
  exact ⟨T, hT, hgap, herr.1, herr.2⟩

/-- A common homogeneous small-ball modulus tending to zero gives uniform
unsigned recovery scales. Boundedness and the modulus are imposed on the
actual random coefficients; no absolute continuity is required. -/
theorem exists_uniform_conditional_recovery_scales_of_modulus
    (K : ℕ) (γ : ℝ) (ψ : ℝ → ℝ) (ε δ₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0)) (hε : 0 < ε) (hδ₀ : 0 < δ₀) :
    ∃ t δ τ : ℝ, 0 < t ∧ 0 < δ ∧ δ ≤ δ₀ ∧ 0 < τ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Z : Ω → EuclideanRepresentation K), Measurable Z →
        (∀ᵐ ω ∂μ, ‖Z ω‖ ≤ (K : ℝ) + 1) →
        (∀ s : ℝ, 0 < s → ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
          μ.real {ω | |inner ℝ v (Z ω)| ≤ s} ≤ ψ s) →
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
            (∀ j ∈ T, μ.real {ω | code ω j ≤ t} ≤ 4 * L / (γ ^ 2 * t ^ 2) + ε) := by
  have hscale (r : ℝ) (hr : 0 < r) : ∃ s : ℝ, 0 < s ∧ ψ s ≤ r := by
    have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ψ s < r := hψ.eventually (Iio_mem_nhds hr)
    have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
    obtain ⟨s, hs, hsr⟩ := (hpos.and hsmall).exists
    exact ⟨s, hs, hsr.le⟩
  obtain ⟨N, hscales⟩ := exists_uniform_conditional_recovery_scales_of_two_slabs K γ hK hγ hγone
  obtain ⟨sI, hsI, hψI⟩ := hscale (1 / (4 * ((N : ℝ) + 1))) (by positivity)
  obtain ⟨sF, hsF, hψF⟩ := hscale ε hε
  obtain ⟨t, δ, τ, ht, hδ, hδle, hτ, hlocal⟩ := hscales sI sF ε δ₀ hsI hsF hδ₀
  refine ⟨t, δ, τ, ht, hδ, hδle, hτ, ?_⟩
  intro Ω _ μ _ Z hZ hbounded hslab
  exact hlocal Ω μ Z hZ hbounded
    (fun v hv => (hslab sI hsI v hv).trans hψI)
    (fun v hv => (hslab sF hsF v hv).trans hψF)

end PKG26AtomicFeatures
