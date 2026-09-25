import PKG26AtomicFeatures.ModulusSupportRecovery

/-!
# Sparse support incidence from one fixed small-ball scale

The number of directions needed by incidence is chosen before the requested
span accuracy. Thus a single fixed slab bound can supply arbitrarily accurate
support spans at a sufficiently small loss, including for finite coefficient
clouds. Source-coordinate lower tails are a separate primitive used to orient
the globally matched atoms and recover their actual activation events.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped ENNReal

/-- One homogeneous slab scale and one source-coordinate tail scale, imposed
on every actual positive-mass support. No density or independence is assumed. -/
structure FiniteScaleSparsePopulation
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (N : ℕ) (s₀ a ε : ℝ) : Prop
    extends BoundedSparsePopulation (K := K) μ z where
  conditional_incidence : ∀ S : ExactSourceSupport M K,
    μ (sourceSupportEvent z S.1) ≠ 0 →
    ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
      (sourceSupportConditionalLaw μ z S.1).real
        {x | |inner ℝ v (sourceSupportCoordinates z S x)| ≤ s₀} ≤
          1 / (4 * ((N : ℝ) + 1))
  conditional_coordinate_tail : ∀ S : ExactSourceSupport M K,
    μ (sourceSupportEvent z S.1) ≠ 0 → ∀ i ∈ S.1,
      (sourceSupportConditionalLaw μ z S.1).real {x | z x i ≤ a} ≤ ε

/-- The incidence count is fixed before both the homogeneous slab scale and
the requested projector accuracy. The resulting loss budget is uniform over
all actual source populations, ambient dimensions, and learned widths. -/
theorem exists_finite_scale_support_incidence_threshold
    (K : ℕ) (γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) :
    ∃ N : ℕ, ∀ s₀ δ : ℝ, 0 < s₀ → 0 < δ → δ < 1 →
      ∃ τ : ℝ, 0 < τ ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
          BoundedSparsePopulation (K := K) μ z →
          (∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
            ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
              (sourceSupportConditionalLaw μ z S.1).real
                {x | |inner ℝ v (sourceSupportCoordinates z S x)| ≤ s₀} ≤
                  1 / (4 * ((N : ℝ) + 1))) →
          HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
          ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
            IsFeasibleRecoveryPair B code γ K →
            ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
            actualPopulationSquaredLoss (sourceSupportConditionalLaw μ z S.1) A z B code ≤
                ENNReal.ofReal τ →
            ∃ T : Finset (Fin m), T.card = K ∧
              ‖(euclideanColumnSpan A S.1).starProjection -
                (euclideanColumnSpan B T).starProjection‖ ≤ δ := by
  obtain ⟨N, hincidence⟩ := exists_uniform_sparse_subspace_incidence_threshold K γ hK hγ hγone
  refine ⟨N, ?_⟩
  intro s₀ δ hs₀ hδ hδone
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  obtain ⟨τ, hτ, hconditional⟩ := hincidence γ (K : ℝ) ((K : ℝ) + 1) s₀ δ
    hγ hKr (by positivity) hs₀ hδ hδone
  refine ⟨τ, hτ, ?_⟩
  intro Ω _ μ _ d M m A z hpop hslab hAunit hAstable B code hfeas S hS hloss
  have hZ := measurable_sourceSupportCoordinates z hpop.measurable S
  have hsynth := sourceSupportConditionalLaw_ae_synthesis_eq μ A z hpop.measurable S hS
  have hloss' : (∫⁻ ω, ENNReal.ofReal
      (‖selectedSourceSynthesis A (sourceSupportEnumeration S) (sourceSupportCoordinates z S ω) -
        representationToEuclidean d (B.mulVec (code ω))‖ ^ 2)
        ∂sourceSupportConditionalLaw μ z S.1) ≤ ENNReal.ofReal τ := by
    apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hloss
    filter_upwards [hsynth] with ω hω
    rw [hω]
  obtain ⟨T, hT, hgap⟩ := hconditional Ω
    (sourceSupportConditionalLaw μ z S.1) (sourceSupportCoordinates z S) hZ
    (hpop.conditional_norm_le S) (hslab S hS) d m
    (selectedSourceSynthesis A (sourceSupportEnumeration S)) B code hfeas.2.2.1
    (selectedSourceSynthesis_lower A _ γ hAstable)
    (selectedSourceSynthesis_upper A _ (fun j => (hAunit j).le))
    (fun j => (hfeas.1 j).le) hfeas.2.1 hfeas.2.2.2.1 hloss'
  refine ⟨T, hT, ?_⟩
  simpa only [range_selectedSourceSynthesis, sourceSupportEnumeration_image] using hgap

end PKG26AtomicFeatures
