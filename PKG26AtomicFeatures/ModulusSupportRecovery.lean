import PKG26AtomicFeatures.ModulusConditionalRecovery
import PKG26AtomicFeatures.SupportConditioning

/-!
# Conditional source-support recovery from a common small-ball modulus

The population hypothesis below concerns the actual source features and their
actual support-conditioned laws. Coefficients are nonnegative and bounded,
and each positive-mass support obeys the same homogeneous small-ball bound.
No density, independence, separation, or orientation assumption is imposed.

The recovery scales are chosen before the probability space, dictionaries,
and widths. The source synthesis and loss identities are derived from the
observed support, so the conclusion applies to the actual learned code.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The bounded exact-sparsity source assumptions, without any requirement
on conditional coefficient laws or separation between source features. -/
structure BoundedSparsePopulation
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) : Prop where
  measurable : Measurable z
  ae_support_card : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K
  ae_coefficient_bounds : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i ∧ z x i ≤ 1

/-- A bounded exact-sparsity population with a common homogeneous small-ball
bound on every positive-mass support. Convergence of the function `ψ` to zero
is a separate hypothesis of recovery theorems. Null support events impose no
conditional-law requirement. -/
structure ModulusSparsePopulation
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (ψ : ℝ → ℝ) : Prop
    extends BoundedSparsePopulation (K := K) μ z where
  conditional_small_ball : ∀ S : ExactSourceSupport M K,
    μ (sourceSupportEvent z S.1) ≠ 0 →
    ∀ s : ℝ, 0 < s → ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
      (sourceSupportConditionalLaw μ z S.1).real
        {x | |inner ℝ v (sourceSupportCoordinates z S x)| ≤ s} ≤ ψ s

/-- An almost-everywhere property of the original source population remains
valid under its support-conditioned law, including the zero-mass convention. -/
theorem sourceSupportConditionalLaw_ae_of_ae
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (S : Finset (Fin M))
    {p : Ω → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂sourceSupportConditionalLaw μ z S, p x := by
  unfold sourceSupportConditionalLaw
  split_ifs
  · exact hp
  · exact Measure.ae_smul_measure (ae_restrict_of_ae hp) _

/-- Cube-bounded source coordinates supply the dimension-only norm bound
used by conditional recovery. The estimate holds even on null supports,
whose conditional law is the original law by convention. -/
theorem BoundedSparsePopulation.conditional_norm_le
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector M}
    (hpop : BoundedSparsePopulation (K := K) μ z) (S : ExactSourceSupport M K) :
    ∀ᵐ x ∂sourceSupportConditionalLaw μ z S.1,
      ‖sourceSupportCoordinates z S x‖ ≤ (K : ℝ) + 1 := by
  filter_upwards [sourceSupportConditionalLaw_ae_of_ae μ z S.1
    hpop.ae_coefficient_bounds] with x hx
  have hsq : ‖sourceSupportCoordinates z S x‖ ^ 2 ≤ (K : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin K, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        change (z x (sourceSupportEnumeration S i)) ^ 2 ≤ 1
        nlinarith [(hx (sourceSupportEnumeration S i)).1,
          (hx (sourceSupportEnumeration S i)).2]
      _ = K := by simp
  nlinarith [norm_nonneg (sourceSupportCoordinates z S x),
    (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

/-- Uniform unsigned recovery on every positive-mass source support.
Small actual conditional loss supplies one learned support of size `K`
with the requested span accuracy and both conditional activation-error
bounds. The common modulus controls the scales uniformly over all source
populations, ambient dimensions, learned widths, and measurable codes. -/
theorem exists_modulus_support_recovery_scales
    (K : ℕ) (γ : ℝ) (ψ : ℝ → ℝ) (ε δ₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0)) (hε : 0 < ε) (hδ₀ : 0 < δ₀) :
    ∃ t δ τ : ℝ, 0 < t ∧ 0 < δ ∧ δ ≤ δ₀ ∧ 0 < τ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        ModulusSparsePopulation (K := K) μ z ψ →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
          ∀ L : ℝ, 0 ≤ L → L ≤ τ →
          actualPopulationSquaredLoss (sourceSupportConditionalLaw μ z S.1) A z B code ≤
              ENNReal.ofReal L →
          ∃ T : Finset (Fin m), T.card = K ∧
            ‖(euclideanColumnSpan A S.1).starProjection -
              (euclideanColumnSpan B T).starProjection‖ ≤ δ ∧
            (∀ j ∉ T, (sourceSupportConditionalLaw μ z S.1).real {ω | t < code ω j} ≤
              4 * L / (γ ^ 2 * t ^ 2)) ∧
            (∀ j ∈ T, (sourceSupportConditionalLaw μ z S.1).real {ω | code ω j ≤ t} ≤
              4 * L / (γ ^ 2 * t ^ 2) + ε) := by
  obtain ⟨t, δ, τ, ht, hδ, hδle, hτ, hconditional⟩ :=
    exists_uniform_conditional_recovery_scales_of_modulus K γ ψ ε δ₀
      hK hγ hγone hψ hε hδ₀
  refine ⟨t, δ, τ, ht, hδ, hδle, hτ, ?_⟩
  intro Ω _ μ _ d M m A z hpop hAunit hAstable B code hfeas S hS L hL hLτ hloss
  have hZ := measurable_sourceSupportCoordinates z hpop.measurable S
  have hsynth := sourceSupportConditionalLaw_ae_synthesis_eq μ A z hpop.measurable S hS
  have hloss' : (∫⁻ ω, ENNReal.ofReal
      (‖selectedSourceSynthesis A (sourceSupportEnumeration S) (sourceSupportCoordinates z S ω) -
        representationToEuclidean d (B.mulVec (code ω))‖ ^ 2)
        ∂sourceSupportConditionalLaw μ z S.1) ≤ ENNReal.ofReal L := by
    apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hloss
    filter_upwards [hsynth] with ω hω
    rw [hω]
  obtain ⟨T, hT, hgap, hfp, hfn⟩ := hconditional Ω
    (sourceSupportConditionalLaw μ z S.1) (sourceSupportCoordinates z S) hZ
    (hpop.toBoundedSparsePopulation.conditional_norm_le S) (hpop.conditional_small_ball S hS)
    d m (selectedSourceSynthesis A (sourceSupportEnumeration S)) B code hfeas.2.2.1
    (selectedSourceSynthesis_lower A _ γ hAstable)
    (selectedSourceSynthesis_upper A _ (fun j => (hAunit j).le))
    (fun j => (hfeas.1 j).le) hfeas.2.1 hfeas.2.2.2.1 hfeas.2.2.2.2 L hL hLτ hloss'
  refine ⟨T, hT, ?_, hfp, hfn⟩
  simpa only [range_selectedSourceSynthesis, sourceSupportEnumeration_image] using hgap

end PKG26AtomicFeatures
