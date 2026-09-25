import PKG26AtomicFeatures.ConditionalRecoveryScales
import PKG26AtomicFeatures.SupportConditioning

/-!
# Conditional recovery for actual source supports

The conditional recovery estimates below use the given data distribution,
source dictionary and encoder. The restricted synthesis maps, their decoding
bounds, the conditional coefficient laws and the loss identity are derived
from those primitives.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped ENNReal

@[simp] theorem selectedSourceSynthesis_coefficientBasisVector {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (e : Fin K ↪ Fin M) (i : Fin K) :
    selectedSourceSynthesis A e (coefficientBasisVector i) =
      representationToEuclidean d (A.col (e i)) := by
  change representationToEuclidean d ((A.submatrix id e).mulVec
    ((representationToEuclidean K).symm (representationToEuclidean K (Pi.single i 1)))) = _
  rw [(representationToEuclidean K).symm_apply_apply, Matrix.mulVec_single_one]
  rfl

/-- Uniform thresholds for every positive-mass source support. The same
selected learned support simultaneously controls span error, activation
errors and orientation of all source atoms on that support. -/
theorem exists_regular_support_recovery_scales
    (K : ℕ) (γ cLower cUpper ε δ₀ : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper)
    (hε : 0 < ε) (hδ₀ : 0 < δ₀) :
    ∃ t δ τ : ℝ, 0 < t ∧ 0 < δ ∧ δ ≤ δ₀ ∧ 0 < τ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
        (ρ : ℝ), RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
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
              4 * L / (γ ^ 2 * t ^ 2) + ε) ∧
            ∀ i ∈ S.1, ∀ j ∈ T,
              γ / 2 < ‖representationToEuclidean d (A.col i) +
                representationToEuclidean d (B.col j)‖ := by
  obtain ⟨t, δ, τ, ht, hδ, hδle, hτ, hconditional⟩ :=
    exists_uniform_conditional_recovery_scales K γ cLower cUpper ε δ₀
      hK hγ hγone hcLower hcUpper hε hδ₀
  refine ⟨t, δ, τ, ht, hδ, hδle, hτ, ?_⟩
  intro Ω _ μ _ d M m A z ρ hreg hAunit hAstable B code hfeas S hS L hL hLτ hloss
  have hlaw := hreg.coefficientLaw_bounds S hS
  have hZ := measurable_sourceSupportCoordinates z hreg.1 S
  have hsynth := sourceSupportConditionalLaw_ae_synthesis_eq μ A z hreg.1 S hS
  have hloss' : (∫⁻ ω, ENNReal.ofReal
      (‖selectedSourceSynthesis A (sourceSupportEnumeration S) (sourceSupportCoordinates z S ω) -
        representationToEuclidean d (B.mulVec (code ω))‖ ^ 2)
        ∂sourceSupportConditionalLaw μ z S.1) ≤ ENNReal.ofReal L := by
    apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hloss
    filter_upwards [hsynth] with ω hω
    rw [hω]
  obtain ⟨T, hT, hgap, hfp, hfn, horient⟩ := hconditional Ω
    (sourceSupportConditionalLaw μ z S.1) (sourceSupportCoordinates z S) hZ hlaw.1 hlaw.2
    d m (selectedSourceSynthesis A (sourceSupportEnumeration S)) B code hfeas.2.2.1
    (selectedSourceSynthesis_lower A _ γ hAstable)
    (selectedSourceSynthesis_upper A _ (fun j => (hAunit j).le))
    (fun j => (hfeas.1 j).le) hfeas.2.1 hfeas.2.2.2.1 hfeas.2.2.2.2 L hL hLτ hloss'
  have hgap' : ‖(euclideanColumnSpan A S.1).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ := by
    simpa only [range_selectedSourceSynthesis, sourceSupportEnumeration_image] using hgap
  refine ⟨T, hT, hgap', hfp, hfn, ?_⟩
  intro i hi j hj
  have hi' : i ∈ Finset.univ.image (sourceSupportEnumeration S) := by
    rwa [sourceSupportEnumeration_image]
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi'
  simpa only [selectedSourceSynthesis_coefficientBasisVector] using horient k j hj

end PKG26AtomicFeatures
