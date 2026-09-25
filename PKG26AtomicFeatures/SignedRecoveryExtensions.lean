import PKG26AtomicFeatures.FiniteScalePopulationRecovery
import PKG26AtomicFeatures.ModulusFiniteScaleBridge
import PKG26AtomicFeatures.RegularPopulationModulus
import PKG26AtomicFeatures.SparseCodeSanitation

/-!
# Signed recovery under homogeneous modulus and upper-density assumptions

A common vanishing homogeneous small-ball modulus supplies the fixed
incidence and coordinate-tail scales required by finite-scale recovery.
Under source-feature separation, one injection simultaneously recovers
signed atom similarity and thresholded activation F1. All constants precede
the population, probability space, ambient dimension, and dictionary widths.

Conditional upper domination by the coefficient cube is a primitive special
case. Its source-coordinate bounds are derived from the actual conditional
laws. The regular-population specialization is uniform in the unused lower
density parameter. Almost-sure learned-code feasibility is also sufficient.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Uniform signed and feature-presence recovery from a common homogeneous
small-ball modulus. The source separation condition applies to actual feature
absence events, and the reconstruction loss is that of the actual learned
code. No coefficient density or independence assumption is made. -/
theorem exists_signed_modulus_recovery_constants
    (K : ℕ) (γ ρ : ℝ) (ψ : ℝ → ℝ) (η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0)) (hη : 0 < η) (hηone : η < 1) :
    ∃ t D : ℝ, 0 < t ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        ModulusSparsePopulation (K := K) μ z ψ →
        (∀ i j : Fin M, i ≠ j → 0 < featurePrevalence μ z i →
          ρ * featurePrevalence μ z i ≤ μ.real {x | 0 < z x i ∧ z x j = 0}) →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ e : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            ∀ i,
              η < inner ℝ (representationToEuclidean d (A.col i.1))
                (representationToEuclidean d (B.col (e i))) ∧
              η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  obtain ⟨N, hfinite⟩ := exists_finite_scale_population_recovery_constants K γ hK hγ hγone
  obtain ⟨s₀, a, hs₀, ha, haone, hscales⟩ :=
    exists_finite_scale_population_scales_of_modulus K N ψ ((1 - η) / 4)
      hψ (div_pos (sub_pos.mpr hηone) (by norm_num))
  obtain ⟨t, D, ht, hD, _hteq, hmain⟩ :=
    hfinite ρ η s₀ a hρ hρone hη hηone hs₀ ha haone
  refine ⟨t, D, ht, hD, ?_⟩
  intro Ω _ μ _ d M m A z hpop
  exact hmain Ω μ d M m A z (hscales Ω μ M z hpop)

/-- Signed modulus recovery is unchanged when sparsity and nonnegativity of
the actual measurable code hold only almost surely. A pointwise feasible
version has the same actual loss and every thresholded F1 score. -/
theorem exists_signed_modulus_recovery_constants_ae
    (K : ℕ) (γ ρ : ℝ) (ψ : ℝ → ℝ) (η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0)) (hη : 0 < η) (hηone : η < 1) :
    ∃ t D : ℝ, 0 < t ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        ModulusSparsePopulation (K := K) μ z ψ →
        (∀ i j : Fin M, i ≠ j → 0 < featurePrevalence μ z i →
          ρ * featurePrevalence μ z i ≤ μ.real {x | 0 < z x i ∧ z x j = 0}) →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          HasUnitEuclideanColumns B → SparseLowerStable B γ (2 * K) → Measurable code →
          (∀ᵐ x ∂μ, (nonzeroSupport (code x)).card ≤ K) →
          (∀ᵐ x ∂μ, ∀ j, 0 ≤ code x j) →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ e : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            ∀ i,
              η < inner ℝ (representationToEuclidean d (A.col i.1))
                (representationToEuclidean d (B.col (e i))) ∧
              η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  obtain ⟨t, D, ht, hD, hmain⟩ := exists_signed_modulus_recovery_constants
    K γ ρ ψ η hK hγ hγone hρ hρone hψ hη hηone
  refine ⟨t, D, ht, hD, ?_⟩
  intro Ω _ μ _ d M m A z hpop hsep hA hAstable B code hB hBstable
    hcode hsparse hnonneg L hL hloss
  obtain ⟨code', hcode', hsparse', hnonneg', heq⟩ :=
    exists_pointwise_feasible_code_ae_eq μ code hcode hsparse hnonneg
  have hloss' : actualPopulationSquaredLoss μ A z B code' ≤ ENNReal.ofReal L := by
    rwa [actualPopulationSquaredLoss_congr_code_ae μ A z B code' code heq]
  obtain ⟨e, he⟩ := hmain Ω μ d M m A z hpop hsep hA hAstable B code'
    ⟨hB, hBstable, hcode', hsparse', hnonneg'⟩ L hL hloss'
  refine ⟨e, fun i => ⟨(he i).1, ?_⟩⟩
  simpa only [populationF1_threshold_congr_code_ae μ _ code' code heq] using (he i).2

/-- A conditional upper density bound alone supplies signed and activation
recovery. The almost-sure source cube bounds follow from domination of the
actual exact-support laws; no lower density or separate coefficient-bound
premise is required. The source supports satisfy the displayed separation
condition, and learned codes need only be feasible almost surely. -/
theorem exists_signed_upper_density_recovery_constants
    (K : ℕ) (γ ρ C η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hC : 0 ≤ C)
    (hη : 0 < η) (hηone : η < 1) :
    ∃ t D : ℝ, 0 < t ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        Measurable z → (∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K) →
        (∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
          Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) ≤
            ENNReal.ofReal C • uniformCubeCoefficientLaw K) →
        (∀ i j : Fin M, i ≠ j → 0 < featurePrevalence μ z i →
          ρ * featurePrevalence μ z i ≤ μ.real {x | 0 < z x i ∧ z x j = 0}) →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          HasUnitEuclideanColumns B → SparseLowerStable B γ (2 * K) → Measurable code →
          (∀ᵐ x ∂μ, (nonzeroSupport (code x)).card ≤ K) →
          (∀ᵐ x ∂μ, ∀ j, 0 ≤ code x j) →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ e : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            ∀ i,
              η < inner ℝ (representationToEuclidean d (A.col i.1))
                (representationToEuclidean d (B.col (e i))) ∧
              η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  obtain ⟨t, D, ht, hD, hmain⟩ := exists_signed_modulus_recovery_constants_ae
    K γ ρ (fun s => C * uniformCubeSlabModulus K s) η hK hγ hγone hρ hρone
    (upperDensitySlabModulus_tendsto_zero K C) hη hηone
  refine ⟨t, D, ht, hD, ?_⟩
  intro Ω _ μ _ d M m A z hz hexact hdom
  exact hmain Ω μ d M m A z
    (modulusSparsePopulation_of_conditional_upper_density μ z hz hexact C hC hdom)

/-- The existing regular-population assumptions are a special case of
upper-density signed recovery. Constants are chosen before the lower-density
parameter as well as before all spaces, laws, and dimensions, so no lower
bound on the coefficient density enters these constants. -/
theorem exists_signed_regular_population_recovery_constants
    (K : ℕ) (γ ρ cUpper η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hcUpper : 0 ≤ cUpper)
    (hη : 0 < η) (hηone : η < 1) :
    ∃ t D : ℝ, 0 < t ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
        (cLower : ℝ), RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          HasUnitEuclideanColumns B → SparseLowerStable B γ (2 * K) → Measurable code →
          (∀ᵐ x ∂μ, (nonzeroSupport (code x)).card ≤ K) →
          (∀ᵐ x ∂μ, ∀ j, 0 ≤ code x j) →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ e : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            ∀ i,
              η < inner ℝ (representationToEuclidean d (A.col i.1))
                (representationToEuclidean d (B.col (e i))) ∧
              η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  obtain ⟨t, D, ht, hD, hmain⟩ := exists_signed_upper_density_recovery_constants
    K γ ρ cUpper η hK hγ hγone hρ hρone hcUpper hη hηone
  refine ⟨t, D, ht, hD, ?_⟩
  intro Ω _ μ _ d M m A z cLower hreg
  exact hmain Ω μ d M m A z hreg.1 hreg.2.1
    (fun S hS => (hreg.coefficientLaw_bounds S hS).2) hreg.2.2.1

end PKG26AtomicFeatures
