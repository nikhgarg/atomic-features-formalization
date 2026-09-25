import PKG26AtomicFeatures.ModulusPopulationRecovery

/-!
# Almost-sure sparse-code feasibility

A measurable code that is feasible almost surely can be set to zero on its
measurable exceptional set. This preserves the actual population loss and
all thresholded F1 scores while supplying pointwise feasible codes to the
sparse-recovery theorems.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The event that a measurable code satisfies a fixed sparsity budget is
a finite union of measurable exact-support events. -/
theorem measurableSet_sparse_code
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (code : Ω → FeatureVector m) (hcode : Measurable code) (K : ℕ) :
    MeasurableSet {x | (nonzeroSupport (code x)).card ≤ K} := by
  classical
  have hset : {x | (nonzeroSupport (code x)).card ≤ K} =
      ⋃ S : {S : Finset (Fin m) // S.card ≤ K}, sourceSupportEvent code S.1 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, sourceSupportEvent]
    constructor
    · intro hx
      exact ⟨⟨nonzeroSupport (code x), hx⟩, rfl⟩
    · rintro ⟨S, hS⟩
      simpa only [hS] using S.2
  rw [hset]
  exact MeasurableSet.iUnion fun S => measurableSet_sourceSupportEvent code hcode S.1

/-- Almost-sure nonnegative sparse codes admit a pointwise feasible version
without changing the code on a set of positive measure. -/
theorem exists_pointwise_feasible_code_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {m K : ℕ}
    (μ : Measure Ω) (code : Ω → FeatureVector m) (hcode : Measurable code)
    (hsparse : ∀ᵐ x ∂μ, (nonzeroSupport (code x)).card ≤ K)
    (hnonneg : ∀ᵐ x ∂μ, ∀ j, 0 ≤ code x j) :
    ∃ code' : Ω → FeatureVector m, Measurable code' ∧ KSparse (K := K) code' ∧
      (∀ x j, 0 ≤ code' x j) ∧ code' =ᵐ[μ] code := by
  classical
  let good : Set Ω := {x | (nonzeroSupport (code x)).card ≤ K ∧ ∀ j, 0 ≤ code x j}
  have hnonnegative : MeasurableSet {x | ∀ j, 0 ≤ code x j} := by
    have hset : {x | ∀ j, 0 ≤ code x j} = ⋂ j, {x | 0 ≤ code x j} := by ext x; simp
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le measurable_const ((measurable_pi_apply j).comp hcode)
  have hgood : MeasurableSet good :=
    (measurableSet_sparse_code code hcode K).inter hnonnegative
  refine ⟨good.indicator code, hcode.indicator hgood, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ good
    · rw [Set.indicator_of_mem hx]
      exact hx.1
    · rw [Set.indicator_of_notMem hx]
      simp [nonzeroSupport]
  · intro x j
    by_cases hx : x ∈ good
    · rw [Set.indicator_of_mem hx]
      exact hx.2 j
    · rw [Set.indicator_of_notMem hx]
      exact le_rfl
  · filter_upwards [hsparse, hnonneg] with x hs hn
    exact Set.indicator_of_mem (show x ∈ good from ⟨hs, hn⟩) code

/-- Almost-surely equal codes have identical nonnegative population loss. -/
theorem actualPopulationSquaredLoss_congr_code_ae
    {Ω : Type*} [MeasurableSpace Ω] {d M m : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (code code' : Ω → FeatureVector m)
    (hcode : code =ᵐ[μ] code') :
    actualPopulationSquaredLoss μ A z B code = actualPopulationSquaredLoss μ A z B code' := by
  apply lintegral_congr_ae
  filter_upwards [hcode] with x hx
  rw [hx]

/-- Every fixed-threshold population F1 score is unchanged by altering a
code on a null set. -/
theorem populationF1_threshold_congr_code_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (truth : Set Ω) (code code' : Ω → FeatureVector m)
    (hcode : code =ᵐ[μ] code') (j : Fin m) (t : ℝ) :
    populationF1 μ truth {x | t < code x j} = populationF1 μ truth {x | t < code' x j} := by
  have hevent : μ.real {x | t < code x j} = μ.real {x | t < code' x j} := by
    apply measureReal_congr
    filter_upwards [hcode] with x hx
    change (t < code x j) = (t < code' x j)
    rw [hx]
  have hinter : μ.real (truth ∩ {x | t < code x j}) =
      μ.real (truth ∩ {x | t < code' x j}) := by
    apply measureReal_congr
    filter_upwards [hcode] with x hx
    change (x ∈ truth ∧ t < code x j) = (x ∈ truth ∧ t < code' x j)
    rw [hx]
  unfold populationF1
  rw [hevent, hinter]

/-- Uniform modulus recovery also holds for actual learned codes whose
nonnegativity and sparsity constraints are imposed only almost surely. -/
theorem exists_modulus_population_feature_presence_recovery_constants_ae
    (K : ℕ) (γ : ℝ) (ψ : ℝ → ℝ) (η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0)) (hη : 0 < η) (hηone : η < 1) :
    ∃ t D : ℝ, 0 < t ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        ModulusSparsePopulation (K := K) μ z ψ →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          HasUnitEuclideanColumns B → SparseLowerStable B γ (2 * K) → Measurable code →
          (∀ᵐ x ∂μ, (nonzeroSupport (code x)).card ≤ K) →
          (∀ᵐ x ∂μ, ∀ j, 0 ≤ code x j) →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ e : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            ∀ i, η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  obtain ⟨t, D, ht, hD, hmain⟩ := exists_modulus_population_feature_presence_recovery_constants
    K γ ψ η hK hγ hγone hψ hη hηone
  refine ⟨t, D, ht, hD, ?_⟩
  intro Ω _ μ _ d M m A z hpop hA hAstable B code hB hBstable hcode hsparse hnonneg L hL hloss
  obtain ⟨code', hcode', hsparse', hnonneg', heq⟩ :=
    exists_pointwise_feasible_code_ae_eq μ code hcode hsparse hnonneg
  have hloss' : actualPopulationSquaredLoss μ A z B code' ≤ ENNReal.ofReal L := by
    rwa [actualPopulationSquaredLoss_congr_code_ae μ A z B code' code heq]
  obtain ⟨e, he⟩ := hmain Ω μ d M m A z hpop hA hAstable B code'
    ⟨hB, hBstable, hcode', hsparse', hnonneg'⟩ L hL hloss'
  refine ⟨e, fun i => ?_⟩
  simpa only [populationF1_threshold_congr_code_ae μ _ code' code heq] using he i

end PKG26AtomicFeatures
