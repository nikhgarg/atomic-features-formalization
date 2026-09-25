import PKG26AtomicFeatures.TailRecoveryPrinciple
import PKG26AtomicFeatures.TestableMatchingMetrics

/-!
# One constant for recovery and both matching predictions

A single tail-recovery invocation at the larger of the requested feature
confidence and the geometric matching confidence supplies the same threshold
and tail constant throughout. Population-specific recovery sets retain their
own actual prevalences and rankings.
-/

namespace PKG26AtomicFeatures

universe u v

open MeasureTheory
open scoped InnerProductSpace

/-- Increasing the tail multiplier can only shrink the recoverable set
when marginal weights are nonnegative. No sorting assumption is needed. -/
theorem tailRecoverableFeatures_antitone_constant {M : ℕ}
    (p : Fin M → ℝ) (hp : ∀ i, 0 ≤ p i) (σ : Equiv.Perm (Fin M)) (m : ℕ) :
    Antitone (fun C : ℝ => tailRecoverableFeatures p σ C m) := by
  intro C C' hCC' i hi
  obtain ⟨hpos, hbound⟩ := (mem_tailRecoverableFeatures p σ C' m i).mp hi
  exact (mem_tailRecoverableFeatures p σ C m i).mpr ⟨hpos,
    (mul_le_mul_of_nonneg_right hCC' (rankedFeatureTail_nonneg p hp σ m)).trans hbound⟩

/-- The same positive threshold and tail constant give actual atom/feature
recovery, simultaneous matching across larger widths, and matching across
arbitrary other regular populations. The confidence for recovery and the
error parameter for matching may be chosen independently. -/
theorem exists_common_recovery_prediction_constants
    (K : ℕ) (γ ρ cLower cUpper C₀ η ε : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hρ : 0 < ρ)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper) (hC₀ : 0 < C₀)
    (hη : 0 < η) (hηone : η < 1) (hε : 0 < ε) (_hεone : ε < 1) :
    ∃ t C : ℝ, 0 < t ∧ 1 < C ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (σ : Equiv.Perm (Fin M)), m ≤ M →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsApproximatelyOptimalRecoveryPair μ A z B code γ C₀ K →
          (∃ e : tailRecoverableFeatures (featurePrevalence μ z) σ C m ↪ Fin m,
            ∀ i,
              η < inner ℝ (representationToEuclidean d (A.col i.1))
                (representationToEuclidean d (B.col (e i))) ∧
              η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)}) ∧
          (∀ (ι : Type v) [Fintype ι] (width : ι → ℕ),
            (∀ l, m ≤ width l) → (∀ l, width l ≤ M) →
            ∀ (B' : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ)
              (code' : ∀ l, Ω → FeatureVector (width l)),
              (∀ l, IsApproximatelyOptimalRecoveryPair μ A z (B' l) (code' l) γ C₀ K) →
              (tailRecoverableFeatures (featurePrevalence μ z) σ C m).card ≤
                testableMatchingMetric width B B' (1 - 2 * ε ^ 2)) ∧
          (∀ (μ' : Measure Ω) [IsProbabilityMeasure μ'],
            RegularSparsePopulation (K := K) μ' z ρ cLower cUpper →
            ∀ (σ' : Equiv.Perm (Fin M)) (B' : Matrix (Fin d) (Fin m) ℝ)
              (code' : Ω → FeatureVector m),
              IsApproximatelyOptimalRecoveryPair μ' A z B' code' γ C₀ K →
              (tailRecoverableFeatures (featurePrevalence μ z) σ C m ∩
                tailRecoverableFeatures (featurePrevalence μ' z) σ' C m).card ≤
                  testableMatchingMetric (fun _ : Unit => m) B (fun _ => B')
                    (1 - 2 * ε ^ 2)) := by
  classical
  let q := max η (1 - ε ^ 2 / 2)
  have hηq : η ≤ q := le_max_left _ _
  have hgeometryq : 1 - ε ^ 2 / 2 ≤ q := le_max_right _ _
  have hq : 0 < q := hη.trans_le hηq
  have hqone : q < 1 := max_lt hηone (by nlinarith)
  obtain ⟨t, C, ht, hC, hrecovery⟩ := exists_tail_recovery_constants
    K γ ρ cLower cUpper C₀ q hK hγ hγone hρ hcLower hcUpper hC₀ hq hqone
  refine ⟨t, C, ht, hC, ?_⟩
  intro Ω _ μ _ d M m A z hreg hAunit hAstable
    σ hm B code hopt
  obtain ⟨e₀, he₀⟩ := hrecovery Ω μ d M m A z hreg hAunit hAstable
    σ hm B code hopt
  refine ⟨⟨e₀, fun i => ⟨hηq.trans_lt (he₀ i).1, hηq.trans_lt (he₀ i).2⟩⟩, ?_, ?_⟩
  · intro ι _ width hwidth hwidthM B' code' hopt'
    choose e he using fun l => hrecovery Ω μ d M (width l) A z hreg hAunit hAstable
      σ (hwidthM l) (B' l) (code' l) (hopt' l)
    let R := tailRecoverableFeatures (featurePrevalence μ z) σ C m
    let restrict (l : ι) : R ↪
        tailRecoverableFeatures (featurePrevalence μ z) σ C (width l) :=
      { toFun := fun i => ⟨i.1,
          tailRecoverableFeatures_subset_of_width_le (featurePrevalence μ z)
            (fun _ => measureReal_nonneg) σ C (by linarith) (hwidth l) i.2⟩
        inj' := fun _ _ h => Subtype.ext (congrArg
          (fun j : tailRecoverableFeatures (featurePrevalence μ z) σ C (width l) => j.1) h) }
    have hmetric := testableMatchingMetric_ge_of_common_reference_inner width B B'
      (fun i : R => representationToEuclidean d (A.col i.1))
      (fun i => hAunit i.1) e₀ (fun l => (restrict l).trans (e l))
      (fun i => hopt.1.1 (e₀ i))
      (fun l i => (hopt' l).1.1 (e l (restrict l i))) ε hε.le
      (fun i => hgeometryq.trans (he₀ i).1.le)
      (fun l i => hgeometryq.trans (he l (restrict l i)).1.le)
    simpa only [R, Fintype.card_coe] using hmetric
  · intro μ' _ hreg' σ' B' code' hopt'
    obtain ⟨e₁, he₁⟩ := hrecovery Ω μ' d M m A z hreg' hAunit hAstable
      σ' hm B' code' hopt'
    let R := tailRecoverableFeatures (featurePrevalence μ z) σ C m ∩
      tailRecoverableFeatures (featurePrevalence μ' z) σ' C m
    let restrict₀ : R ↪ tailRecoverableFeatures (featurePrevalence μ z) σ C m :=
      { toFun := fun i => ⟨i.1, (Finset.mem_inter.mp i.2).1⟩
        inj' := fun _ _ h => Subtype.ext (congrArg
          (fun j : tailRecoverableFeatures (featurePrevalence μ z) σ C m => j.1) h) }
    let restrict₁ : R ↪ tailRecoverableFeatures (featurePrevalence μ' z) σ' C m :=
      { toFun := fun i => ⟨i.1, (Finset.mem_inter.mp i.2).2⟩
        inj' := fun _ _ h => Subtype.ext (congrArg
          (fun j : tailRecoverableFeatures (featurePrevalence μ' z) σ' C m => j.1) h) }
    have hmetric := testableMatchingMetric_ge_of_common_reference_inner
      (fun _ : Unit => m) B (fun _ => B')
      (fun i : R => representationToEuclidean d (A.col i.1))
      (fun i => hAunit i.1) (restrict₀.trans e₀) (fun _ => restrict₁.trans e₁)
      (fun i => hopt.1.1 (e₀ (restrict₀ i)))
      (fun _ i => hopt'.1.1 (e₁ (restrict₁ i))) ε hε.le
      (fun i => hgeometryq.trans (he₀ (restrict₀ i)).1.le)
      (fun _ i => hgeometryq.trans (he₁ (restrict₁ i)).1.le)
    simpa only [R, Fintype.card_coe] using hmetric

end PKG26AtomicFeatures
