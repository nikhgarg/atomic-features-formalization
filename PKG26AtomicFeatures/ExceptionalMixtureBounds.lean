import PKG26AtomicFeatures.ExceptionalCompanionWeights
import PKG26AtomicFeatures.MatchedFeatureRecovery
import PKG26AtomicFeatures.ThresholdedFeatureRecovery

/-!
# Population errors after discarding exceptional companions

Conditional estimates outside an excluded family lose at most that family's
weight. Reverse support separation bounds the weight of bad supports and
exceptional companions together, independently of the dictionary width.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff

/-- A conditional event estimate transports through a finite mixture after
charging the full weight of an arbitrary excluded family exactly once. -/
theorem finiteSupportMixture_error_le_of_excludedFamily
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (ν : ι → Measure Ω)
    [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (Q : Finset ι) (ε A : ℝ) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (i : Fin M) (E : Set Ω)
    (hconditional : ∀ s, s ∉ Q →
      (ν s).real E ≤ ε * (if i ∈ S s then 1 else 0) + A * loss s) :
    (finiteSupportMixture w ν).real E ≤
      ε * supportMarginalWeight S w i + A * weightedConditionalLoss w loss +
        supportFamilyWeight w Q := by
  classical
  have hpoint (s : ι) : w s * (ν s).real E ≤
      ε * (w s * (if i ∈ S s then 1 else 0)) + A * (w s * loss s) +
        (if s ∈ Q then w s else 0) := by
    by_cases hs : s ∈ Q
    · have hprob : (ν s).real E ≤ 1 := by
        simpa using (measureReal_mono (Set.subset_univ E) :
          (ν s).real E ≤ (ν s).real Set.univ)
      have hmass := mul_le_mul_of_nonneg_left hprob (hw s)
      have hfirst : 0 ≤ ε * (w s * (if i ∈ S s then 1 else 0)) :=
        mul_nonneg hε (mul_nonneg (hw s) (by split_ifs <;> norm_num))
      have hsecond : 0 ≤ A * (w s * loss s) :=
        mul_nonneg hA (mul_nonneg (hw s) (hloss s))
      simp only [hs, if_true]
      nlinarith
    · have h := mul_le_mul_of_nonneg_left (hconditional s hs) (hw s)
      simp only [hs, if_false, add_zero]
      nlinarith
  have hexcluded : (∑ s, if s ∈ Q then w s else 0) = supportFamilyWeight w Q := by
    have hQ : Finset.univ.filter (fun s => s ∈ Q) = Q := by ext s; simp
    simp only [← Finset.sum_filter, hQ, supportFamilyWeight]
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hpoint s)
  rw [← finiteSupportMixture_real_apply w ν hw E] at hsum
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hexcluded,
    ← supportMarginalWeight_eq_sum_indicator, weightedConditionalLoss] using hsum

/-- Reverse separation charges every exceptional support to the actual
weighted loss. Local event estimates are needed only on the remaining good
supports and may depend on the selected target feature. -/
theorem finiteSupportMixture_error_le_of_exceptional_supports
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (ν : ι → Measure Ω)
    [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hcard : ∀ s, (S s).card ≤ K)
    (τ ρ ε A : ℝ) (hτ : 0 < τ) (hρ : 0 < ρ) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (i : Fin M) (E : Set Ω)
    (hsep : ∀ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i)
    (hconditional : ∀ s, s ∉ exceptionalSupportIndices S (goodSupportIndices w loss τ) i →
      (ν s).real E ≤ ε * (if i ∈ S s then 1 else 0) + A * loss s) :
    (finiteSupportMixture w ν).real E ≤
      ε * supportMarginalWeight S w i +
        (A + (1 + (K : ℝ) / ρ) / τ) * weightedConditionalLoss w loss := by
  have h := finiteSupportMixture_error_le_of_excludedFamily S w loss ν hw hloss
    (exceptionalSupportIndices S (goodSupportIndices w loss τ) i) ε A hε hA i E hconditional
  have hweight := exceptionalSupportWeight_goodSupport_le_loss S w loss τ ρ i
    hw hloss hcard hτ hρ hsep
  calc
    _ ≤ ε * supportMarginalWeight S w i + A * weightedConditionalLoss w loss +
        (1 + (K : ℝ) / ρ) * (weightedConditionalLoss w loss / τ) :=
      h.trans (add_le_add le_rfl hweight)
    _ = _ := by ring

/-- If small residuals almost never coexist with a present feature outside
the exceptional supports, its prevalence is controlled by the loss. This is
the population contradiction used to exclude a negative atom orientation. -/
theorem finiteSupportMixture_prevalence_bound_of_small_residuals
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (ν : ι → Measure Ω)
    [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1) (hloss : ∀ s, 0 ≤ loss s)
    (hcard : ∀ s, (S s).card ≤ K)
    (τ ρ ε r L : ℝ) (hτ : 0 < τ) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hr : 0 < r) (hL : 0 ≤ L)
    (i : Fin M) (truth : Set Ω) (residual : Ω → ℝ) (hresidual : Measurable residual)
    (htruth : ∀ s, 0 < w s → (ν s).real truth = if i ∈ S s then 1 else 0)
    (hsep : ∀ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i)
    (hconditional : ∀ s, s ∉ exceptionalSupportIndices S (goodSupportIndices w loss τ) i →
      (ν s).real (truth \ {x | r < residual x}) ≤ ε * (if i ∈ S s then 1 else 0))
    (hbound : (∫⁻ x, ENNReal.ofReal (residual x ^ 2) ∂finiteSupportMixture w ν) ≤
      ENNReal.ofReal L) :
    (1 - ε) * supportMarginalWeight S w i ≤
      ((1 + (K : ℝ) / ρ) / τ) * weightedConditionalLoss w loss + L / r ^ 2 := by
  letI := finiteSupportMixture_isProbabilityMeasure w ν hw hsum
  have hsmall := finiteSupportMixture_error_le_of_exceptional_supports
    S w loss ν hw hloss hcard τ ρ ε 0 hτ hρ hε le_rfl i
    (truth \ {x | r < residual x}) hsep (by simpa only [zero_mul, add_zero] using hconditional)
  simp only [zero_add] at hsmall
  have htail := measureReal_residual_tail_le_of_squared_loss
    (finiteSupportMixture w ν) residual hresidual r L hr hL hbound
  have hsubset : truth ⊆ (truth \ {x | r < residual x}) ∪ {x | r < residual x} := by
    intro x hx
    by_cases ht : r < residual x
    · exact Or.inr ht
    · exact Or.inl ⟨hx, ht⟩
  have hmass : (finiteSupportMixture w ν).real truth ≤
      (finiteSupportMixture w ν).real (truth \ {x | r < residual x}) +
        (finiteSupportMixture w ν).real {x | r < residual x} :=
    (measureReal_mono hsubset).trans (measureReal_union_le _ _)
  rw [finiteSupportMixture_truth_eq_marginal S w ν hw i truth htruth] at hmass
  nlinarith

/-- The same exceptional-support estimate gives population F1 for any
fixed matched coordinate once the actual weighted loss is small relative
to its prevalence. -/
theorem finiteSupportMixture_populationF1_ge_of_exceptional_supports
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (ν : ι → Measure Ω)
    [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1) (hloss : ∀ s, 0 ≤ loss s)
    (hcard : ∀ s, (S s).card ≤ K)
    (τ ρ ε A η : ℝ) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (hη : 0 ≤ η) (hεsmall : ε ≤ η / 2)
    (i : Fin M) (truth prediction : Set Ω) (ht : MeasurableSet truth) (hp : MeasurableSet prediction)
    (htruth : ∀ s, 0 < w s → (ν s).real truth = if i ∈ S s then 1 else 0)
    (hsep : ∀ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i)
    (hconditional : ∀ s, s ∉ exceptionalSupportIndices S (goodSupportIndices w loss τ) i →
      (ν s).real (truth ∆ prediction) ≤ ε * (if i ∈ S s then 1 else 0) + A * loss s)
    (hprevalence : 0 < supportMarginalWeight S w i)
    (hbudget : (A + (1 + (K : ℝ) / ρ) / τ) * weightedConditionalLoss w loss ≤
      η / 2 * supportMarginalWeight S w i) :
    1 - η ≤ populationF1 (finiteSupportMixture w ν) truth prediction := by
  letI := finiteSupportMixture_isProbabilityMeasure w ν hw hsum
  have htruthmix := finiteSupportMixture_truth_eq_marginal S w ν hw i truth htruth
  apply populationF1_ge_of_error_le (finiteSupportMixture w ν) ht hp
    (by rwa [htruthmix]) hη
  rw [htruthmix]
  have herror := finiteSupportMixture_error_le_of_exceptional_supports
    S w loss ν hw hloss hcard τ ρ ε A hτ hρ hε hA i (truth ∆ prediction) hsep hconditional
  have heps := mul_le_mul_of_nonneg_right hεsmall hprevalence.le
  linarith

end PKG26AtomicFeatures
