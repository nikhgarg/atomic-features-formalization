import PKG26AtomicFeatures.WeightedGoodSupports
import PKG26AtomicFeatures.FeatureF1
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Aggregating conditional feature errors

A finite probability mixture transports conditional error bounds to the
population law. Positive-weight components with small conditional loss use
their local recovery bound; the remaining components contribute at most their
weight. The latter weight is controlled by the actual weighted loss. Components
of weight zero impose no conditional truth or recovery requirements.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff

/-- The population law formed from a finite family of conditional laws. -/
noncomputable def finiteSupportMixture {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (w : ι → ℝ) (ν : ι → Measure Ω) : Measure Ω :=
  ∑ s, ENNReal.ofReal (w s) • ν s

/-- Nonnegative normalized weights and probability components give a
probability mixture, including when some weights vanish. -/
theorem finiteSupportMixture_isProbabilityMeasure
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (ν : ι → Measure Ω) [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1) :
    IsProbabilityMeasure (finiteSupportMixture w ν) := by
  constructor
  simp only [finiteSupportMixture, Measure.finset_sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hw s), hsum]
  simp

/-- Real event probabilities are the actual weighted conditional
probabilities. The equality holds for arbitrary events. -/
theorem finiteSupportMixture_real_apply
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (ν : ι → Measure Ω) [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (E : Set Ω) :
    (finiteSupportMixture w ν).real E = ∑ s, w s * (ν s).real E := by
  classical
  simp only [Measure.real, finiteSupportMixture, Measure.finset_sum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun s _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top (ν s) E))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw _)]

/-- A marginal support weight is its full-family indicator sum. -/
theorem supportMarginalWeight_eq_sum_indicator
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (i : Fin M) :
    supportMarginalWeight S w i = ∑ s, w s * (if i ∈ S s then 1 else 0) := by
  classical
  simp [supportMarginalWeight, supportFamilyWeight, Finset.sum_filter]

/-- Conditional recovery on the good components, together with the finite
weighted Markov bound, controls population classification error. -/
theorem finiteSupportMixture_error_le
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (ν : ι → Measure Ω)
    [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (τ ε A : ℝ) (hτ : 0 < τ) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (i : Fin M) (E : Set Ω)
    (hconditional : ∀ s ∈ goodSupportIndices w loss τ,
      (ν s).real E ≤ ε * (if i ∈ S s then 1 else 0) + A * loss s) :
    (finiteSupportMixture w ν).real E ≤
      ε * supportMarginalWeight S w i + A * weightedConditionalLoss w loss +
        weightedConditionalLoss w loss / τ := by
  classical
  have hpoint (s : ι) : w s * (ν s).real E ≤
      ε * (w s * (if i ∈ S s then 1 else 0)) + A * (w s * loss s) +
        (if s ∈ goodSupportIndices w loss τ then 0 else w s) := by
    by_cases hs : s ∈ goodSupportIndices w loss τ
    · have h := mul_le_mul_of_nonneg_left (hconditional s hs) (hw s)
      simp only [hs, if_true, add_zero]
      nlinarith
    · have hprob : (ν s).real E ≤ 1 := by
        simpa using (measureReal_mono (Set.subset_univ E) :
          (ν s).real E ≤ (ν s).real Set.univ)
      have hmass := mul_le_mul_of_nonneg_left hprob (hw s)
      have hfirst : 0 ≤ ε * (w s * (if i ∈ S s then 1 else 0)) :=
        mul_nonneg hε (mul_nonneg (hw s) (by split_ifs <;> norm_num))
      have hsecond : 0 ≤ A * (w s * loss s) :=
        mul_nonneg hA (mul_nonneg (hw s) (hloss s))
      simp only [hs, if_false]
      nlinarith
  have hbad : (∑ s, if s ∈ goodSupportIndices w loss τ then 0 else w s) =
      badSupportWeight w loss τ := by
    rw [badSupportWeight, supportFamilyWeight, Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hpoint s)
  rw [← finiteSupportMixture_real_apply w ν hw E] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hbad,
    ← supportMarginalWeight_eq_sum_indicator] at hsum
  exact hsum.trans (add_le_add le_rfl
    (badSupportWeight_le_loss_div_threshold w loss τ hw hloss hτ))

/-- Conditional truth is required only on positive-weight components. This
identifies population prevalence with the source-support marginal. -/
theorem finiteSupportMixture_truth_eq_marginal
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (ν : ι → Measure Ω)
    [∀ s, IsProbabilityMeasure (ν s)] (hw : ∀ s, 0 ≤ w s)
    (i : Fin M) (truth : Set Ω)
    (htruth : ∀ s, 0 < w s → (ν s).real truth = if i ∈ S s then 1 else 0) :
    (finiteSupportMixture w ν).real truth = supportMarginalWeight S w i := by
  classical
  rw [finiteSupportMixture_real_apply w ν hw truth,
    supportMarginalWeight_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : w s = 0
  · simp [hs]
  · rw [htruth s (lt_of_le_of_ne (hw s) (Ne.symm hs))]

/-- The conditional classification estimate yields population F1 once the
feature prevalence dominates the total-loss budget. Positive prevalence is
explicit even when the loss vanishes. -/
theorem finiteSupportMixture_populationF1_ge
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (ν : ι → Measure Ω)
    [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1)
    (hloss : ∀ s, 0 ≤ loss s) (τ ε A η : ℝ)
    (hτ : 0 < τ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hη : 0 < η)
    (hεsmall : ε ≤ η / 2) (i : Fin M) (truth prediction : Set Ω)
    (ht : MeasurableSet truth) (hp : MeasurableSet prediction)
    (htruth : ∀ s, 0 < w s → (ν s).real truth = if i ∈ S s then 1 else 0)
    (hconditional : ∀ s ∈ goodSupportIndices w loss τ,
      (ν s).real (truth ∆ prediction) ≤
        ε * (if i ∈ S s then 1 else 0) + A * loss s)
    (hprevalence : 0 < supportMarginalWeight S w i)
    (hbudget : 2 * (A + 1 / τ) * weightedConditionalLoss w loss / η ≤
      supportMarginalWeight S w i) :
    1 - η ≤ populationF1 (finiteSupportMixture w ν) truth prediction := by
  letI := finiteSupportMixture_isProbabilityMeasure w ν hw hsum
  have htruthmix := finiteSupportMixture_truth_eq_marginal S w ν hw i truth htruth
  apply populationF1_ge_of_error_le (finiteSupportMixture w ν) ht hp
    (by rwa [htruthmix]) hη.le
  rw [htruthmix]
  have herror := finiteSupportMixture_error_le S w loss ν hw hloss
    τ ε A hτ hε hA i (truth ∆ prediction) hconditional
  have hεterm := mul_le_mul_of_nonneg_right hεsmall hprevalence.le
  have hlossterm := (div_le_iff₀ hη).mp hbudget
  have hrewrite : A * weightedConditionalLoss w loss +
      weightedConditionalLoss w loss / τ =
      (A + 1 / τ) * weightedConditionalLoss w loss := by ring
  rw [add_assoc, hrewrite] at herror
  nlinarith

/-- Nonnegative integration commutes exactly with the finite mixture.
Measurability or finiteness is not needed for this identity. -/
theorem lintegral_finiteSupportMixture
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (ν : ι → Measure Ω) (f : Ω → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂finiteSupportMixture w ν =
      ∑ s, ENNReal.ofReal (w s) * ∫⁻ ω, f ω ∂ν s := by
  simp only [finiteSupportMixture, lintegral_finset_sum_measure,
    lintegral_smul_measure, smul_eq_mul]

/-- Finite population loss forces finite conditional loss on every
positive-weight component. Zero-weight components remain unrestricted. -/
theorem conditional_lintegral_ne_top_of_finite_mixture
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (ν : ι → Measure Ω) (f : Ω → ℝ≥0∞)
    (hfinite : (∫⁻ ω, f ω ∂finiteSupportMixture w ν) ≠ ∞)
    (s : ι) (hs : 0 < w s) : (∫⁻ ω, f ω ∂ν s) ≠ ∞ := by
  have hterm : ENNReal.ofReal (w s) * (∫⁻ ω, f ω ∂ν s) ≤
      ∫⁻ ω, f ω ∂finiteSupportMixture w ν := by
    rw [lintegral_finiteSupportMixture]
    exact Finset.single_le_sum
      (f := fun j => ENNReal.ofReal (w j) * ∫⁻ ω, f ω ∂ν j)
      (fun _ _ => zero_le _) (Finset.mem_univ s)
  have htermfinite := ne_top_of_le_ne_top hfinite hterm
  intro htop
  exact htermfinite (ENNReal.mul_eq_top.mpr
    (Or.inl ⟨(ENNReal.ofReal_pos.mpr hs).ne', htop⟩))

/-- Converting conditional losses to real numbers preserves the total loss
when all positive-weight conditional integrals are finite. An infinite
integral on a zero-weight component contributes zero on both sides. -/
theorem lintegral_finiteSupportMixture_eq_weightedConditionalLoss
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (ν : ι → Measure Ω) (f : Ω → ℝ≥0∞)
    (hw : ∀ s, 0 ≤ w s)
    (hfinite : ∀ s, 0 < w s → (∫⁻ ω, f ω ∂ν s) ≠ ∞) :
    (∫⁻ ω, f ω ∂finiteSupportMixture w ν) =
      ENNReal.ofReal (weightedConditionalLoss w
        (fun s => (∫⁻ ω, f ω ∂ν s).toReal)) := by
  rw [lintegral_finiteSupportMixture, weightedConditionalLoss,
    ENNReal.ofReal_sum_of_nonneg
      (fun s _ => mul_nonneg (hw s) ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : w s = 0
  · simp [hs]
  · rw [ENNReal.ofReal_mul (hw s),
      ENNReal.ofReal_toReal (hfinite s (lt_of_le_of_ne (hw s) (Ne.symm hs)))]

/-- A finite bound on the actual population loss supplies both honest
conditional real losses and their weighted bound. The loss integrand may be
the squared residual of a separately measurable stochastic code. -/
theorem weightedConditionalLoss_le_of_lintegral_mixture_le
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (ν : ι → Measure Ω) (f : Ω → ℝ≥0∞)
    (hw : ∀ s, 0 ≤ w s) (L : ℝ) (hL : 0 ≤ L)
    (hbound : (∫⁻ ω, f ω ∂finiteSupportMixture w ν) ≤ ENNReal.ofReal L) :
    (∀ s, 0 < w s → (∫⁻ ω, f ω ∂ν s) ≠ ∞) ∧
      weightedConditionalLoss w (fun s => (∫⁻ ω, f ω ∂ν s).toReal) ≤ L := by
  have hfinite := conditional_lintegral_ne_top_of_finite_mixture w ν f
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨hfinite, ?_⟩
  rw [lintegral_finiteSupportMixture_eq_weightedConditionalLoss w ν f hw hfinite]
    at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hL).mp hbound

end PKG26AtomicFeatures
