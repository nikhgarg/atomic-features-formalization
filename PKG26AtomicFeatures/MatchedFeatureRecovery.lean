import PKG26AtomicFeatures.MixtureRecoveryBounds

/-!
# Recovering one consistently matched feature

On a positive-weight source support, the truth event has probability zero
or one according to support membership. A single learned coordinate whose
membership agrees on every good support therefore uses the false-positive
bound outside the support and the false-negative bound inside it. This
derives the conditional classification-error estimate without adding its
two alternatives, and preserves the coefficient of the conditional loss.
The mixture bound then gives population F1 for that same coordinate.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators symmDiff

/-- When truth has probability zero, classification error is precisely
the prediction probability. -/
theorem classification_error_eq_prediction_of_truth_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (truth prediction : Set Ω) (ht : MeasurableSet truth)
    (hp : MeasurableSet prediction) (hzero : μ.real truth = 0) :
    μ.real (truth ∆ prediction) = μ.real prediction := by
  rw [measureReal_symmDiff_eq ht hp,
    measureReal_mono_null Set.diff_subset hzero, measureReal_diff_null hzero, zero_add]

/-- When truth has probability one, classification error is precisely
the probability of an inactive prediction. -/
theorem classification_error_eq_compl_prediction_of_truth_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (truth prediction : Set Ω) (ht : MeasurableSet truth)
    (hp : MeasurableSet prediction) (hone : μ.real truth = 1) :
    μ.real (truth ∆ prediction) = μ.real predictionᶜ := by
  have hzero : μ.real truthᶜ = 0 := by
    rw [probReal_compl_eq_one_sub ht, hone, sub_self]
  have hfirst : truth \ prediction = predictionᶜ \ truthᶜ := by
    ext ω
    simp only [Set.mem_diff, Set.mem_compl_iff]
    tauto
  have hsecond : prediction \ truth ⊆ truthᶜ := by
    intro ω hω
    exact hω.2
  rw [measureReal_symmDiff_eq ht hp, hfirst, measureReal_diff_null hzero,
    measureReal_mono_null hsecond hzero, add_zero]

/-- Deterministic conditional truth chooses one of the two activation
error bounds. Their common loss coefficient is used only once. -/
theorem classification_error_le_of_activation_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (truth : Set Ω) (ht : MeasurableSet truth)
    (learned : Ω → ℝ) (hl : Measurable learned) (t ε q : ℝ)
    (present : Prop) [Decidable present]
    (htruth : μ.real truth = if present then 1 else 0)
    (houtside : ¬ present → μ.real {ω | t < learned ω} ≤ q)
    (hinside : present → μ.real {ω | learned ω ≤ t} ≤ q + ε) :
    μ.real (truth ∆ {ω | t < learned ω}) ≤
      ε * (if present then 1 else 0) + q := by
  have hp : MeasurableSet {ω | t < learned ω} := measurableSet_lt measurable_const hl
  by_cases hpresent : present
  · have hone : μ.real truth = 1 := by simpa only [if_pos hpresent] using htruth
    rw [classification_error_eq_compl_prediction_of_truth_one μ truth _ ht hp hone]
    have hcomp : {ω | t < learned ω}ᶜ = {ω | learned ω ≤ t} := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    rw [hcomp, if_pos hpresent, mul_one]
    simpa only [add_comm] using hinside hpresent
  · have hzero : μ.real truth = 0 := by simpa only [if_neg hpresent] using htruth
    rw [classification_error_eq_prediction_of_truth_zero μ truth _ ht hp hzero,
      if_neg hpresent, mul_zero, zero_add]
    exact houtside hpresent

/-- A matched source and learned coordinate inherit a conditional
classification-error estimate on every good support. The learned supports
need only be defined on the actual good family. -/
theorem matched_good_support_classification_error_le
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M m : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ : ℝ)
    (ν : ι → Measure Ω) [∀ s, IsProbabilityMeasure (ν s)]
    (T : {s // s ∈ goodSupportIndices w loss τ} → Finset (Fin m))
    (i : Fin M) (j : Fin m) (truth : Set Ω) (ht : MeasurableSet truth)
    (code : Ω → FeatureVector m) (hcode : Measurable code) (t ε A : ℝ)
    (htruth : ∀ s, 0 < w s → (ν s).real truth = if i ∈ S s then 1 else 0)
    (hmatch : ∀ s, i ∈ S s.1 ↔ j ∈ T s)
    (houtside : ∀ s, j ∉ T s → (ν s.1).real {ω | t < code ω j} ≤ A * loss s.1)
    (hinside : ∀ s, j ∈ T s → (ν s.1).real {ω | code ω j ≤ t} ≤ A * loss s.1 + ε) :
    ∀ s ∈ goodSupportIndices w loss τ,
      (ν s).real (truth ∆ {ω | t < code ω j}) ≤
        ε * (if i ∈ S s then 1 else 0) + A * loss s := by
  classical
  intro s hs
  let good : {s // s ∈ goodSupportIndices w loss τ} := ⟨s, hs⟩
  have hpositive : 0 < w s := ((mem_goodSupportIndices w loss τ s).mp hs).1
  apply classification_error_le_of_activation_bounds (ν s) truth ht
    (fun ω => code ω j) ((measurable_pi_apply j).comp hcode) t ε (A * loss s)
    (i ∈ S s) (htruth s hpositive)
  · intro hnot
    exact houtside good (fun hj => hnot ((hmatch good).mpr hj))
  · intro hi
    exact hinside good ((hmatch good).mp hi)

/-- One matched learned coordinate has the required population F1. The
threshold may be any real number; in the recovery application it is positive.
Conditional activation bounds are required only on positive-weight good
supports, while truth probabilities are required only on positive weights. -/
theorem matched_feature_populationF1_ge
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {M m : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (ν : ι → Measure Ω)
    [∀ s, IsProbabilityMeasure (ν s)]
    (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1)
    (hloss : ∀ s, 0 ≤ loss s) (τ ε A η : ℝ)
    (hτ : 0 < τ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hη : 0 < η)
    (hεsmall : ε ≤ η / 2)
    (T : {s // s ∈ goodSupportIndices w loss τ} → Finset (Fin m))
    (i : Fin M) (j : Fin m) (truth : Set Ω) (ht : MeasurableSet truth)
    (code : Ω → FeatureVector m) (hcode : Measurable code) (t : ℝ)
    (htruth : ∀ s, 0 < w s → (ν s).real truth = if i ∈ S s then 1 else 0)
    (hmatch : ∀ s, i ∈ S s.1 ↔ j ∈ T s)
    (houtside : ∀ s, j ∉ T s → (ν s.1).real {ω | t < code ω j} ≤ A * loss s.1)
    (hinside : ∀ s, j ∈ T s → (ν s.1).real {ω | code ω j ≤ t} ≤ A * loss s.1 + ε)
    (hprevalence : 0 < supportMarginalWeight S w i)
    (hbudget : 2 * (A + 1 / τ) * weightedConditionalLoss w loss / η ≤
      supportMarginalWeight S w i) :
    1 - η ≤ populationF1 (finiteSupportMixture w ν) truth {ω | t < code ω j} := by
  apply finiteSupportMixture_populationF1_ge S w loss ν hw hsum hloss τ ε A η
    hτ hε hA hη hεsmall i truth {ω | t < code ω j} ht
    (measurableSet_lt measurable_const ((measurable_pi_apply j).comp hcode)) htruth
    (matched_good_support_classification_error_le S w loss τ ν T i j truth ht
      code hcode t ε A htruth hmatch houtside hinside) hprevalence hbudget

end PKG26AtomicFeatures
