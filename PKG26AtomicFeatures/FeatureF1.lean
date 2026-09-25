import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Feature presence and population F1

For measurable truth and prediction events, F1 is twice the true-positive
probability divided by the sum of the two positive probabilities. The
positive-prevalence hypothesis below makes the denominator nonzero; no
convention for an unobserved truth feature is used by the recovery bound.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped symmDiff

/-- Population binary F1. Lean's zero-denominator convention assigns zero
when both events have zero mass. All recovery results use positive truth
prevalence and therefore do not depend on that convention. -/
noncomputable def populationF1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (truth prediction : Set Ω) : ℝ :=
  2 * μ.real (truth ∩ prediction) / (μ.real truth + μ.real prediction)

/-- The classification error equals false-negative plus false-positive
probability, or total positive mass minus twice the true-positive mass. -/
theorem classification_error_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {truth prediction : Set Ω} (ht : MeasurableSet truth)
    (hp : MeasurableSet prediction) :
    μ.real (truth ∆ prediction) + 2 * μ.real (truth ∩ prediction) =
      μ.real truth + μ.real prediction := by
  rw [measureReal_symmDiff_eq ht hp]
  have hfirst := measureReal_inter_add_diff (μ := μ) (s := truth) hp
  have hsecond := measureReal_inter_add_diff (μ := μ) (s := prediction) ht
  rw [inter_comm prediction truth] at hsecond
  linarith

/-- An error probability at most `η` times the feature prevalence gives
F1 at least `1-η`. This is the normalization used by the recovery principle. -/
theorem populationF1_ge_of_error_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {truth prediction : Set Ω} (ht : MeasurableSet truth)
    (hp : MeasurableSet prediction) (hprevalence : 0 < μ.real truth)
    {η : ℝ} (hη : 0 ≤ η)
    (herror : μ.real (truth ∆ prediction) ≤ η * μ.real truth) :
    1 - η ≤ populationF1 μ truth prediction := by
  have hdenom : 0 < μ.real truth + μ.real prediction :=
    add_pos_of_pos_of_nonneg hprevalence measureReal_nonneg
  rw [populationF1, le_div_iff₀ hdenom]
  have hidentity := classification_error_identity μ ht hp
  have hnonneg : 0 ≤ η * μ.real prediction := mul_nonneg hη measureReal_nonneg
  nlinarith

/-- Presence events for a source coefficient and a thresholded learned
coefficient. The learned threshold may be chosen strictly positive in the
recovery proof. -/
theorem featureF1_ge_of_error_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (source learned : Ω → ℝ) (hs : Measurable source) (hl : Measurable learned)
    (threshold η : ℝ) (hη : 0 ≤ η)
    (hprevalence : 0 < μ.real {x | 0 < source x})
    (herror : μ.real ({x | 0 < source x} ∆ {x | threshold < learned x}) ≤
      η * μ.real {x | 0 < source x}) :
    1 - η ≤ populationF1 μ {x | 0 < source x} {x | threshold < learned x} := by
  exact populationF1_ge_of_error_le μ
    (measurableSet_lt measurable_const hs) (measurableSet_lt measurable_const hl)
    hprevalence hη herror

end PKG26AtomicFeatures
