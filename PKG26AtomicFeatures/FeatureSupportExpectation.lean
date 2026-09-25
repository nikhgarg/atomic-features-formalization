import PKG26AtomicFeatures.RegularPopulationModel

/-! # Expected activation count of a learned feature map -/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal

/-- The actual expected number of active learned coordinates. The
nonnegative integral retains infinite values for arbitrary input measures. -/
noncomputable def expectedCodeSupportSize
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (u : Ω → FeatureVector m) : ℝ≥0∞ :=
  ∫⁻ x, ((nonzeroSupport (u x)).card : ℝ≥0∞) ∂μ


end PKG26AtomicFeatures
