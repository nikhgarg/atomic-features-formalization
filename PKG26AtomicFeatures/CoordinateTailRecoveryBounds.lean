import PKG26AtomicFeatures.ThresholdedFeatureRecovery

/-!
# Recovery probabilities from source-coordinate lower tails

After a matched atom has its positive orientation, comparison with the actual
source coordinate replaces small-ball bounds for arbitrary inverse rows.
The estimates use only a coordinate lower tail and actual squared loss.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal

/-- A wrong-orientation coordinate estimate makes every sufficiently large
source coordinate incur a fixed positive residual. -/
theorem residual_gt_of_negative_orientation_coordinate_bound
    (z r γ a E : ℝ) (hγ : 0 < γ)
    (hcoord : z ≤ r / γ ^ 2 + E) (hE : E ≤ a / 2) (hz : a < z) :
    γ ^ 2 * a / 2 < r := by
  have h : a / 2 < r / γ ^ 2 := by linarith
  have h' := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp h
  nlinarith

/-- A small residual and accurate positive coefficient comparison activate
the learned coordinate above the common threshold `a/2`. -/
theorem activation_of_positive_coordinate_comparison
    (z u r γ a : ℝ) (hγ : 0 < γ)
    (hcomparison : |u - z| ≤ r / γ + a / 4)
    (hz : a < z) (hr : r ≤ γ * a / 4) : a / 2 < u := by
  have hr' : r / γ ≤ a / 4 := (div_le_iff₀ hγ).mpr (by nlinarith)
  have hneg := (neg_le_abs (u - z)).trans hcomparison
  linarith

/-- Activation outside the selected learned support forces a large actual
residual when the projection error is below the threshold margin. -/
theorem residual_gt_of_outside_coordinate_bound
    (u r projection γ a : ℝ) (hγ : 0 < γ)
    (hcomparison : u ≤ (r + projection) / γ)
    (hprojection : projection ≤ γ * a / 4) (hactive : a / 2 < u) :
    γ * a / 4 < r := by
  have h := (lt_div_iff₀ hγ).mp (hactive.trans_le hcomparison)
  nlinarith

/-- Wrong orientation bounds the probability of small residuals by the
source-coordinate lower tail. All pointwise estimates may hold almost surely. -/
theorem small_residual_probability_le_of_negative_orientation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (z residual : Ω → ℝ) (γ a E ε : ℝ) (hγ : 0 < γ)
    (hE : E ≤ a / 2)
    (hcoord : ∀ᵐ x ∂μ, z x ≤ residual x / γ ^ 2 + E)
    (htail : μ.real {x | z x ≤ a} ≤ ε) :
    μ.real {x | residual x ≤ γ ^ 2 * a / 2} ≤ ε := by
  have hsubset : {x | residual x ≤ γ ^ 2 * a / 2} ≤ᵐ[μ] {x | z x ≤ a} := by
    filter_upwards [hcoord] with x hx
    intro hr
    by_contra hn
    exact (not_lt_of_ge hr)
      (residual_gt_of_negative_orientation_coordinate_bound _ _ γ a E hγ hx hE
        (lt_of_not_ge hn))
  exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsubset)).trans htail

/-- Positive coefficient comparison controls false negatives using only
the actual source-coordinate lower tail and a squared-loss Markov bound. -/
theorem coordinate_threshold_false_negative_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (z learned residual : Ω → ℝ) (hresidual : Measurable residual)
    (γ a ε L : ℝ) (hγ : 0 < γ) (ha : 0 < a) (hL : 0 ≤ L)
    (hcomparison : ∀ᵐ x ∂μ, |learned x - z x| ≤ residual x / γ + a / 4)
    (htail : μ.real {x | z x ≤ a} ≤ ε)
    (hloss : (∫⁻ x, ENNReal.ofReal (residual x ^ 2) ∂μ) ≤ ENNReal.ofReal L) :
    μ.real {x | learned x ≤ a / 2} ≤ L / (γ * a / 4) ^ 2 + ε := by
  have hsubset : ∀ᵐ x ∂μ, learned x ≤ a / 2 →
      γ * a / 4 < residual x ∨ z x ≤ a := by
    filter_upwards [hcomparison] with x hx
    intro hu
    by_cases hr : γ * a / 4 < residual x
    · exact Or.inl hr
    · right
      by_contra hz
      exact (not_lt_of_ge hu) (activation_of_positive_coordinate_comparison
        _ _ _ γ a hγ hx (lt_of_not_ge hz) (le_of_not_gt hr))
  have hmeasure : μ.real {x | learned x ≤ a / 2} ≤
      μ.real ({x | γ * a / 4 < residual x} ∪ {x | z x ≤ a}) :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsubset)
  exact hmeasure.trans ((measureReal_union_le _ _).trans (add_le_add
    (measureReal_residual_tail_le_of_squared_loss μ residual hresidual
      (γ * a / 4) L (by positivity) hL hloss) htail))

/-- A coordinate excluded from the projected code has false-positive mass
controlled solely by actual squared reconstruction loss. -/
theorem coordinate_threshold_false_positive_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (learned residual : Ω → ℝ) (hresidual : Measurable residual)
    (γ a projection L : ℝ) (hγ : 0 < γ) (ha : 0 < a) (hL : 0 ≤ L)
    (hcomparison : ∀ᵐ x ∂μ, learned x ≤ (residual x + projection) / γ)
    (hprojection : projection ≤ γ * a / 4)
    (hloss : (∫⁻ x, ENNReal.ofReal (residual x ^ 2) ∂μ) ≤ ENNReal.ofReal L) :
    μ.real {x | a / 2 < learned x} ≤ L / (γ * a / 4) ^ 2 := by
  have hsubset : {x | a / 2 < learned x} ≤ᵐ[μ] {x | γ * a / 4 < residual x} := by
    filter_upwards [hcomparison] with x hx
    exact residual_gt_of_outside_coordinate_bound _ _ projection γ a hγ hx hprojection
  exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsubset)).trans
    (measureReal_residual_tail_le_of_squared_loss μ residual hresidual
      (γ * a / 4) L (by positivity) hL hloss)

end PKG26AtomicFeatures
