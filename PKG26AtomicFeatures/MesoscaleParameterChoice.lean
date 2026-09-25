import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Primitive parameters for the mesoscale construction

The rare mass can be arbitrarily small while retaining its fixed relative
second-moment contribution. The continuous cube mass and the rare point's
child coefficient can then be chosen strictly positive with arbitrarily
small total objective perturbation. The final common scaling therefore
places the source in the unit cube without changing its feature scores.
-/

namespace PKG26AtomicFeatures

/-- Simultaneously meet the F1 error budget, the reference calibration,
unit-cube scaling requirements, and any prescribed uniform risk tolerance. -/
theorem exists_mesoscale_primitive_parameters (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ δ θ H η : ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < θ ∧ θ < 1 ∧ 1 ≤ H ∧ 0 < η ∧ η ≤ 1 ∧
      δ + θ ≤ ε / 2 ∧ δ * H ^ 2 = (3 / 5) * (1 - δ) ∧
      δ * η * (2 * H + η) + 2 * θ < κ * (1 - δ) := by
  let δ := min (ε / 8) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδquarter : δ ≤ 1 / 4 := min_le_right _ _
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hδone : δ < 1 := by linarith
  have honeδ : 0 < 1 - δ := sub_pos.mpr hδone
  let H := Real.sqrt ((3 / 5) * (1 - δ) / δ)
  have hratio : 0 ≤ (3 / 5 : ℝ) * (1 - δ) / δ := by positivity
  have hHsq : H ^ 2 = (3 / 5) * (1 - δ) / δ := Real.sq_sqrt hratio
  have hcal : δ * H ^ 2 = (3 / 5) * (1 - δ) := by
    rw [hHsq]
    field_simp
  have hH : 1 ≤ H := by
    have hHnonneg : 0 ≤ H := Real.sqrt_nonneg _
    have hratioone : 1 ≤ (3 / 5 : ℝ) * (1 - δ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      linarith
    nlinarith
  have hHpositive : 0 < H := by linarith
  let θ := min (δ / 2) (min (κ * (1 - δ) / 8) (1 / 4))
  have hθ : 0 < θ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hθδ : θ ≤ δ / 2 := min_le_left _ _
  have hθκ : θ ≤ κ * (1 - δ) / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hθquarter : θ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let η := min 1 (κ * (1 - δ) / (8 * δ * (2 * H + 1)))
  have hden : 0 < 8 * δ * (2 * H + 1) := by positivity
  have hη : 0 < η := lt_min (by norm_num) (div_pos (by positivity) hden)
  have hηone : η ≤ 1 := min_le_left _ _
  have hηκ : η ≤ κ * (1 - δ) / (8 * δ * (2 * H + 1)) := min_le_right _ _
  have hηbound : η * (8 * δ * (2 * H + 1)) ≤ κ * (1 - δ) :=
    (le_div_iff₀ hden).mp hηκ
  have herror : δ * η * (2 * H + η) ≤ κ * (1 - δ) / 8 := by
    have hsmall : δ * η * (2 * H + η) ≤ δ * η * (2 * H + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hδ.le hη.le)
    nlinarith
  refine ⟨δ, θ, H, η, hδ, hδone, hθ, by linarith, hH, hη, hηone, by linarith,
    hcal, ?_⟩
  have hbudget : 0 < κ * (1 - δ) := mul_pos hκ (sub_pos.mpr hδone)
  linarith

end PKG26AtomicFeatures
