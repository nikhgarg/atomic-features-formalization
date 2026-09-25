import PKG26AtomicFeatures.PositivePopulationScaling

/-!
# Scaling the actual optimal reconstruction loss

The positive scaling bijection of the full feasible encoder class commutes
with the infimum over dictionaries and encoders. This includes infeasible
widths and nonattained infima; no optimizer is assumed.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal

theorem optimalRecoveryLoss_le_actual
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m) (γ : ℝ)
    (hu : IsFeasibleRecoveryPair B u γ K) :
    optimalRecoveryLoss μ A z γ K m ≤ actualPopulationSquaredLoss μ A z B u :=
  iInf_le_of_le B (iInf_le_of_le u (iInf_le_of_le hu le_rfl))

theorem optimalRecoveryLoss_positive_scaling {d m K : ℕ}
    (μ : Measure (FeatureVector d)) (γ s : ℝ) (hs : 0 < s) :
    optimalRecoveryLoss (scaledSourceLaw s μ) (1 : Matrix (Fin d) (Fin d) ℝ) id γ K m =
      ENNReal.ofReal (s ^ 2) * optimalRecoveryLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) id γ K m := by
  have hc : ENNReal.ofReal (s ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hs)).ne'
  apply le_antisymm
  · have hmul : ENNReal.ofReal (s ^ 2) *
        optimalRecoveryLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) id γ K m =
        ⨅ (B : Matrix (Fin d) (Fin m) ℝ) (u : FeatureVector d → FeatureVector m)
          (_ : IsFeasibleRecoveryPair B u γ K),
          ENNReal.ofReal (s ^ 2) * actualPopulationSquaredLoss μ 1 id B u := by
      simp only [optimalRecoveryLoss, ENNReal.mul_iInf_of_ne hc ENNReal.ofReal_ne_top]
    rw [hmul]
    refine le_iInf fun B => le_iInf fun u => le_iInf fun hu => ?_
    calc
      _ ≤ actualPopulationSquaredLoss (scaledSourceLaw s μ) 1 id B (scaledFeatureMap s u) :=
        optimalRecoveryLoss_le_actual _ _ _ B _ γ (hu.scaledFeatureMap s hs)
      _ = _ := actualPopulationSquaredLoss_positive_scaling μ B u hu.2.2.1 s hs
  · unfold optimalRecoveryLoss
    refine le_iInf fun B => le_iInf fun v => le_iInf fun hv => ?_
    rw [actualPopulationSquaredLoss_scaledSourceLaw μ B v hv.2.2.1 s hs]
    apply mul_le_mul_right
    exact optimalRecoveryLoss_le_actual μ 1 id B (scaledFeatureMap s⁻¹ v) γ
      (hv.scaledFeatureMap s⁻¹ (inv_pos.mpr hs))

end PKG26AtomicFeatures
