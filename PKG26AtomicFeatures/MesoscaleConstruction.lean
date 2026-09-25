import PKG26AtomicFeatures.MesoscaleParameterChoice
import PKG26AtomicFeatures.MesoscaleWidthOneRecovery
import PKG26AtomicFeatures.MesoscaleWidthThreeRecovery
import PKG26AtomicFeatures.MesoscaleWidthTwoRecovery
import PKG26AtomicFeatures.MesoscaleLossOrdering

/-!
# One explicit mesoscale population for all three learned widths

The construction chooses one positive rare mass, cube mass, parent scale,
and child perturbation. Its actual population simultaneously has attained
optima, the width-dependent feature-recovery table, and strictly decreasing
optimal reconstruction loss. All optimization and feature scores use the
actual population measure and feasible dictionary/encoder pairs.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal

/-- An actual exact optimal pair attains the actual infimum, including
extended nonnegative losses. This identifies numerical optimal-loss endpoints
with the loss of any exhibited global optimum. -/
theorem IsApproximatelyOptimalRecoveryPair.loss_eq_optimalRecoveryLoss
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    {μ : Measure Ω} {A : Matrix (Fin d) (Fin M) ℝ} {z : Ω → FeatureVector M}
    {B : Matrix (Fin d) (Fin m) ℝ} {u : Ω → FeatureVector m} {γ : ℝ}
    (hopt : IsApproximatelyOptimalRecoveryPair μ A z B u γ 1 K) :
    actualPopulationSquaredLoss μ A z B u = optimalRecoveryLoss μ A z γ K m := by
  have hle := ((isApproximatelyOptimalRecoveryPair_iff_loss_le_infimum μ A z B u γ 1
    (by norm_num)).mp hopt).2
  simp only [ENNReal.ofReal_one, one_mul] at hle
  apply le_antisymm hle
  unfold optimalRecoveryLoss
  exact iInf_le_of_le B (iInf_le_of_le u (iInf_le_of_le hopt.1 le_rfl))

/-- Width-one attainment uses the explicit positive leading dictionary
and the actual clipped encoder, rather than an assumed optimizer. -/
theorem exists_mesoscale_width_one_optimal_pair
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η) :
    ∃ (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1),
      IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 := by
  let B := oneColumnDictionary
    (symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment δ θ H η)
      (mesoscaleParentChildMoment δ θ H η) (mesoscaleChildSecondMoment δ θ H η))
  exact ⟨B, oneColumnClippedFeatureMap B,
    mesoscale_leading_width_one_pair_optimal δ θ H η hδ hδone hθ hθone hH hη⟩

/-- Width-three attainment uses the actual globally feasible sanitized
identity encoder on the entire ambient source space. -/
theorem exists_mesoscale_width_three_optimal_pair
    (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∃ (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3),
      IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 :=
  ⟨1, nonnegativeSparseIdentityEncoder 3 2,
    mesoscalePopulationLaw_sanitized_identity_isOptimal δ θ H η hH hη⟩

/-- The actual width-three optimal value is zero, established by an
explicit feasible zero-loss pair. -/
theorem mesoscale_optimalRecoveryLoss_width_three_eq_zero
    (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    optimalRecoveryLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 = 0 := by
  rw [← (mesoscalePopulationLaw_sanitized_identity_isOptimal δ θ H η hH hη).loss_eq_optimalRecoveryLoss]
  exact mesoscalePopulationLaw_sanitized_identity_zero_loss δ θ H η hH hη

/-- One primitive parameter choice satisfies the feature tolerance, the
uniform reference-neighborhood tolerance, and the strict loss-gap tolerance. -/
theorem exists_mesoscale_common_parameters (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ δ θ H η : ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < θ ∧ θ < 1 ∧ 1 ≤ H ∧ 0 < η ∧ η ≤ 1 ∧
      δ + θ ≤ ε / 2 ∧ δ * H ^ 2 = (3 / 5) * (1 - δ) ∧
      δ * η * (2 * H + η) + 2 * θ < κ * (1 - δ) ∧
      δ * η * (2 * H + η) + 2 * θ < (1 - δ) / 10 := by
  obtain ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, hεsmall, hcal, herr⟩ :=
    exists_mesoscale_primitive_parameters ε (min κ (1 / 10)) hε
      (lt_min hκ (by norm_num))
  have hgap : 0 ≤ 1 - δ := (sub_pos.mpr hδone).le
  refine ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, hεsmall, hcal,
    herr.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hgap), ?_⟩
  have h := herr.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hgap)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

/-- For every positive feature tolerance, one explicit unscaled mesoscale
population has attained optima at all three widths, the every-optimum feature
table, and strictly decreasing actual optimal loss ending at zero. The same
parameter tuple satisfies all conclusions simultaneously. -/
theorem exists_mesoscale_unscaled_construction (ε : ℝ) (hε : 0 < ε) :
    ∃ δ θ H η : ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < θ ∧ θ < 1 ∧ 1 ≤ H ∧ 0 < η ∧ η ≤ 1 ∧
      δ + θ ≤ ε / 2 ∧ δ * H ^ 2 = (3 / 5) * (1 - δ) ∧
      IsProbabilityMeasure (mesoscalePopulationLaw δ θ H η) ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        ∃ (B : Matrix (Fin 3) (Fin m) ℝ) (u : FeatureVector 3 → FeatureVector m),
          IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
            (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) ∧
      (∀ (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1),
        IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u = 1 ∧
          ∀ k : Fin 2, singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η)
            {z | 0 < z k.succ} u = 2 / 3) ∧
      (∀ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
        IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u ≤ 2 / 3 + ε ∧
          ∀ k : Fin 2, 1 - ε ≤ singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η)
            {z | 0 < z k.succ} u) ∧
      (∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3),
        IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 ∧
        ∃ p : Equiv.Perm (Fin 3),
          (∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, ∀ j, 0 < u z (p j) ↔ 0 < z j) ∧
          ∀ j : Fin 3, singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z j} u = 1) ∧
      optimalRecoveryLoss (mesoscalePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 = 0 ∧
      optimalRecoveryLoss (mesoscalePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 <
        optimalRecoveryLoss (mesoscalePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 2 ∧
      optimalRecoveryLoss (mesoscalePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 2 <
        optimalRecoveryLoss (mesoscalePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 1 := by
  obtain ⟨κ, hκ, htwo⟩ := exists_mesoscale_width_two_recovery_margin
  obtain ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, hbudget, hcal, hsmall, hgap⟩ :=
    exists_mesoscale_common_parameters ε κ hε hκ
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  obtain ⟨B₁, u₁, hopt₁⟩ := exists_mesoscale_width_one_optimal_pair δ θ H η
    hδ.le hδone hθ.le hθone hHpos hη
  obtain ⟨B₂, u₂, hopt₂⟩ := exists_mesoscale_width_two_optimal_pair δ θ H η
  obtain ⟨B₃, u₃, hopt₃⟩ := exists_mesoscale_width_three_optimal_pair δ θ H η hHpos hη
  have hloss := mesoscale_actual_optimal_losses_strictly_ordered δ θ H η hδ.le hδone
    hθ hθone.le hHpos hη hcal hgap B₁ u₁ hopt₁ B₂ u₂ hopt₂ B₃ u₃ hopt₃
  rw [hopt₁.loss_eq_optimalRecoveryLoss, hopt₂.loss_eq_optimalRecoveryLoss,
    hopt₃.loss_eq_optimalRecoveryLoss] at hloss
  refine ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, hbudget, hcal,
    mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ.le hδone.le hθ.le hθone.le,
    ?_, ?_, ?_, ?_, hloss.1, hloss.2.1, hloss.2.2⟩
  · intro m hm hmthree
    interval_cases m
    · exact ⟨B₁, u₁, hopt₁⟩
    · exact ⟨B₂, u₂, hopt₂⟩
    · exact ⟨B₃, u₃, hopt₃⟩
  · intro B u hopt
    exact mesoscale_width_one_optimal_pair_F1 δ θ H η hδ.le hδone hθ.le hθone hHpos hη B u hopt
  · intro B u hopt
    obtain ⟨hchild, hparent, hratio⟩ :=
      htwo δ θ H η hδ.le hδone hθ.le hθone hHpos hη hcal hsmall.le B u hopt
    refine ⟨(hparent.trans hratio).trans (by linarith), ?_⟩
    intro k
    exact (by linarith : 1 - ε ≤ 1 - 2 * (δ + θ)).trans (hchild k)
  · intro B u hopt
    exact mesoscalePopulationLaw_width_three_optimum_recovery δ θ H η
      hδ.le hδone.le hθ hθone.le hHpos hη B u hopt

end PKG26AtomicFeatures
