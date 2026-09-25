import PKG26AtomicFeatures.MesoscaleRiskPerturbation
import PKG26AtomicFeatures.MesoscaleRankOneGap
import PKG26AtomicFeatures.MesoscalePositiveLoss
import PKG26AtomicFeatures.MesoscaleWidthThreeRecovery

/-!
# Strict loss ordering for the actual mesoscale population

Calibration of the rare parent mass transfers the reference width-one lower
bound and the explicit width-two benchmark to the actual population law.
A sufficiently small perturbation separates their actual losses. The positive
cube component excludes zero loss at width two, whereas every width-three
optimum attains zero loss.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal BigOperators

/-- Canonical nonnegative regression on the explicit stable benchmark dictionary. -/
noncomputable def mesoscaleBenchmarkPopulationEncoder : FeatureVector 3 → FeatureVector 2 :=
  nonnegativeLeastSquaresEncoder (representationToEuclidean 3)
    mesoscaleBenchmarkDictionary (1 / 2) (by norm_num)
    (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))

/-- The benchmark's actual finite population risk. -/
noncomputable def mesoscaleBenchmarkPopulationRisk (δ θ H η : ℝ) : ℝ :=
  nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
    (representationToEuclidean 3) mesoscaleBenchmarkDictionary (1 / 2) (by norm_num)
    (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))

theorem mesoscaleBenchmarkPopulationEncoder_feasible :
    IsFeasibleRecoveryPair mesoscaleBenchmarkDictionary mesoscaleBenchmarkPopulationEncoder (1 / 2) 2 :=
  isFeasibleRecoveryPair_nonnegativeLeastSquaresEncoder
    (representationToEuclidean 3).continuous.measurable mesoscaleBenchmarkDictionary (1 / 2)
    (by norm_num) _ mesoscaleBenchmarkDictionary_unit mesoscaleBenchmarkDictionary_stable (by norm_num)

theorem mesoscaleBenchmarkPopulationRisk_actual_loss (δ θ H η : ℝ) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id mesoscaleBenchmarkDictionary
      mesoscaleBenchmarkPopulationEncoder = ENNReal.ofReal (mesoscaleBenchmarkPopulationRisk δ θ H η) := by
  symm
  simpa only [mesoscaleBenchmarkPopulationRisk, mesoscaleBenchmarkPopulationEncoder,
    actualPopulationSquaredLoss, euclideanPopulationSquaredLoss, Matrix.one_mulVec, id_eq] using
    ofReal_nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
      (representationToEuclidean 3).continuous.measurable
      (integrable_mesoscalePopulation_secondMoment δ θ H η) mesoscaleBenchmarkDictionary
      (1 / 2) (by norm_num)
      (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))

/-- The actual benchmark risk is below the canonical risk of every unit
width-one dictionary. The gap follows from the primitive calibrated mixture
parameters, not from an assumed risk comparison. -/
theorem mesoscaleBenchmarkPopulationRisk_lt_rank_one_risk
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ))
    (hsmall : δ * η * (2 * H + η) + 2 * θ < (1 - δ) / 10)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) :
    mesoscaleBenchmarkPopulationRisk δ θ H η <
      nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
        (representationToEuclidean 3) B 1 (by norm_num)
        ((one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num)) := by
  let hlower := (one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num : 1 ≤ 1)
  have hpert1 := abs_le.mp (nnls_mesoscalePopulation_perturbation B 1 (by norm_num)
    hlower δ θ H η hδ hδone.le hθ hθone hH hη hcal)
  have hpert2 := abs_le.mp (nnls_mesoscalePopulation_perturbation mesoscaleBenchmarkDictionary
    (1 / 2) (by norm_num) (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))
    δ θ H η hδ hδone.le hθ hθone hH hη hcal)
  have hscale1 := mul_le_mul_of_nonneg_left
    (mesoscaleReference_rank_one_loss_ge B hunit 1 (by norm_num) hlower)
    (sub_nonneg.mpr hδone.le)
  have hscale2 := mul_lt_mul_of_pos_left mesoscaleBenchmark_referenceRisk_lt (sub_pos.mpr hδone)
  change _ < nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
    (representationToEuclidean 3) B 1 (by norm_num) hlower
  have hupper2 := hpert2.2
  change mesoscaleBenchmarkPopulationRisk δ θ H η -
    (1 - δ) * mesoscaleReferenceNNLSRisk mesoscaleBenchmarkDictionary
      mesoscaleBenchmarkDictionary_stable ≤ _ at hupper2
  nlinarith [hpert1.1, hupper2]

/-- Every nonnegative width-one encoder has at least its canonical NNLS
risk, retaining infinite competing loss through the nonnegative integral. -/
theorem mesoscale_rank_one_canonical_risk_le_actual_loss
    (δ θ H η : ℝ) (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B)
    (u : FeatureVector 3 → FeatureVector 1) (hnonneg : ∀ z j, 0 ≤ u z j) :
    ENNReal.ofReal (nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
      (representationToEuclidean 3) B 1 (by norm_num)
      ((one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num))) ≤
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u := by
  rw [ofReal_nonnegativeLeastSquaresPopulationRisk _
    (representationToEuclidean 3).continuous.measurable
    (integrable_mesoscalePopulation_secondMoment δ θ H η)]
  unfold actualPopulationSquaredLoss euclideanPopulationSquaredLoss
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  simpa only [Matrix.one_mulVec, id_eq, nonnegativeLeastSquaresEncoder, Function.comp_apply] using
    (nonnegativeLeastSquaresCode_isMinimizer B 1 (by norm_num)
      ((one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num))
      (representationToEuclidean 3 z)).2 (u z) (hnonneg z)

/-- Every actual width-two global optimum beats every feasible width-one
pair. Width-one optimality is unnecessary for this stronger comparison. -/
theorem mesoscale_width_two_optimum_loss_lt_width_one_feasible
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ))
    (hsmall : δ * η * (2 * H + η) + 2 * θ < (1 - δ) / 10)
    (B₁ : Matrix (Fin 3) (Fin 1) ℝ) (u₁ : FeatureVector 3 → FeatureVector 1)
    (hfeas₁ : IsFeasibleRecoveryPair B₁ u₁ (1 / 2) 2)
    (B₂ : Matrix (Fin 3) (Fin 2) ℝ) (u₂ : FeatureVector 3 → FeatureVector 2)
    (hopt₂ : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ <
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₁ u₁ := by
  have hupper := hopt₂.2 mesoscaleBenchmarkDictionary mesoscaleBenchmarkPopulationEncoder
    mesoscaleBenchmarkPopulationEncoder_feasible
  rw [ENNReal.ofReal_one, one_mul, mesoscaleBenchmarkPopulationRisk_actual_loss] at hupper
  have hgap := mesoscaleBenchmarkPopulationRisk_lt_rank_one_risk δ θ H η
    hδ hδone hθ hθone hH hη hcal hsmall B₁ hfeas₁.1
  have hbase : 0 ≤ mesoscaleBenchmarkPopulationRisk δ θ H η :=
    integral_nonneg fun _ => sq_nonneg _
  have henn : ENNReal.ofReal (mesoscaleBenchmarkPopulationRisk δ θ H η) <
      ENNReal.ofReal (nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
        (representationToEuclidean 3) B₁ 1 (by norm_num)
        ((one_column_unit_stable B₁ hfeas₁.1 1).global_bound_of_width_le (by norm_num))) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hbase).mpr hgap
  exact (hupper.trans_lt henn).trans_le
    (mesoscale_rank_one_canonical_risk_le_actual_loss δ θ H η B₁ hfeas₁.1 u₁ hfeas₁.2.2.2.2)

/-- The actual globally optimal losses at widths one, two, and three are
strictly ordered, with the width-three loss equal to zero. All objectives
are the original nonnegative population integrals over actual feasible pairs. -/
theorem mesoscale_actual_optimal_losses_strictly_ordered
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hθ : 0 < θ) (hθone : θ ≤ 1) (hH : 0 < H) (hη : 0 < η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ))
    (hsmall : δ * η * (2 * H + η) + 2 * θ < (1 - δ) / 10)
    (B₁ : Matrix (Fin 3) (Fin 1) ℝ) (u₁ : FeatureVector 3 → FeatureVector 1)
    (hopt₁ : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₁ u₁ (1 / 2) 1 2)
    (B₂ : Matrix (Fin 3) (Fin 2) ℝ) (u₂ : FeatureVector 3 → FeatureVector 2)
    (hopt₂ : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ (1 / 2) 1 2)
    (B₃ : Matrix (Fin 3) (Fin 3) ℝ) (u₃ : FeatureVector 3 → FeatureVector 3)
    (hopt₃ : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₃ u₃ (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₃ u₃ = 0 ∧
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₃ u₃ <
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ ∧
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ <
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₁ u₁ := by
  have hzero := mesoscalePopulationLaw_width_three_optimum_zero_loss δ θ H η hH hη B₃ u₃ hopt₃
  refine ⟨hzero, ?_, ?_⟩
  · rw [hzero]
    exact mesoscalePopulationLaw_loss_pos_of_width_lt_three δ θ H η hθ (by norm_num) B₂ u₂
      hopt₂.1.2.2.1
  · exact mesoscale_width_two_optimum_loss_lt_width_one_feasible δ θ H η
      hδ hδone hθ.le hθone hH.le hη.le hcal hsmall B₁ u₁ hopt₁.1 B₂ u₂ hopt₂

end PKG26AtomicFeatures
