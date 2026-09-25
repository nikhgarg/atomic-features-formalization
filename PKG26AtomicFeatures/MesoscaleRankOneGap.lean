import PKG26AtomicFeatures.MesoscaleReferenceGeometry
import PKG26AtomicFeatures.NonnegativeRankOneRecovery

/-!
# A uniform reference loss gap at width one

The actual three-point reference objective has second moment 641/400.
Its directional second moment is at most 7/10 on the unit sphere. Since
nonnegative rank-one regression can remove no more than that directional
moment, every unit width-one dictionary has reference loss at least 361/400.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators InnerProductSpace

/-- The trace of the actual unnormalized reference second moment. -/
theorem mesoscaleReference_total_second_moment :
    (∑ s, mesoscaleReferenceWeight s * ‖mesoscaleReferenceInput s‖ ^ 2) = (641 / 400 : ℝ) := by
  simp only [mesoscaleReferenceWeight, mesoscaleReferenceInput, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [representationToEuclidean, Matrix.cons_val_two]

/-- A rational upper bound on every actual reference directional moment. -/
theorem mesoscaleNormalMoment_le_seven_tenths (v : EuclideanRepresentation 3) :
    mesoscaleNormalMoment v ≤ (7 / 10 : ℝ) * ‖v‖ ^ 2 := by
  have hnorm : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) = _
    ring
  rw [hnorm]
  dsimp [mesoscaleNormalMoment]
  nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2),
    sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

/-- Actual canonical rank-one NNLS loses at least the orthogonal residual. -/
theorem one_column_nonnegativeLeastSquaresValue_ge_projection_residual
    (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B)
    (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector 1, γ * ‖representationToEuclidean 1 u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖) (x : EuclideanRepresentation 3) :
    ‖x‖ ^ 2 - inner ℝ (representationToEuclidean 3 (B.col 0)) x ^ 2 ≤
      nonnegativeLeastSquaresValue B γ hγ hlower x := by
  rw [one_column_nonnegativeLeastSquaresValue_eq B hunit γ hγ hlower]
  dsimp [nonnegativeRankOneCode]
  by_cases hp : 0 ≤ inner ℝ (representationToEuclidean 3 (B.col 0)) x
  · rw [max_eq_right hp]
  · rw [max_eq_left (le_of_not_ge hp)]
    nlinarith [sq_nonneg (inner ℝ (representationToEuclidean 3 (B.col 0)) x)]

/-- Every unit dictionary has the stated lower bound for the actual
weighted canonical NNLS objective, regardless of the chosen positive
stability witness used to define its unique code. -/
theorem mesoscaleReference_rank_one_loss_ge
    (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B)
    (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector 1, γ * ‖representationToEuclidean 1 u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖) :
    (361 / 400 : ℝ) ≤ ∑ s, mesoscaleReferenceWeight s *
      nonnegativeLeastSquaresValue B γ hγ hlower (mesoscaleReferenceInput s) := by
  let v := representationToEuclidean 3 (B.col 0)
  have hmoment : mesoscaleNormalMoment v ≤ 7 / 10 := by
    simpa only [show ‖v‖ = 1 from hunit 0, one_pow, mul_one] using
      mesoscaleNormalMoment_le_seven_tenths v
  calc
    (361 / 400 : ℝ) ≤ 641 / 400 - mesoscaleNormalMoment v := by linarith
    _ = ∑ s, mesoscaleReferenceWeight s *
        (‖mesoscaleReferenceInput s‖ ^ 2 - inner ℝ v (mesoscaleReferenceInput s) ^ 2) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, mesoscaleReference_total_second_moment,
        ← mesoscaleNormalMoment_eq_weighted_projections]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left
        (one_column_nonnegativeLeastSquaresValue_ge_projection_residual B hunit γ hγ hlower _)
      fin_cases s <;> norm_num [mesoscaleReferenceWeight]

/-- The actual width-one reference risk, using unit columns' derived
margin-one lower bound to define canonical NNLS. -/
noncomputable def mesoscaleReferenceRankOneNNLSRisk
    (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) : ℝ :=
  ∑ s, mesoscaleReferenceWeight s * nonnegativeLeastSquaresValue B 1 (by norm_num)
    ((one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num))
    (mesoscaleReferenceInput s)

/-- The bound exceeds nine tenths, uniformly over actual unit columns. -/
theorem mesoscaleReferenceRankOneNNLSRisk_gt_nine_tenths
    (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) :
    (9 / 10 : ℝ) < mesoscaleReferenceRankOneNNLSRisk B hunit := by
  have h := mesoscaleReference_rank_one_loss_ge B hunit 1 (by norm_num)
    ((one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num))
  change (361 / 400 : ℝ) ≤ mesoscaleReferenceRankOneNNLSRisk B hunit at h
  linarith

/-- The explicit feasible stable width-two benchmark strictly beats every
actual unit width-one dictionary on the same reference inputs and weights. -/
theorem mesoscaleReference_width_one_width_two_strict_gap
    (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) :
    mesoscaleReferenceNNLSRisk mesoscaleBenchmarkDictionary mesoscaleBenchmarkDictionary_stable <
      mesoscaleReferenceRankOneNNLSRisk B hunit := by
  have h1 := mesoscaleReferenceRankOneNNLSRisk_gt_nine_tenths B hunit
  have h2 := mesoscaleBenchmark_referenceRisk_lt
  linarith

end PKG26AtomicFeatures
