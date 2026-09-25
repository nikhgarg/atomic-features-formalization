import PKG26AtomicFeatures.TwoColumnStability
import PKG26AtomicFeatures.NonnegativeLeastSquaresPopulation

/-!
# The explicit stable width-two mesoscale benchmark

The actual three-point, unnormalized reference objective in Section 1 of
MESOSCALE_FEATURE_SPLITTING_WITH_STABLE_DICTIONARIES.md. The dictionary has
unit columns with inner product minus three quarters. Explicit nonnegative
codes bound its actual canonical NNLS risk below 49/100.
-/

namespace PKG26AtomicFeatures

open scoped Matrix BigOperators InnerProductSpace

/-- The displayed parent entry with its denominator rationalized. -/
noncomputable def mesoscaleBenchmarkParentEntry : ℝ := 6 * Real.sqrt 2 / 25

noncomputable def mesoscaleBenchmarkH : ℝ := 3 * Real.sqrt 2 / 250 + 7 / 100

noncomputable def mesoscaleBenchmarkK : ℝ := Real.sqrt 7 / 4

/-- The actual 3-by-2 comparison dictionary in equation (2). -/
noncomputable def mesoscaleBenchmarkDictionary : Matrix (Fin 3) (Fin 2) ℝ :=
  !![mesoscaleBenchmarkParentEntry, mesoscaleBenchmarkParentEntry;
    7 / 100 + mesoscaleBenchmarkK, 7 / 100 - mesoscaleBenchmarkK;
    7 / 100 - mesoscaleBenchmarkK, 7 / 100 + mesoscaleBenchmarkK]

theorem mesoscaleBenchmarkParentEntry_eq :
    mesoscaleBenchmarkParentEntry = 12 / (25 * Real.sqrt 2) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [mesoscaleBenchmarkParentEntry]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hs.ne')).mpr
  nlinarith

/-- The two dominant reference inputs, followed by the parent input. -/
noncomputable def mesoscaleReferenceInput (s : Fin 3) : EuclideanRepresentation 3 :=
  representationToEuclidean 3 (![![1 / 20, 1, 0], ![1 / 20, 0, 1], ![1, 0, 0]] s)

/-- The reference weights have total mass 8/5 and are not normalized. -/
noncomputable def mesoscaleReferenceWeight : Fin 3 → ℝ := ![1 / 2, 1 / 2, 3 / 5]

/-- Ray candidates for the dominant inputs and an interior parent code. -/
noncomputable def mesoscaleBenchmarkCode (s : Fin 3) : FeatureVector 2 :=
  ![![mesoscaleBenchmarkH + mesoscaleBenchmarkK, 0],
    ![0, mesoscaleBenchmarkH + mesoscaleBenchmarkK],
    ![24 * Real.sqrt 2 / 25, 24 * Real.sqrt 2 / 25]] s

private theorem norm_sq_three_coordinates (v : FeatureVector 3) :
    ‖representationToEuclidean 3 v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) = _
  ring

private theorem inner_three_coordinates (v w : FeatureVector 3) :
    inner ℝ (representationToEuclidean 3 v) (representationToEuclidean 3 w) =
      v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change w 0 * v 0 + (w 1 * v 1 + w 2 * v 2) = _
  ring

theorem mesoscaleBenchmarkDictionary_unit : HasUnitEuclideanColumns mesoscaleBenchmarkDictionary := by
  intro j
  have hsq := norm_sq_three_coordinates (mesoscaleBenchmarkDictionary.col j)
  have hn := norm_nonneg (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col j))
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs7 := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
  have hsum : mesoscaleBenchmarkDictionary.col j 0 ^ 2 +
      mesoscaleBenchmarkDictionary.col j 1 ^ 2 + mesoscaleBenchmarkDictionary.col j 2 ^ 2 = 1 := by
    fin_cases j <;>
      norm_num [mesoscaleBenchmarkDictionary, mesoscaleBenchmarkParentEntry,
        mesoscaleBenchmarkK, Matrix.col, Matrix.cons_val_two] <;> nlinarith
  rw [hsum] at hsq
  nlinarith

theorem mesoscaleBenchmarkDictionary_inner :
    inner ℝ (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col 0))
      (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col 1)) = -(3 / 4) := by
  rw [inner_three_coordinates]
  norm_num [mesoscaleBenchmarkDictionary, mesoscaleBenchmarkParentEntry,
    mesoscaleBenchmarkK, Matrix.col, Matrix.cons_val_two]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]

theorem mesoscaleBenchmarkDictionary_stable :
    SparseLowerStable mesoscaleBenchmarkDictionary (1 / 2) 4 := by
  apply (two_column_half_stable_iff_abs_inner_le_three_quarters
    mesoscaleBenchmarkDictionary mesoscaleBenchmarkDictionary_unit).mpr
  rw [mesoscaleBenchmarkDictionary_inner]
  norm_num

theorem mesoscaleBenchmarkCode_nonneg (s : Fin 3) (j : Fin 2) :
    0 ≤ mesoscaleBenchmarkCode s j := by
  fin_cases s <;> fin_cases j <;>
    norm_num [mesoscaleBenchmarkCode, mesoscaleBenchmarkH, mesoscaleBenchmarkK] <;> positivity

theorem mesoscaleBenchmark_active_pos : 0 < mesoscaleBenchmarkH + mesoscaleBenchmarkK := by
  dsimp [mesoscaleBenchmarkH, mesoscaleBenchmarkK]
  positivity

private theorem mesoscaleBenchmark_dominant_norm_sq (s : Fin 2) :
    ‖mesoscaleReferenceInput (Fin.castSucc s)‖ ^ 2 = 401 / 400 := by
  fin_cases s <;> norm_num [mesoscaleReferenceInput, norm_sq_three_coordinates, Matrix.cons_val_two]

private theorem mesoscaleBenchmark_dominant_active_inner (s : Fin 2) :
    inner ℝ (mesoscaleReferenceInput (Fin.castSucc s))
      (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col s)) =
        mesoscaleBenchmarkH + mesoscaleBenchmarkK := by
  fin_cases s <;>
    simp only [mesoscaleReferenceInput] <;>
    rw [inner_three_coordinates] <;>
    norm_num [mesoscaleBenchmarkDictionary, mesoscaleBenchmarkParentEntry,
      mesoscaleBenchmarkH, mesoscaleBenchmarkK, Matrix.col, Matrix.cons_val_two] <;> ring

private theorem mesoscaleBenchmark_dominant_synthesis (s : Fin 2) :
    representationToEuclidean 3
      (mesoscaleBenchmarkDictionary.mulVec (mesoscaleBenchmarkCode (Fin.castSucc s))) =
      (mesoscaleBenchmarkH + mesoscaleBenchmarkK) •
        representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col s) := by
  rw [two_column_euclidean_mulVec]
  fin_cases s <;> simp [mesoscaleBenchmarkCode]

/-- The ray candidates have the exact dominant-point residual in equation (3). -/
theorem mesoscaleBenchmark_dominant_residual_sq (s : Fin 2) :
    ‖mesoscaleReferenceInput (Fin.castSucc s) - representationToEuclidean 3
      (mesoscaleBenchmarkDictionary.mulVec (mesoscaleBenchmarkCode (Fin.castSucc s)))‖ ^ 2 =
      401 / 400 - (mesoscaleBenchmarkH + mesoscaleBenchmarkK) ^ 2 := by
  rw [mesoscaleBenchmark_dominant_synthesis, norm_sub_sq_real,
    mesoscaleBenchmark_dominant_norm_sq, norm_smul, Real.norm_eq_abs,
    mesoscaleBenchmarkDictionary_unit s, mul_one, sq_abs, real_inner_smul_right,
    mesoscaleBenchmark_dominant_active_inner]
  ring

private theorem mesoscaleBenchmark_parent_synthesis :
    mesoscaleBenchmarkDictionary.mulVec (mesoscaleBenchmarkCode 2) =
      ![576 / 625, 84 * Real.sqrt 2 / 625, 84 * Real.sqrt 2 / 625] := by
  ext i
  fin_cases i <;>
    norm_num [mesoscaleBenchmarkDictionary, mesoscaleBenchmarkCode,
      mesoscaleBenchmarkParentEntry, mesoscaleBenchmarkK, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.cons_val_two]
  · nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · ring
  · ring

/-- The interior parent candidate has squared residual exactly 49/625. -/
theorem mesoscaleBenchmark_parent_residual_sq :
    ‖mesoscaleReferenceInput 2 - representationToEuclidean 3
      (mesoscaleBenchmarkDictionary.mulVec (mesoscaleBenchmarkCode 2))‖ ^ 2 = 49 / 625 := by
  rw [mesoscaleBenchmark_parent_synthesis]
  change ‖representationToEuclidean 3 ![1, 0, 0] - representationToEuclidean 3 _‖ ^ 2 = _
  rw [← map_sub, norm_sq_three_coordinates]
  norm_num [Matrix.cons_val_two]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Actual canonical NNLS residuals with the exact finite reference weights. -/
noncomputable def mesoscaleReferenceNNLSRisk
    (B : Matrix (Fin 3) (Fin 2) ℝ) (hstable : SparseLowerStable B (1 / 2) 4) : ℝ :=
  ∑ s, mesoscaleReferenceWeight s *
    ‖mesoscaleReferenceInput s - representationToEuclidean 3
      (B.mulVec (nonnegativeLeastSquaresCode B (1 / 2) (by norm_num)
        (hstable.global_bound_of_width_le (by norm_num)) (mesoscaleReferenceInput s)))‖ ^ 2

theorem mesoscaleBenchmark_referenceRisk_le :
    mesoscaleReferenceNNLSRisk mesoscaleBenchmarkDictionary mesoscaleBenchmarkDictionary_stable ≤
      401 / 400 + (3 / 5) * (49 / 625) - (mesoscaleBenchmarkH + mesoscaleBenchmarkK) ^ 2 := by
  calc
    _ ≤ ∑ s, mesoscaleReferenceWeight s *
        ‖mesoscaleReferenceInput s - representationToEuclidean 3
          (mesoscaleBenchmarkDictionary.mulVec (mesoscaleBenchmarkCode s))‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left
      · exact (nonnegativeLeastSquaresCode_isMinimizer mesoscaleBenchmarkDictionary (1 / 2)
          (by norm_num) (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le
            (by norm_num)) (mesoscaleReferenceInput s)).2 _ (mesoscaleBenchmarkCode_nonneg s)
      · fin_cases s <;> norm_num [mesoscaleReferenceWeight]
    _ = _ := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
      have h0 := mesoscaleBenchmark_dominant_residual_sq 0
      have h1 := mesoscaleBenchmark_dominant_residual_sq 1
      norm_num [mesoscaleReferenceWeight, Matrix.cons_val_two] at h0 h1 ⊢
      rw [h0, h1, mesoscaleBenchmark_parent_residual_sq]
      ring

/-- The explicit benchmark's actual NNLS risk is strictly below 49/100,
using exact rational lower bounds on its square roots. -/
theorem mesoscaleBenchmark_referenceRisk_lt :
    mesoscaleReferenceNNLSRisk mesoscaleBenchmarkDictionary mesoscaleBenchmarkDictionary_stable <
      49 / 100 := by
  have hs2 : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hs7 : (529 / 200 : ℝ) < Real.sqrt 7 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_nonneg (7 : ℝ)]
  have hactive : (374109 / 500000 : ℝ) < mesoscaleBenchmarkH + mesoscaleBenchmarkK := by
    dsimp [mesoscaleBenchmarkH, mesoscaleBenchmarkK]
    linarith
  have hsq := (sq_lt_sq₀ (show (0 : ℝ) ≤ 374109 / 500000 by norm_num)
    mesoscaleBenchmark_active_pos.le).mpr hactive
  have hrisk := mesoscaleBenchmark_referenceRisk_le
  nlinarith

/-- The strict inactive optimality inequality in the reference calculation. -/
theorem mesoscaleBenchmark_strict_inactive_scalar :
    (7 * mesoscaleBenchmarkH - mesoscaleBenchmarkK) / 4 < 0 := by
  have hs2 : Real.sqrt 2 < (3 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hs7 : (66 / 25 : ℝ) < Real.sqrt 7 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_nonneg (7 : ℝ)]
  dsimp [mesoscaleBenchmarkH, mesoscaleBenchmarkK]
  linarith

private theorem mesoscaleBenchmark_dominant_inactive_inner (s : Fin 2) :
    inner ℝ (mesoscaleReferenceInput (Fin.castSucc s))
      (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col s.rev)) =
        mesoscaleBenchmarkH - mesoscaleBenchmarkK := by
  fin_cases s <;>
    simp only [mesoscaleReferenceInput] <;> rw [inner_three_coordinates] <;>
    norm_num [mesoscaleBenchmarkDictionary, mesoscaleBenchmarkParentEntry,
      mesoscaleBenchmarkH, mesoscaleBenchmarkK, Matrix.col, Matrix.cons_val_two, Fin.rev] <;> ring

private theorem mesoscaleBenchmark_cross_inner (s : Fin 2) :
    inner ℝ (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col s))
      (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col s.rev)) = -(3 / 4) := by
  fin_cases s
  · exact mesoscaleBenchmarkDictionary_inner
  · rw [real_inner_comm]
    exact mesoscaleBenchmarkDictionary_inner

theorem mesoscaleBenchmark_dominant_active_gradient (s : Fin 2) :
    inner ℝ (mesoscaleReferenceInput (Fin.castSucc s) - representationToEuclidean 3
      (mesoscaleBenchmarkDictionary.mulVec (mesoscaleBenchmarkCode (Fin.castSucc s))))
      (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col s)) = 0 := by
  rw [mesoscaleBenchmark_dominant_synthesis, inner_sub_left, real_inner_smul_left,
    mesoscaleBenchmark_dominant_active_inner, real_inner_self_eq_norm_sq,
    mesoscaleBenchmarkDictionary_unit s]
  ring

/-- Each dominant point has a strictly negative inactive-coordinate
residual inner product at its explicit positive one-ray code. -/
theorem mesoscaleBenchmark_dominant_strict_inactive_gradient (s : Fin 2) :
    inner ℝ (mesoscaleReferenceInput (Fin.castSucc s) - representationToEuclidean 3
      (mesoscaleBenchmarkDictionary.mulVec (mesoscaleBenchmarkCode (Fin.castSucc s))))
      (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col s.rev)) < 0 := by
  rw [mesoscaleBenchmark_dominant_synthesis, inner_sub_left, real_inner_smul_left,
    mesoscaleBenchmark_dominant_inactive_inner, mesoscaleBenchmark_cross_inner]
  have h := mesoscaleBenchmark_strict_inactive_scalar
  nlinarith

private theorem nonnegativeLeastSquares_of_two_column_gradients
    {B : Matrix (Fin 3) (Fin 2) ℝ} {x : EuclideanRepresentation 3} {u : FeatureVector 2}
    (hnonneg : ∀ j, 0 ≤ u j)
    (hgrad : ∀ j, inner ℝ (x - representationToEuclidean 3 (B.mulVec u))
      (representationToEuclidean 3 (B.col j)) ≤ 0)
    (hcomplement : ∀ j, u j * inner ℝ (x - representationToEuclidean 3 (B.mulVec u))
      (representationToEuclidean 3 (B.col j)) = 0) :
    IsNonnegativeLeastSquaresCode B x u := by
  refine ⟨hnonneg, fun v hv => ?_⟩
  let r := x - representationToEuclidean 3 (B.mulVec u)
  have hcross : inner ℝ r (representationToEuclidean 3 (B.mulVec v) -
      representationToEuclidean 3 (B.mulVec u)) ≤ 0 := by
    rw [inner_sub_right, two_column_euclidean_mulVec B v, two_column_euclidean_mulVec B u,
      inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right]
    change v 0 * inner ℝ r _ + v 1 * inner ℝ r _ -
      (u 0 * inner ℝ r _ + u 1 * inner ℝ r _) ≤ 0
    rw [hcomplement 0, hcomplement 1, add_zero, sub_zero]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (hv 0) (hgrad 0))
      (mul_nonpos_of_nonneg_of_nonpos (hv 1) (hgrad 1))
  have heq : x - representationToEuclidean 3 (B.mulVec v) =
      r - (representationToEuclidean 3 (B.mulVec v) -
        representationToEuclidean 3 (B.mulVec u)) := by dsimp [r]; abel
  conv_rhs => rw [heq, norm_sub_sq_real]
  change ‖r‖ ^ 2 ≤ _
  nlinarith [sq_nonneg ‖representationToEuclidean 3 (B.mulVec v) -
    representationToEuclidean 3 (B.mulVec u)‖]

/-- The explicit positive one-sparse dominant codes are actual NNLS
minimizers, not merely feasible comparator codes. -/
theorem mesoscaleBenchmark_dominant_isNNLS (s : Fin 2) :
    IsNonnegativeLeastSquaresCode mesoscaleBenchmarkDictionary
      (mesoscaleReferenceInput (Fin.castSucc s)) (mesoscaleBenchmarkCode (Fin.castSucc s)) := by
  apply nonnegativeLeastSquares_of_two_column_gradients
    (mesoscaleBenchmarkCode_nonneg (Fin.castSucc s))
  · intro j
    by_cases h : j = s
    · subst j
      exact (mesoscaleBenchmark_dominant_active_gradient s).le
    · have hj : j = s.rev := by fin_cases s <;> fin_cases j <;> simp_all [Fin.rev]
      subst j
      exact (mesoscaleBenchmark_dominant_strict_inactive_gradient s).le
  · intro j
    by_cases h : j = s
    · subst j
      rw [mesoscaleBenchmark_dominant_active_gradient, mul_zero]
    · have hj : j = s.rev := by fin_cases s <;> fin_cases j <;> simp_all [Fin.rev]
      subst j
      have hzero : mesoscaleBenchmarkCode (Fin.castSucc s) s.rev = 0 := by
        fin_cases s <;> simp [mesoscaleBenchmarkCode, Fin.rev]
      rw [hzero, zero_mul]

/-- Uniqueness identifies the canonical NNLS code with the displayed
positive one-ray code for both dominant reference inputs. -/
theorem mesoscaleBenchmark_dominant_NNLS_code (s : Fin 2) :
    nonnegativeLeastSquaresCode mesoscaleBenchmarkDictionary (1 / 2) (by norm_num)
      (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))
      (mesoscaleReferenceInput (Fin.castSucc s)) = mesoscaleBenchmarkCode (Fin.castSucc s) :=
  ((mesoscaleBenchmark_dominant_isNNLS s).eq_nonnegativeLeastSquaresCode
    (by norm_num) (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))).symm

theorem mesoscaleBenchmark_dominant_code_support (s : Fin 2) :
    nonzeroSupport (mesoscaleBenchmarkCode (Fin.castSucc s)) = {s} := by
  classical
  have hne := mesoscaleBenchmark_active_pos.ne'
  fin_cases s <;> ext j <;> fin_cases j <;>
    simp [mesoscaleBenchmarkCode, nonzeroSupport, hne]


/-- The interior parent candidate has zero residual inner product with
both columns. -/
theorem mesoscaleBenchmark_parent_gradient (j : Fin 2) :
    inner ℝ (mesoscaleReferenceInput 2 - representationToEuclidean 3
      (mesoscaleBenchmarkDictionary.mulVec (mesoscaleBenchmarkCode 2)))
      (representationToEuclidean 3 (mesoscaleBenchmarkDictionary.col j)) = 0 := by
  rw [mesoscaleBenchmark_parent_synthesis]
  change inner ℝ (representationToEuclidean 3 ![1, 0, 0] - representationToEuclidean 3 _)
    (representationToEuclidean 3 _) = 0
  rw [← map_sub, inner_three_coordinates]
  fin_cases j <;>
    norm_num [mesoscaleBenchmarkDictionary, mesoscaleBenchmarkParentEntry,
      mesoscaleBenchmarkK, Matrix.col, Matrix.cons_val_two] <;> ring

theorem mesoscaleBenchmark_parent_isNNLS :
    IsNonnegativeLeastSquaresCode mesoscaleBenchmarkDictionary
      (mesoscaleReferenceInput 2) (mesoscaleBenchmarkCode 2) := by
  apply nonnegativeLeastSquares_of_two_column_gradients (mesoscaleBenchmarkCode_nonneg 2)
  · intro j
    exact (mesoscaleBenchmark_parent_gradient j).le
  · intro j
    rw [mesoscaleBenchmark_parent_gradient, mul_zero]

/-- All three displayed codes are the actual unique canonical NNLS codes. -/
theorem mesoscaleBenchmark_NNLS_code (s : Fin 3) :
    nonnegativeLeastSquaresCode mesoscaleBenchmarkDictionary (1 / 2) (by norm_num)
      (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))
      (mesoscaleReferenceInput s) = mesoscaleBenchmarkCode s := by
  fin_cases s
  · exact mesoscaleBenchmark_dominant_NNLS_code 0
  · exact mesoscaleBenchmark_dominant_NNLS_code 1
  · exact (mesoscaleBenchmark_parent_isNNLS.eq_nonnegativeLeastSquaresCode (by norm_num)
      (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))).symm

/-- Equation (3) for the actual NNLS risk, now as an equality. -/
theorem mesoscaleBenchmark_referenceRisk_eq :
    mesoscaleReferenceNNLSRisk mesoscaleBenchmarkDictionary mesoscaleBenchmarkDictionary_stable =
      401 / 400 + (3 / 5) * (49 / 625) - (mesoscaleBenchmarkH + mesoscaleBenchmarkK) ^ 2 := by
  unfold mesoscaleReferenceNNLSRisk
  simp only [mesoscaleBenchmark_NNLS_code]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h0 := mesoscaleBenchmark_dominant_residual_sq 0
  have h1 := mesoscaleBenchmark_dominant_residual_sq 1
  norm_num [mesoscaleReferenceWeight, Matrix.cons_val_two] at h0 h1 ⊢
  rw [h0, h1, mesoscaleBenchmark_parent_residual_sq]
  ring

end PKG26AtomicFeatures
