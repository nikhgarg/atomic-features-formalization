import PKG26AtomicFeatures.MesoscaleReferenceBenchmark

/-!
# Geometry of low-loss mesoscale reference planes

Any dictionary beating the explicit reference benchmark has a plane normal
whose two child coordinates share a sign and whose parent coordinate has the
opposite sign. The actual NNLS risk bounds the squared normal projections;
the exclusion of other sign patterns follows by rational completed squares.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators InnerProductSpace

/-- The reference moment quadratic, evaluated at an actual plane normal. -/
noncomputable def mesoscaleNormalMoment (n : EuclideanRepresentation 3) : ℝ :=
  (241 / 400) * n 0 ^ 2 + (1 / 2) * (n 1 ^ 2 + n 2 ^ 2) +
    (1 / 20) * n 0 * (n 1 + n 2)

theorem mesoscaleNormalMoment_eq_weighted_projections (n : EuclideanRepresentation 3) :
    mesoscaleNormalMoment n =
      ∑ s, mesoscaleReferenceWeight s * inner ℝ n (mesoscaleReferenceInput s) ^ 2 := by
  simp only [mesoscaleNormalMoment, mesoscaleReferenceWeight, mesoscaleReferenceInput,
    PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [representationToEuclidean, real_inner_eq_re_inner, RCLike.inner_apply,
    Matrix.cons_val_two]
  ring

/-- Every reconstruction in the learned plane retains the source's normal
component in its residual, independently of code optimality. -/
theorem squared_normal_projection_le_residual
    (B : Matrix (Fin 3) (Fin 2) ℝ) (n x : EuclideanRepresentation 3)
    (hn : ‖n‖ = 1)
    (horth : ∀ j, inner ℝ n (representationToEuclidean 3 (B.col j)) = 0)
    (u : FeatureVector 2) :
    inner ℝ n x ^ 2 ≤ ‖x - representationToEuclidean 3 (B.mulVec u)‖ ^ 2 := by
  have hzero : inner ℝ n (representationToEuclidean 3 (B.mulVec u)) = 0 := by
    rw [two_column_euclidean_mulVec B u, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, horth 0, horth 1]
    ring
  have h := abs_real_inner_le_norm n (x - representationToEuclidean 3 (B.mulVec u))
  rw [inner_sub_right, hzero, sub_zero, hn, one_mul] at h
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h

/-- The reference moment is a lower bound on the actual NNLS objective
of any dictionary with this normal. -/
theorem mesoscaleNormalMoment_le_referenceRisk
    (B : Matrix (Fin 3) (Fin 2) ℝ) (hstable : SparseLowerStable B (1 / 2) 4)
    (n : EuclideanRepresentation 3) (hn : ‖n‖ = 1)
    (horth : ∀ j, inner ℝ n (representationToEuclidean 3 (B.col j)) = 0) :
    mesoscaleNormalMoment n ≤ mesoscaleReferenceNNLSRisk B hstable := by
  rw [mesoscaleNormalMoment_eq_weighted_projections, mesoscaleReferenceNNLSRisk]
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left (squared_normal_projection_le_residual B n _ hn horth _)
  fin_cases s <;> norm_num [mesoscaleReferenceWeight]

/-- A completed square excludes opposite child signs below 49/100. -/
theorem mesoscaleNormalMoment_ge_cutoff_of_child_product_nonpos
    (n : EuclideanRepresentation 3) (hn : ‖n‖ = 1) (hchildren : n 1 * n 2 ≤ 0) :
    (49 / 100 : ℝ) ≤ mesoscaleNormalMoment n := by
  have hnorm : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq n
    rw [hn] at h
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_pow, add_assoc] using h.symm
  have hs := sq_nonneg (n 1 + n 2 + (5 / 2 : ℝ) * n 0)
  dsimp [mesoscaleNormalMoment]
  nlinarith [sq_nonneg (n 0)]

/-- Below the feasible benchmark, a unit normal's children share a sign,
and its parent has the opposite sign. This applies in particular to every
global reference minimizer. -/
theorem mesoscale_low_referenceRisk_normal_signs
    (B : Matrix (Fin 3) (Fin 2) ℝ) (hstable : SparseLowerStable B (1 / 2) 4)
    (hloss : mesoscaleReferenceNNLSRisk B hstable < 49 / 100)
    (n : EuclideanRepresentation 3) (hn : ‖n‖ = 1)
    (horth : ∀ j, inner ℝ n (representationToEuclidean 3 (B.col j)) = 0) :
    0 < n 1 * n 2 ∧ n 0 * n 1 < 0 := by
  have hmoment := (mesoscaleNormalMoment_le_referenceRisk B hstable n hn horth).trans_lt hloss
  have hchildren : 0 < n 1 * n 2 := by
    by_contra h
    exact (not_lt_of_ge (mesoscaleNormalMoment_ge_cutoff_of_child_product_nonpos n hn
      (le_of_not_gt h))) hmoment
  have hnorm : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq n
    rw [hn] at h
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_pow, add_assoc] using h.symm
  refine ⟨hchildren, ?_⟩
  by_contra h
  have h01 : 0 ≤ n 0 * n 1 := le_of_not_gt h
  have h02 : 0 ≤ n 0 * n 2 := by
    rcases (mul_pos_iff.mp hchildren) with hpos | hneg
    · have hp : 0 ≤ n 0 := (mul_nonneg_iff_of_pos_right hpos.1).mp h01
      exact mul_nonneg hp hpos.2.le
    · have hp : n 0 ≤ 0 := by nlinarith [hneg.1]
      exact mul_nonneg_of_nonpos_of_nonpos hp hneg.2.le
  dsimp [mesoscaleNormalMoment] at hmoment
  nlinarith [sq_nonneg (n 0)]

end PKG26AtomicFeatures
