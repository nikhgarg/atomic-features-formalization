import PKG26AtomicFeatures.SparseStability

/-!
# Stability of one- and two-column unit dictionaries

For two normalized columns, the lower Euclidean singular margin is determined
exactly by their absolute inner product. The coefficient and representation
norms are both transported to Euclidean space; no function-space supremum norm
is used. An order of four tests all codes at widths one and two.
-/

namespace PKG26AtomicFeatures

open scoped InnerProductSpace

/-- Two-column synthesis is the corresponding linear combination of the
actual Euclidean dictionary columns. -/
theorem two_column_euclidean_mulVec {d : ℕ}
    (B : Matrix (Fin d) (Fin 2) ℝ) (v : FeatureVector 2) :
    representationToEuclidean d (B.mulVec v) =
      v 0 • representationToEuclidean d (B.col 0) +
        v 1 • representationToEuclidean d (B.col 1) := by
  have hvec : B.mulVec v = v 0 • B.col 0 + v 1 • B.col 1 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.col, mul_comm]
  rw [hvec, map_add, map_smul, map_smul]

/-- The coefficient norm at width two is the ordinary sum-of-squares norm. -/
theorem two_coordinate_euclidean_norm_sq (v : FeatureVector 2) :
    ‖representationToEuclidean 2 v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

/-- The actual reconstruction norm is the quadratic form of the unit-column
Gram matrix. -/
theorem two_column_unit_gram_norm_sq {d : ℕ}
    (B : Matrix (Fin d) (Fin 2) ℝ) (hunit : HasUnitEuclideanColumns B)
    (v : FeatureVector 2) :
    ‖representationToEuclidean d (B.mulVec v)‖ ^ 2 =
      (v 0) ^ 2 + (v 1) ^ 2 + 2 * v 0 * v 1 *
        inner ℝ (representationToEuclidean d (B.col 0))
          (representationToEuclidean d (B.col 1)) := by
  rw [two_column_euclidean_mulVec, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, hunit 0, hunit 1, mul_one, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- A normalized two-column dictionary is four-sparse stable exactly when
its absolute column correlation is at most `1-γ²`. The endpoints `γ=0` and
`γ=1` are included. -/
theorem two_column_stable_iff_abs_inner_le {d : ℕ}
    (B : Matrix (Fin d) (Fin 2) ℝ) (hunit : HasUnitEuclideanColumns B)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγone : γ ≤ 1) :
    SparseLowerStable B γ 4 ↔
      |inner ℝ (representationToEuclidean d (B.col 0))
        (representationToEuclidean d (B.col 1))| ≤ 1 - γ ^ 2 := by
  constructor
  · intro hstable
    have hsq (v : FeatureVector 2) :
        γ ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2) ≤
          (v 0) ^ 2 + (v 1) ^ 2 + 2 * v 0 * v 1 *
            inner ℝ (representationToEuclidean d (B.col 0))
              (representationToEuclidean d (B.col 1)) := by
      have hcard : (nonzeroSupport v).card ≤ 4 := by
        have h := Finset.card_le_univ (nonzeroSupport v)
        simp only [Fintype.card_fin] at h
        omega
      have hbound := hstable v hcard
      have hsquare := (sq_le_sq₀ (mul_nonneg hγ (norm_nonneg _))
        (norm_nonneg _)).mpr hbound
      rwa [mul_pow, two_coordinate_euclidean_norm_sq,
        two_column_unit_gram_norm_sq B hunit] at hsquare
    have hplus := hsq ![1, 1]
    have hminus := hsq ![1, -1]
    norm_num at hplus hminus
    apply abs_le.mpr
    constructor <;> nlinarith
  · intro hcorrelation v _
    have hmargin : 0 ≤ 1 - γ ^ 2 := by nlinarith
    have hxy : 2 * |v 0 * v 1| ≤ (v 0) ^ 2 + (v 1) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|v 0| - |v 1|), sq_abs (v 0), sq_abs (v 1)]
    have hfirst := mul_le_mul_of_nonneg_left hcorrelation
      (show 0 ≤ 2 * |v 0 * v 1| by positivity)
    have hsecond := mul_le_mul_of_nonneg_right hxy hmargin
    have hsign := neg_abs_le (v 0 * v 1 *
      inner ℝ (representationToEuclidean d (B.col 0))
        (representationToEuclidean d (B.col 1)))
    rw [abs_mul] at hsign
    apply (sq_le_sq₀ (mul_nonneg hγ (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow, two_coordinate_euclidean_norm_sq,
      two_column_unit_gram_norm_sq B hunit]
    nlinarith

/-- At the mesoscale proposition's margin one half, the allowed two-column
correlations are exactly the interval from minus to plus three quarters. -/
theorem two_column_half_stable_iff_abs_inner_le_three_quarters {d : ℕ}
    (B : Matrix (Fin d) (Fin 2) ℝ) (hunit : HasUnitEuclideanColumns B) :
    SparseLowerStable B (1 / 2) 4 ↔
      |inner ℝ (representationToEuclidean d (B.col 0))
        (representationToEuclidean d (B.col 1))| ≤ 3 / 4 := by
  rw [two_column_stable_iff_abs_inner_le B hunit (1 / 2) (by norm_num) (by norm_num)]
  norm_num

/-- A single unit column is an isometry on its scalar coefficient, so it
has global margin one at every requested sparsity order. -/
theorem one_column_unit_stable {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) (s : ℕ) :
    SparseLowerStable B 1 s := by
  intro v _
  have hvec : B.mulVec v = v 0 • B.col 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.col, mul_comm]
  have hcoef : ‖representationToEuclidean 1 v‖ ^ 2 = (v 0) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]
    rfl
  have hnorm : ‖representationToEuclidean 1 v‖ = |v 0| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    simpa only [sq_abs] using hcoef
  rw [hvec, map_smul, norm_smul, Real.norm_eq_abs, hunit 0, mul_one, one_mul, hnorm]

end PKG26AtomicFeatures
