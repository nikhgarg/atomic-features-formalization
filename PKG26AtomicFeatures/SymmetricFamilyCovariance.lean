import PKG26AtomicFeatures.TwoColumnStability
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The unique positive leading direction of a symmetric family covariance

For the actual matrix with rows (a,b,b), (b,c,0), and (b,0,c), a positive
parent-child cross moment b forces a unique leading line. The explicit
positive symmetric vector and the completed-square identity below prove
this directly, without assumed eigenvectors or a spectral certificate.
-/

namespace PKG26AtomicFeatures

open scoped Matrix BigOperators InnerProductSpace

/-- The actual covariance shape of a symmetric parent-child family. -/
noncomputable def symmetricFamilyCovariance (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, b, b; b, c, 0; b, 0, c]

/-- Apply the actual covariance in Euclidean coordinates. -/
noncomputable def symmetricFamilyCovarianceAction (a b c : ℝ)
    (v : EuclideanRepresentation 3) : EuclideanRepresentation 3 :=
  representationToEuclidean 3 ((symmetricFamilyCovariance a b c).mulVec (fun j => v j))

/-- The explicit larger eigenvalue of the parent/symmetric-child block. -/
noncomputable def symmetricFamilyLeadingValue (a b c : ℝ) : ℝ :=
  (a + c + Real.sqrt ((a - c) ^ 2 + 8 * b ^ 2)) / 2

/-- The positive child-to-parent ratio of the leading direction. -/
noncomputable def symmetricFamilyLeadingSlope (a b c : ℝ) : ℝ :=
  b / (symmetricFamilyLeadingValue a b c - c)

noncomputable def symmetricFamilyLeadingSeed (a b c : ℝ) : EuclideanRepresentation 3 :=
  representationToEuclidean 3 ![1, symmetricFamilyLeadingSlope a b c, symmetricFamilyLeadingSlope a b c]

/-- The displayed normalized, positive, child-symmetric leading direction. -/
noncomputable def symmetricFamilyLeadingDirection (a b c : ℝ) : EuclideanRepresentation 3 :=
  NormedSpace.normalize (symmetricFamilyLeadingSeed a b c)

/-- A strictly positive cross moment puts the leading value above both
diagonal values, including the antisymmetric-child eigenvalue c. -/
theorem symmetricFamilyLeadingValue_gt (a b c : ℝ) (hb : 0 < b) :
    a < symmetricFamilyLeadingValue a b c ∧ c < symmetricFamilyLeadingValue a b c := by
  have hnonneg : 0 ≤ (a - c) ^ 2 + 8 * b ^ 2 := by positivity
  have hs := Real.sq_sqrt hnonneg
  have hsnonneg := Real.sqrt_nonneg ((a - c) ^ 2 + 8 * b ^ 2)
  have hbsq : 0 < b ^ 2 := sq_pos_of_pos hb
  have hsq : |a - c| ^ 2 < (Real.sqrt ((a - c) ^ 2 + 8 * b ^ 2)) ^ 2 := by
    rw [sq_abs]
    nlinarith
  have habs := (sq_lt_sq₀ (abs_nonneg (a - c)) hsnonneg).mp hsq
  dsimp [symmetricFamilyLeadingValue]
  constructor <;> linarith [le_abs_self (a - c), neg_abs_le (a - c)]

/-- The exact characteristic equation used in the completed square. -/
theorem symmetricFamilyLeadingValue_characteristic (a b c : ℝ) :
    (symmetricFamilyLeadingValue a b c - a) * (symmetricFamilyLeadingValue a b c - c) =
      2 * b ^ 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ (a - c) ^ 2 + 8 * b ^ 2 by positivity)
  dsimp [symmetricFamilyLeadingValue]
  nlinarith

theorem symmetricFamilyLeadingSlope_pos (a b c : ℝ) (hb : 0 < b) :
    0 < symmetricFamilyLeadingSlope a b c :=
  div_pos hb (sub_pos.mpr (symmetricFamilyLeadingValue_gt a b c hb).2)

private theorem symmetricFamilyLeadingSeed_ne_zero (a b c : ℝ) :
    symmetricFamilyLeadingSeed a b c ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : EuclideanRepresentation 3 => v 0) h
  norm_num [symmetricFamilyLeadingSeed, representationToEuclidean] at h0

/-- Normalizing the displayed nonzero seed gives an actual unit vector. -/
theorem symmetricFamilyLeadingDirection_unit (a b c : ℝ) :
    ‖symmetricFamilyLeadingDirection a b c‖ = 1 :=
  NormedSpace.norm_normalize (symmetricFamilyLeadingSeed_ne_zero a b c)

/-- Every coordinate of the leading direction is strictly positive. -/
theorem symmetricFamilyLeadingDirection_pos (a b c : ℝ) (hb : 0 < b) (j : Fin 3) :
    0 < symmetricFamilyLeadingDirection a b c j := by
  have hslope := symmetricFamilyLeadingSlope_pos a b c hb
  have hnorm := norm_pos_iff.mpr (symmetricFamilyLeadingSeed_ne_zero a b c)
  change 0 < ‖symmetricFamilyLeadingSeed a b c‖⁻¹ * symmetricFamilyLeadingSeed a b c j
  apply mul_pos (inv_pos.mpr hnorm)
  fin_cases j <;> simpa [symmetricFamilyLeadingSeed, representationToEuclidean,
    Matrix.cons_val_two] using (show 0 < symmetricFamilyLeadingSlope a b c from hslope)

/-- The leading direction is invariant under swapping the two children. -/
theorem symmetricFamilyLeadingDirection_child_symmetry (a b c : ℝ) :
    symmetricFamilyLeadingDirection a b c 1 = symmetricFamilyLeadingDirection a b c 2 := by
  rfl

/-- The exact completed-square identity for the actual matrix and actual
Euclidean norm. It proves the global Rayleigh bound simultaneously for all
vectors, not merely for a guessed eigendirection. -/
theorem symmetricFamilyCovariance_completed_square (a b c : ℝ) (hb : 0 < b)
    (v : EuclideanRepresentation 3) :
    symmetricFamilyLeadingValue a b c * ‖v‖ ^ 2 - inner ℝ v (symmetricFamilyCovarianceAction a b c v) =
      (symmetricFamilyLeadingValue a b c - c) *
        ((v 1 - symmetricFamilyLeadingSlope a b c * v 0) ^ 2 +
          (v 2 - symmetricFamilyLeadingSlope a b c * v 0) ^ 2) := by
  let ev := symmetricFamilyLeadingValue a b c
  let t := symmetricFamilyLeadingSlope a b c
  have hgap : ev - c ≠ 0 := (sub_pos.mpr (symmetricFamilyLeadingValue_gt a b c hb).2).ne'
  have hbt : b = (ev - c) * t := by
    change b = (ev - c) * (b / (ev - c))
    field_simp [hgap]
  have ha : ev - a = 2 * (ev - c) * t ^ 2 := by
    calc
      ev - a = (2 * b ^ 2) / (ev - c) :=
        (eq_div_iff hgap).mpr (symmetricFamilyLeadingValue_characteristic a b c)
      _ = _ := by
        dsimp [t, symmetricFamilyLeadingSlope]
        change 2 * b ^ 2 / (ev - c) = 2 * (ev - c) * (b / (ev - c)) ^ 2
        field_simp
        <;> ring
  have hnorm : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2
    ring
  have hinner : inner ℝ v (symmetricFamilyCovarianceAction a b c v) =
      a * v 0 ^ 2 + c * (v 1 ^ 2 + v 2 ^ 2) + 2 * b * v 0 * (v 1 + v 2) := by
    simp only [symmetricFamilyCovarianceAction, symmetricFamilyCovariance, PiLp.inner_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    norm_num [representationToEuclidean, real_inner_eq_re_inner, RCLike.inner_apply,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    ring
  change ev * ‖v‖ ^ 2 - inner ℝ v (symmetricFamilyCovarianceAction a b c v) =
    (ev - c) * ((v 1 - t * v 0) ^ 2 + (v 2 - t * v 0) ^ 2)
  rw [hnorm, hinner]
  calc
    _ = (ev - a) * v 0 ^ 2 + (ev - c) * (v 1 ^ 2 + v 2 ^ 2) -
        2 * b * v 0 * (v 1 + v 2) := by ring
    _ = _ := by rw [ha, hbt]; ring

/-- The leading value bounds the actual unit-vector Rayleigh quotient. -/
theorem symmetricFamilyCovariance_rayleigh_le (a b c : ℝ) (hb : 0 < b)
    (v : EuclideanRepresentation 3) (hv : ‖v‖ = 1) :
    inner ℝ v (symmetricFamilyCovarianceAction a b c v) ≤ symmetricFamilyLeadingValue a b c := by
  have h := symmetricFamilyCovariance_completed_square a b c hb v
  have hnonneg := mul_nonneg (sub_pos.mpr (symmetricFamilyLeadingValue_gt a b c hb).2).le
    (add_nonneg (sq_nonneg (v 1 - symmetricFamilyLeadingSlope a b c * v 0))
      (sq_nonneg (v 2 - symmetricFamilyLeadingSlope a b c * v 0)))
  rw [hv] at h
  nlinarith

/-- At a unit vector, equality holds exactly on the displayed leading
line. This includes both signs and no other maximizing directions. -/
theorem symmetricFamilyCovariance_rayleigh_eq_iff (a b c : ℝ) (hb : 0 < b)
    (v : EuclideanRepresentation 3) (hv : ‖v‖ = 1) :
    inner ℝ v (symmetricFamilyCovarianceAction a b c v) = symmetricFamilyLeadingValue a b c ↔
      v = symmetricFamilyLeadingDirection a b c ∨ v = -symmetricFamilyLeadingDirection a b c := by
  let t := symmetricFamilyLeadingSlope a b c
  have hgap : 0 < symmetricFamilyLeadingValue a b c - c :=
    sub_pos.mpr (symmetricFamilyLeadingValue_gt a b c hb).2
  constructor
  · intro heq
    have h := symmetricFamilyCovariance_completed_square a b c hb v
    rw [hv, heq] at h
    have hsum : (v 1 - t * v 0) ^ 2 + (v 2 - t * v 0) ^ 2 = 0 := by
      have hprod : (symmetricFamilyLeadingValue a b c - c) *
          ((v 1 - t * v 0) ^ 2 + (v 2 - t * v 0) ^ 2) = 0 := by simpa using h.symm
      exact (mul_eq_zero.mp hprod).resolve_left hgap.ne'
    have h1 : v 1 = t * v 0 := by nlinarith [sq_nonneg (v 2 - t * v 0)]
    have h2 : v 2 = t * v 0 := by nlinarith [sq_nonneg (v 1 - t * v 0)]
    have hrepr : v = v 0 • symmetricFamilyLeadingSeed a b c := by
      ext j
      fin_cases j
      · change v 0 = v 0 * 1
        ring
      · change v 1 = v 0 * t
        nlinarith
      · change v 2 = v 0 * t
        nlinarith
    have hv0 : v 0 ≠ 0 := by
      intro hzero
      have hvzero : v = 0 := by simpa only [hzero, zero_smul] using hrepr
      rw [hvzero, norm_zero] at hv
      norm_num at hv
    have hnormalize := congrArg NormedSpace.normalize hrepr
    rw [NormedSpace.normalize_eq_self_of_norm_eq_one hv] at hnormalize
    rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · rw [NormedSpace.normalize_smul_of_neg hneg] at hnormalize
      exact Or.inr hnormalize
    · rw [NormedSpace.normalize_smul_of_pos hpos] at hnormalize
      exact Or.inl hnormalize
  · intro heq
    have hrelation : ∀ j : Fin 2, symmetricFamilyLeadingDirection a b c j.succ =
        t * symmetricFamilyLeadingDirection a b c 0 := by
      intro j
      fin_cases j <;>
        simp only [symmetricFamilyLeadingDirection, NormedSpace.normalize,
          symmetricFamilyLeadingSeed, representationToEuclidean] <;>
        change ‖symmetricFamilyLeadingSeed a b c‖⁻¹ * t =
          t * (‖symmetricFamilyLeadingSeed a b c‖⁻¹ * 1) <;> ring
    have h1 : v 1 = t * v 0 := by
      rcases heq with rfl | rfl
      · exact hrelation 0
      · simpa only [PiLp.neg_apply, mul_neg] using congrArg Neg.neg (hrelation 0)
    have h2 : v 2 = t * v 0 := by
      rcases heq with rfl | rfl
      · exact hrelation 1
      · simpa only [PiLp.neg_apply, mul_neg] using congrArg Neg.neg (hrelation 1)
    have h := symmetricFamilyCovariance_completed_square a b c hb v
    change symmetricFamilyLeadingValue a b c * ‖v‖ ^ 2 -
      inner ℝ v (symmetricFamilyCovarianceAction a b c v) =
      (symmetricFamilyLeadingValue a b c - c) * ((v 1 - t * v 0) ^ 2 + (v 2 - t * v 0) ^ 2) at h
    rw [h1, h2, sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero, mul_zero, hv] at h
    nlinarith

/-- A single public summary: the actual matrix has exactly two leading
unit directions, with a canonical strictly positive child-symmetric choice. -/
theorem symmetricFamilyCovariance_unique_leading_direction (a b c : ℝ) (hb : 0 < b) :
    ‖symmetricFamilyLeadingDirection a b c‖ = 1 ∧
    (∀ j, 0 < symmetricFamilyLeadingDirection a b c j) ∧
    symmetricFamilyLeadingDirection a b c 1 = symmetricFamilyLeadingDirection a b c 2 ∧
    (∀ v : EuclideanRepresentation 3, ‖v‖ = 1 →
      inner ℝ v (symmetricFamilyCovarianceAction a b c v) ≤ symmetricFamilyLeadingValue a b c) ∧
    (∀ v : EuclideanRepresentation 3, ‖v‖ = 1 →
      (inner ℝ v (symmetricFamilyCovarianceAction a b c v) = symmetricFamilyLeadingValue a b c ↔
        v = symmetricFamilyLeadingDirection a b c ∨ v = -symmetricFamilyLeadingDirection a b c)) :=
  ⟨symmetricFamilyLeadingDirection_unit a b c, symmetricFamilyLeadingDirection_pos a b c hb,
    symmetricFamilyLeadingDirection_child_symmetry a b c,
    symmetricFamilyCovariance_rayleigh_le a b c hb, symmetricFamilyCovariance_rayleigh_eq_iff a b c hb⟩

end PKG26AtomicFeatures
