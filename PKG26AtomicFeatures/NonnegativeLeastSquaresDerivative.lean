import PKG26AtomicFeatures.NonnegativeLeastSquares
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Differentiating the actual nonnegative least-squares value

The supporting affine function at x has slope twice the residual. Actual
optimality and the cone variational inequality bound its approximation error
between zero and the squared input displacement, including at changes of
the active set. The derivative follows directly from this quadratic bound.
-/

namespace PKG26AtomicFeatures

open scoped InnerProductSpace Topology

/-- Squared residual of the actual canonical nonnegative least-squares code. -/
noncomputable def nonnegativeLeastSquaresValue {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) : ℝ :=
  ‖x - representationToEuclidean d
    (B.mulVec (nonnegativeLeastSquaresCode B γ hγ hlower x))‖ ^ 2

/-- A sharp quadratic bound for the value's affine approximation. It
requires only actual nonnegative least-squares optimality of the two codes. -/
theorem nonnegativeLeastSquares_value_affine_error_bounds
    {d M : ℕ} {B : Matrix (Fin d) (Fin M) ℝ}
    {x y : EuclideanRepresentation d} {u v : FeatureVector M}
    (hu : IsNonnegativeLeastSquaresCode B x u)
    (hv : IsNonnegativeLeastSquaresCode B y v) :
    let error := ‖y - representationToEuclidean d (B.mulVec v)‖ ^ 2 -
      ‖x - representationToEuclidean d (B.mulVec u)‖ ^ 2 -
      2 * inner ℝ (x - representationToEuclidean d (B.mulVec u)) (y - x)
    0 ≤ error ∧ error ≤ ‖y - x‖ ^ 2 := by
  dsimp only
  let r := x - representationToEuclidean d (B.mulVec u)
  let h := y - x
  let a := representationToEuclidean d (B.mulVec v) -
    representationToEuclidean d (B.mulVec u)
  have hvi : inner ℝ r a ≤ 0 := hu.inner_le_zero v hv.1
  have hdecomp : y - representationToEuclidean d (B.mulVec v) = r + (h - a) := by
    dsimp [r, h, a]
    abel
  have hupper := hv.2 u hu.1
  have hsame : y - representationToEuclidean d (B.mulVec u) = r + h := by
    dsimp [r, h]
    abel
  rw [hsame, norm_add_sq_real] at hupper
  have hlower := norm_add_sq_real r (h - a)
  rw [← hdecomp, inner_sub_right] at hlower
  change 0 ≤ ‖y - representationToEuclidean d (B.mulVec v)‖ ^ 2 - ‖r‖ ^ 2 -
      2 * inner ℝ r h ∧
    ‖y - representationToEuclidean d (B.mulVec v)‖ ^ 2 - ‖r‖ ^ 2 -
      2 * inner ℝ r h ≤ ‖h‖ ^ 2
  constructor
  · nlinarith [sq_nonneg ‖h - a‖]
  · linarith

/-- Squared nonnegative least-squares distance is differentiable even when
the set of positive optimal coordinates changes. -/
theorem hasFDerivAt_nonnegativeLeastSquaresValue {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) :
    HasFDerivAt (nonnegativeLeastSquaresValue B γ hγ hlower)
      ((2 : ℝ) • innerSL ℝ (x - representationToEuclidean d
        (B.mulVec (nonnegativeLeastSquaresCode B γ hγ hlower x)))) x := by
  rw [hasFDerivAt_iff_isLittleO]
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun y : EuclideanRepresentation d => ‖y - x‖ ^ 2)
  · apply Asymptotics.isBigO_of_le
    intro y
    have h := nonnegativeLeastSquares_value_affine_error_bounds
      (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower x)
      (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower y)
    change ‖nonnegativeLeastSquaresValue B γ hγ hlower y -
        nonnegativeLeastSquaresValue B γ hγ hlower x -
        2 * inner ℝ (x - representationToEuclidean d
          (B.mulVec (nonnegativeLeastSquaresCode B γ hγ hlower x))) (y - x)‖ ≤ ‖‖y - x‖ ^ 2‖
    dsimp only [nonnegativeLeastSquaresValue]
    rw [Real.norm_eq_abs, abs_of_nonneg h.1, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact h.2
  · exact Asymptotics.isLittleO_pow_sub_sub x (by norm_num)

end PKG26AtomicFeatures
