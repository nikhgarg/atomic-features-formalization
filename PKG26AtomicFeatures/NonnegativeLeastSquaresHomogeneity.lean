import PKG26AtomicFeatures.NonnegativeLeastSquaresActiveSet
import PKG26AtomicFeatures.NonnegativeLeastSquaresDerivative

/-!
# Positive homogeneity of actual nonnegative least squares

Common nonnegative scaling preserves the KKT conditions, so both the unique
code and its squared residual scale exactly. The dictionary and its column
normalization remain fixed.
-/

namespace PKG26AtomicFeatures

theorem nnlsResidualColumnInner_smul {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (x : EuclideanRepresentation d)
    (u : FeatureVector m) (s : ℝ) (j : Fin m) :
    nnlsResidualColumnInner B (s • x) (s • u) j =
      s * nnlsResidualColumnInner B x u j := by
  simp only [nnlsResidualColumnInner, Matrix.mulVec_smul, map_smul,
    ← smul_sub, real_inner_smul_left]

/-- Every actual optimal nonnegative code scales to an optimal code, even
when the dictionary is rank deficient and the minimizer is nonunique. -/
theorem IsNonnegativeLeastSquaresCode.smul {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {x : EuclideanRepresentation d}
    {u : FeatureVector m} (hu : IsNonnegativeLeastSquaresCode B x u)
    (s : ℝ) (hs : 0 ≤ s) : IsNonnegativeLeastSquaresCode B (s • x) (s • u) := by
  apply (isNonnegativeLeastSquaresCode_iff_kkt B _ _).mpr
  refine ⟨fun j => mul_nonneg hs (hu.1 j), ?_, ?_⟩
  · intro j
    rw [nnlsResidualColumnInner_smul]
    exact mul_nonpos_of_nonneg_of_nonpos hs (hu.columnResidual_nonpos j)
  · intro j
    rw [nnlsResidualColumnInner_smul]
    change (s * u j) * (s * nnlsResidualColumnInner B x u j) = 0
    calc
      _ = s ^ 2 * (u j * nnlsResidualColumnInner B x u j) := by ring
      _ = 0 := by rw [hu.coordinate_complementarity, mul_zero]

theorem nonnegativeLeastSquaresCode_smul {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) (s : ℝ) (hs : 0 ≤ s) :
    nonnegativeLeastSquaresCode B γ hγ hlower (s • x) =
      s • nonnegativeLeastSquaresCode B γ hγ hlower x := by
  exact ((nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower x).smul s hs
    |>.eq_nonnegativeLeastSquaresCode hγ hlower).symm

theorem nonnegativeLeastSquaresValue_smul {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) (s : ℝ) (hs : 0 ≤ s) :
    nonnegativeLeastSquaresValue B γ hγ hlower (s • x) =
      s ^ 2 * nonnegativeLeastSquaresValue B γ hγ hlower x := by
  simp only [nonnegativeLeastSquaresValue, nonnegativeLeastSquaresCode_smul B γ hγ hlower x s hs,
    Matrix.mulVec_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs, mul_pow]

end PKG26AtomicFeatures
