import PKG26AtomicFeatures.NonnegativeLeastSquaresContinuity
import PKG26AtomicFeatures.NonnegativeLeastSquaresDerivative

/-!
# Uniform changes in nonnegative least-squares risk

Moving an input changes its distance to the learned cone by at most the
input displacement. Squared losses therefore differ by at most the
displacement times the sum of input norms, uniformly over dictionaries.
These bounds control the rare-point and cube-mixture perturbations in the
mesoscale construction without any optimizer-continuity assumption.
-/

namespace PKG26AtomicFeatures

/-- Actual optimal residual norms are one-Lipschitz in the input, with
no dependence on a dictionary's singular margin. -/
theorem IsNonnegativeLeastSquaresCode.abs_residual_norm_sub_le
    {d m : ℕ} {B : Matrix (Fin d) (Fin m) ℝ}
    {x y : EuclideanRepresentation d} {u v : FeatureVector m}
    (hu : IsNonnegativeLeastSquaresCode B x u)
    (hv : IsNonnegativeLeastSquaresCode B y v) :
    |‖x - representationToEuclidean d (B.mulVec u)‖ -
      ‖y - representationToEuclidean d (B.mulVec v)‖| ≤ ‖x - y‖ := by
  have hxu := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hu.2 v hv.1)
  have hyv := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hv.2 u hu.1)
  have hxtri : ‖x - representationToEuclidean d (B.mulVec v)‖ ≤
      ‖x - y‖ + ‖y - representationToEuclidean d (B.mulVec v)‖ := by
    convert norm_add_le (x - y) (y - representationToEuclidean d (B.mulVec v)) using 1 <;> abel
  have hytri : ‖y - representationToEuclidean d (B.mulVec u)‖ ≤
      ‖x - y‖ + ‖x - representationToEuclidean d (B.mulVec u)‖ := by
    calc
      _ ≤ ‖y - x‖ + ‖x - representationToEuclidean d (B.mulVec u)‖ := by
        convert norm_add_le (y - x) (x - representationToEuclidean d (B.mulVec u)) using 1 <;> abel
      _ = _ := by rw [norm_sub_rev y x]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Squared residual perturbations are uniformly bounded by the actual
input norms, even when the optimal code support changes. -/
theorem IsNonnegativeLeastSquaresCode.abs_squared_residual_sub_le
    {d m : ℕ} {B : Matrix (Fin d) (Fin m) ℝ}
    {x y : EuclideanRepresentation d} {u v : FeatureVector m}
    (hu : IsNonnegativeLeastSquaresCode B x u)
    (hv : IsNonnegativeLeastSquaresCode B y v) :
    |‖x - representationToEuclidean d (B.mulVec u)‖ ^ 2 -
      ‖y - representationToEuclidean d (B.mulVec v)‖ ^ 2| ≤
      ‖x - y‖ * (‖x‖ + ‖y‖) := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [mul_comm]
  exact mul_le_mul (hu.abs_residual_norm_sub_le hv)
    (add_le_add hu.residual_norm_le hv.residual_norm_le)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

/-- The canonical value has the same uniform perturbation bound. -/
theorem nonnegativeLeastSquaresValue_abs_sub_le {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x y : EuclideanRepresentation d) :
    |nonnegativeLeastSquaresValue B γ hγ hlower x -
      nonnegativeLeastSquaresValue B γ hγ hlower y| ≤ ‖x - y‖ * (‖x‖ + ‖y‖) :=
  (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower x).abs_squared_residual_sub_le
    (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower y)

/-- Perturbing a reference input by a vector of norm at most e changes
its squared loss by at most e(2R+e), uniformly over feasible dictionaries. -/
theorem nonnegativeLeastSquaresValue_perturbation_bound {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x e : EuclideanRepresentation d) (R δ : ℝ) (hx : ‖x‖ ≤ R) (he : ‖e‖ ≤ δ) :
    |nonnegativeLeastSquaresValue B γ hγ hlower (x + e) -
      nonnegativeLeastSquaresValue B γ hγ hlower x| ≤ δ * (2 * R + δ) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  have hδ : 0 ≤ δ := (norm_nonneg _).trans he
  have h := nonnegativeLeastSquaresValue_abs_sub_le B γ hγ hlower (x + e) x
  rw [add_sub_cancel_left] at h
  apply h.trans
  apply mul_le_mul he
  · have hnorm := norm_add_le x e
    linarith
  · positivity
  · exact hδ

end PKG26AtomicFeatures
