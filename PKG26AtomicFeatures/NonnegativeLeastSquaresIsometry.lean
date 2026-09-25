import PKG26AtomicFeatures.NonnegativeLeastSquaresDerivative

/-!
# Orthogonal changes of the learned dictionary

Applying one ambient linear isometry to every column preserves normalization,
sparse stability, and nonnegative codes. Its least-squares value at x is the
original value at the inverse image of x. This makes rotations legitimate
feasible variations, including dictionaries on the stability boundary.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators InnerProductSpace

/-- Apply one ambient orthogonal transformation to every actual column. -/
noncomputable def isometricDictionary {d m : ℕ}
    (Q : EuclideanRepresentation d ≃ₗᵢ[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) : Matrix (Fin d) (Fin m) ℝ :=
  fun i j => ((representationToEuclidean d).symm
    (Q (representationToEuclidean d (B.col j)))) i

@[simp] theorem isometricDictionary_column {d m : ℕ}
    (Q : EuclideanRepresentation d ≃ₗᵢ[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (j : Fin m) :
    representationToEuclidean d ((isometricDictionary Q B).col j) =
      Q (representationToEuclidean d (B.col j)) := by
  exact (representationToEuclidean d).apply_symm_apply _

theorem isometricDictionary_synthesis {d m : ℕ}
    (Q : EuclideanRepresentation d ≃ₗᵢ[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : FeatureVector m) :
    representationToEuclidean d ((isometricDictionary Q B).mulVec u) =
      Q (representationToEuclidean d (B.mulVec u)) := by
  rw [Matrix.mulVec_eq_sum, Matrix.mulVec_eq_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [op_smul_eq_smul, map_smul] using
    congrArg (fun v => u j • v) (isometricDictionary_column Q B j)

theorem HasUnitEuclideanColumns.isometricDictionary {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} (hB : HasUnitEuclideanColumns B)
    (Q : EuclideanRepresentation d ≃ₗᵢ[ℝ] EuclideanRepresentation d) :
    HasUnitEuclideanColumns (isometricDictionary Q B) := by
  intro j
  rw [isometricDictionary_column, Q.norm_map]
  exact hB j

theorem SparseLowerStable.isometricDictionary {d m s : ℕ} {γ : ℝ}
    {B : Matrix (Fin d) (Fin m) ℝ} (hB : SparseLowerStable B γ s)
    (Q : EuclideanRepresentation d ≃ₗᵢ[ℝ] EuclideanRepresentation d) :
    SparseLowerStable (isometricDictionary Q B) γ s := by
  intro u hu
  rw [isometricDictionary_synthesis, Q.norm_map]
  exact hB u hu

theorem isometricDictionary_residual_norm {d m : ℕ}
    (Q : EuclideanRepresentation d ≃ₗᵢ[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (x : EuclideanRepresentation d) (u : FeatureVector m) :
    ‖x - representationToEuclidean d ((isometricDictionary Q B).mulVec u)‖ =
      ‖Q.symm x - representationToEuclidean d (B.mulVec u)‖ := by
  rw [isometricDictionary_synthesis, ← Q.apply_symm_apply x, ← map_sub, Q.norm_map]
  simp only [Q.symm_apply_apply]

/-- Isometry preserves the complete actual nonnegative optimization problem. -/
theorem isNonnegativeLeastSquaresCode_isometricDictionary_iff {d m : ℕ}
    (Q : EuclideanRepresentation d ≃ₗᵢ[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (x : EuclideanRepresentation d) (u : FeatureVector m) :
    IsNonnegativeLeastSquaresCode (isometricDictionary Q B) x u ↔
      IsNonnegativeLeastSquaresCode B (Q.symm x) u := by
  simp only [IsNonnegativeLeastSquaresCode, isometricDictionary_residual_norm]

/-- The exact value identity allows a moving dictionary to be analyzed
by differentiating the input to a fixed nonnegative cone. -/
theorem nonnegativeLeastSquaresValue_isometricDictionary {d m : ℕ}
    (Q : EuclideanRepresentation d ≃ₗᵢ[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (hrotated : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d ((isometricDictionary Q B).mulVec u)‖)
    (x : EuclideanRepresentation d) :
    nonnegativeLeastSquaresValue (isometricDictionary Q B) γ hγ hrotated x =
      nonnegativeLeastSquaresValue B γ hγ hlower (Q.symm x) := by
  have hu := (isNonnegativeLeastSquaresCode_isometricDictionary_iff Q B x
    (nonnegativeLeastSquaresCode (isometricDictionary Q B) γ hγ hrotated x)).mp
      (nonnegativeLeastSquaresCode_isMinimizer _ γ hγ hrotated x)
  have heq := hu.eq_nonnegativeLeastSquaresCode hγ hlower
  rw [nonnegativeLeastSquaresValue, heq, isometricDictionary_residual_norm]
  rfl

end PKG26AtomicFeatures
