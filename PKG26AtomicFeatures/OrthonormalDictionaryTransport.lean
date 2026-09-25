import PKG26AtomicFeatures.AmbientDictionaryCompression
import PKG26AtomicFeatures.NonnegativeLeastSquaresPopulation

/-!
# Dictionary transport through an orthonormal source

An actual matrix with orthonormal Euclidean columns gives an isometric
synthesis map. Its transpose recovers source coordinates. Dictionaries
inside its range can therefore be coordinatized without changing any
synthesis norm, unit normalization, sparse lower stability, or residual loss.
-/

namespace PKG26AtomicFeatures

open Module MeasureTheory
open scoped BigOperators Matrix

/-- Orthonormal matrix synthesis, bundled as a genuine Euclidean isometry. -/
noncomputable def orthonormalDictionaryIsometry {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j))) :
    EuclideanRepresentation M →ₗᵢ[ℝ] EuclideanRepresentation d := by
  let L := Matrix.toEuclideanLin A
  have heq : L ∘ (EuclideanSpace.basisFun (Fin M) ℝ).toBasis =
      fun j => representationToEuclidean d (A.col j) := by
    funext j
    ext i
    simp [L, Matrix.toEuclideanLin_apply, EuclideanSpace.basisFun_apply, Matrix.mulVec_single,
      representationToEuclidean, Matrix.col]
  exact L.isometryOfOrthonormal (v := (EuclideanSpace.basisFun (Fin M) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin M) ℝ).orthonormal (heq ▸ hA)

@[simp] theorem orthonormalDictionaryIsometry_apply {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (v : FeatureVector M) :
    orthonormalDictionaryIsometry A hA (representationToEuclidean M v) =
      representationToEuclidean d (A.mulVec v) := rfl

theorem orthonormalDictionary_synthesis_norm {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (v : FeatureVector M) :
    ‖representationToEuclidean d (A.mulVec v)‖ = ‖representationToEuclidean M v‖ :=
  (orthonormalDictionaryIsometry A hA).norm_map (representationToEuclidean M v)

/-- The actual transpose computes the source coordinate inner products. -/
theorem transpose_mulVec_eq_column_inner {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (x : FeatureVector d) (j : Fin M) :
    A.transpose.mulVec x j =
      inner ℝ (representationToEuclidean d (A.col j)) (representationToEuclidean d x) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change A i j * x i = x i * A i j
  ring

/-- Transpose synthesis is a left inverse for actual orthonormal columns. -/
theorem orthonormalDictionary_transpose_left_inverse {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (v : FeatureVector M) : A.transpose.mulVec (A.mulVec v) = v := by
  ext j
  rw [transpose_mulVec_eq_column_inner, euclidean_mulVec_eq_sum]
  simpa only [real_inner_smul_right, mul_comm] using hA.inner_right_fintype v j

/-- An orthonormal source's column space has its full source dimension. -/
theorem orthonormalDictionary_range_finrank {d M : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j))) :
    finrank ℝ (LinearMap.range (Matrix.toEuclideanLin A)) = M := by
  have h := LinearMap.finrank_range_of_inj (orthonormalDictionaryIsometry A hA).injective
  simpa using h

/-- Matrix multiplication by the source lifts every coefficient-space
synthesis isometrically into the ambient representation. -/
theorem orthonormalDictionary_lift_synthesis_norm {d M m : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (C : Matrix (Fin M) (Fin m) ℝ) (v : FeatureVector m) :
    ‖representationToEuclidean d ((A * C).mulVec v)‖ = ‖representationToEuclidean M (C.mulVec v)‖ := by
  rw [← Matrix.mulVec_mulVec]
  exact orthonormalDictionary_synthesis_norm A hA _

theorem orthonormalDictionary_lift_unit_iff {d M m : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (C : Matrix (Fin M) (Fin m) ℝ) :
    HasUnitEuclideanColumns (A * C) ↔ HasUnitEuclideanColumns C := by
  have hcol (j) : (A * C).col j = A.mulVec (C.col j) := by
    ext i
    rfl
  simp only [HasUnitEuclideanColumns, hcol, orthonormalDictionary_synthesis_norm A hA]

theorem orthonormalDictionary_lift_stable_iff {d M m s : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (C : Matrix (Fin M) (Fin m) ℝ) (γ : ℝ) :
    SparseLowerStable (A * C) γ s ↔ SparseLowerStable C γ s := by
  simp only [SparseLowerStable, orthonormalDictionary_lift_synthesis_norm A hA]

/-- Dictionaries lying in the actual source range equal the lift of their
transpose coordinates. -/
theorem orthonormalDictionary_lift_transpose_eq {d M m : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (B : Matrix (Fin d) (Fin m) ℝ)
    (hB : ∀ j, representationToEuclidean d (B.col j) ∈ LinearMap.range (Matrix.toEuclideanLin A)) :
    A * (A.transpose * B) = B := by
  have hcol (j) : A.mulVec (A.transpose.mulVec (B.col j)) = B.col j := by
    obtain ⟨q, hq⟩ := hB j
    have hq' : A.mulVec (fun i => q i) = B.col j := by
      exact (representationToEuclidean d).injective hq
    rw [← hq', orthonormalDictionary_transpose_left_inverse A hA]
  ext i j
  exact congrArg (fun v : FeatureVector d => v i) (hcol j)

/-- The true residual norm is preserved by lifting a coefficient-space dictionary. -/
theorem orthonormalDictionary_residual_norm {d M m : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (C : Matrix (Fin M) (Fin m) ℝ) (z : FeatureVector M) (u : FeatureVector m) :
    ‖representationToEuclidean d (A.mulVec z) - representationToEuclidean d ((A * C).mulVec u)‖ =
      ‖representationToEuclidean M z - representationToEuclidean M (C.mulVec u)‖ := by
  rw [← Matrix.mulVec_mulVec, ← map_sub, ← Matrix.mulVec_sub,
    orthonormalDictionary_synthesis_norm A hA, map_sub]

/-- Lifting preserves the actual nonnegative expected squared loss for
arbitrary source and code maps, including infinite loss. -/
theorem orthonormalDictionary_actual_loss_lift
    {Ω : Type*} [MeasurableSpace Ω] {d M m : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : Ω → FeatureVector M) (C : Matrix (Fin M) (Fin m) ℝ) (u : Ω → FeatureVector m) :
    actualPopulationSquaredLoss μ A z (A * C) u =
      actualPopulationSquaredLoss μ (1 : Matrix (Fin M) (Fin M) ℝ) z C u := by
  unfold actualPopulationSquaredLoss
  simp_rw [orthonormalDictionary_residual_norm A hA, Matrix.one_mulVec]

end PKG26AtomicFeatures
