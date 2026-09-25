import PKG26AtomicFeatures.SparseStability
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Stability after removing a selected atom

The sparse-incidence argument removes one learned coordinate and projects
perpendicular to its column. A lower bound at order `2k` then gives the same
margin at order `2(k-1)` for the remaining columns. These lemmas make that
dimension-reduction step explicit; a projected zero column is excluded from
the admissible coordinate set, not treated as a stable dictionary column.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- Sparse lower stability restricted to an explicitly permitted set of
coordinates. Used internally when the incidence induction removes atoms. -/
def SparseLowerStableOn {d M : ℕ} (B : Matrix (Fin d) (Fin M) ℝ)
    (γ : ℝ) (s : ℕ) (allowed : Finset (Fin M)) : Prop :=
  ∀ v : FeatureVector M, nonzeroSupport v ⊆ allowed →
    (nonzeroSupport v).card ≤ s →
    γ * ‖representationToEuclidean M v‖ ≤
      ‖representationToEuclidean d (B.mulVec v)‖

theorem SparseLowerStable.on {d M s : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable B γ s) (allowed : Finset (Fin M)) :
    SparseLowerStableOn B γ s allowed :=
  fun v _ hv => h v hv

/-- Apply a Euclidean linear operator to every dictionary column. -/
noncomputable def postcomposeEuclideanDictionary {d M : ℕ}
    (Q : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) : Matrix (Fin d) (Fin M) ℝ :=
  LinearMap.toMatrix' ((representationToEuclidean d).symm.toLinearMap.comp
    (Q.toLinearMap.comp ((representationToEuclidean d).toLinearMap.comp B.mulVecLin)))

theorem postcomposeEuclideanDictionary_mulVec {d M : ℕ}
    (Q : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (v : FeatureVector M) :
    representationToEuclidean d ((postcomposeEuclideanDictionary Q B).mulVec v) =
      Q (representationToEuclidean d (B.mulVec v)) := by
  simp [postcomposeEuclideanDictionary, LinearMap.toMatrix'_mulVec]

theorem postcomposeEuclideanDictionary_col {d M : ℕ}
    (Q : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (j : Fin M) :
    representationToEuclidean d ((postcomposeEuclideanDictionary Q B).col j) =
      Q (representationToEuclidean d (B.col j)) := by
  simpa only [Matrix.mulVec_single_one] using
    postcomposeEuclideanDictionary_mulVec Q B (Pi.single j 1)

/-- Altering a zero coordinate can only increase Euclidean norm. -/
theorem euclidean_norm_le_sub_single_of_zero {M : ℕ}
    (v : FeatureVector M) (i : Fin M) (t : ℝ) (hi : v i = 0) :
    ‖representationToEuclidean M v‖ ≤
      ‖representationToEuclidean M (v - t • (Pi.single i 1 : FeatureVector M))‖ := by
  have hsq : ‖representationToEuclidean M v‖ ^ 2 ≤
      ‖representationToEuclidean M (v - t • (Pi.single i 1 : FeatureVector M))‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change (v j) ^ 2 ≤ (v j - t * ((Pi.single i 1 : FeatureVector M) j)) ^ 2
    by_cases hji : j = i
    · subst j
      simpa [hi] using sq_nonneg t
    · simp [Pi.single_eq_of_ne hji]
  have hleft := norm_nonneg (representationToEuclidean M v)
  have hright := norm_nonneg (representationToEuclidean M (v - t • (Pi.single i 1 : FeatureVector M)))
  nlinarith

/-- Removing one atom and projecting to its perpendicular space preserves
the lower margin. The original bound is needed only on the allowed columns,
and the resulting tested order is `2k-2`. -/
theorem SparseLowerStableOn.project_erase {d M k : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ} {allowed : Finset (Fin M)}
    (h : SparseLowerStableOn B γ (2 * k) allowed)
    (hγ : 0 ≤ γ) (hk : 0 < k) (i : Fin M) (hi : i ∈ allowed) :
    SparseLowerStableOn
      (postcomposeEuclideanDictionary
        (ℝ ∙ representationToEuclidean d (B.col i))ᗮ.starProjection B)
      γ (2 * (k - 1)) (allowed.erase i) := by
  classical
  intro v hv hcard
  have hvi : v i = 0 := by
    by_contra hn
    have := hv ((mem_nonzeroSupport_iff v i).mpr hn)
    simpa using this
  let W : Submodule ℝ (EuclideanRepresentation d) :=
    ℝ ∙ representationToEuclidean d (B.col i)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (W.starProjection_apply_mem (representationToEuclidean d (B.mulVec v)))
  let w : FeatureVector M := v - t • (Pi.single i 1 : FeatureVector M)
  have hwsub : nonzeroSupport w ⊆ insert i (nonzeroSupport v) := by
    intro j hj
    by_cases hji : j = i
    · exact Finset.mem_insert.mpr (Or.inl hji)
    · apply Finset.mem_insert_of_mem
      apply (mem_nonzeroSupport_iff v j).mpr
      have hne := (mem_nonzeroSupport_iff w j).mp hj
      simpa [w, Pi.single_eq_of_ne hji] using hne
  have hwallowed : nonzeroSupport w ⊆ allowed :=
    hwsub.trans (Finset.insert_subset hi (hv.trans (Finset.erase_subset _ _)))
  have hwcard : (nonzeroSupport w).card ≤ 2 * k := by
    have hle := (Finset.card_le_card hwsub).trans (Finset.card_insert_le i _)
    omega
  have hnorm := euclidean_norm_le_sub_single_of_zero v i t hvi
  have hbound := (mul_le_mul_of_nonneg_left hnorm hγ).trans (h w hwallowed hwcard)
  have heq : representationToEuclidean d (B.mulVec w) =
      Wᗮ.starProjection (representationToEuclidean d (B.mulVec v)) := by
    rw [Submodule.starProjection_orthogonal_val]
    rw [← ht]
    simp [w, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [heq] at hbound
  simpa only [postcomposeEuclideanDictionary_mulVec] using hbound

/-- Orthogonal projection preserves the unit upper bound on learned columns. -/
theorem projected_dictionary_column_norm_le {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ)
    (W : Submodule ℝ (EuclideanRepresentation d))
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1) (j : Fin M) :
    ‖representationToEuclidean d
      ((postcomposeEuclideanDictionary W.starProjection B).col j)‖ ≤ 1 := by
  rw [postcomposeEuclideanDictionary_col]
  exact (W.norm_starProjection_apply_le _).trans (hunit j)

end PKG26AtomicFeatures
