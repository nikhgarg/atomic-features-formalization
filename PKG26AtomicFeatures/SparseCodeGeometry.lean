import PKG26AtomicFeatures.ProjectedSparseStability

/-!
# Local geometry of stable sparse codes

Unit upper bounds on columns force a code reconstructing a unit vector to
have a substantial coordinate. Sparse stability then prevents that coordinate
from disappearing in nearby approximate reconstructions. These are the local
steps in the width-independent sparse-incidence argument.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- Dictionary synthesis in the Euclidean copy of the representation space. -/
theorem euclidean_mulVec_eq_sum {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (u : FeatureVector M) :
    representationToEuclidean d (B.mulVec u) =
      ∑ j, u j • representationToEuclidean d (B.col j) := by
  rw [Matrix.mulVec_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [op_smul_eq_smul, map_smul]
  rfl

/-- The `ℓ¹` coefficient norm bounds synthesis when every column has norm
at most one. The sum runs only over the actual nonzero support. -/
theorem euclidean_mulVec_norm_le_sum_abs {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ)
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (u : FeatureVector M) :
    ‖representationToEuclidean d (B.mulVec u)‖ ≤
      ∑ j ∈ nonzeroSupport u, |u j| := by
  classical
  rw [euclidean_mulVec_eq_sum]
  calc
    _ ≤ ∑ j, ‖u j • representationToEuclidean d (B.col j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, |u j| := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_smul, Real.norm_eq_abs, mul_one] using
        mul_le_mul_of_nonneg_left (hunit j) (abs_nonneg (u j))
    _ = ∑ j ∈ nonzeroSupport u, |u j| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hz : u j = 0 := by simpa only [mem_nonzeroSupport_iff, not_not] using hj
      simp [hz]

/-- Reconstructing a unit vector with error at most `1/4` forces some active
coefficient to have magnitude at least `1/(2K)`. -/
theorem exists_large_sparse_coordinate {d M K : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ)
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (u : FeatureVector M) (x : EuclideanRepresentation d)
    (hK : 0 < K) (hu : (nonzeroSupport u).card ≤ K)
    (hx : ‖x‖ = 1)
    (herr : ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ 1/4) :
    ∃ i ∈ nonzeroSupport u, 1 / (2 * (K : ℝ)) ≤ |u i| := by
  classical
  by_contra hn
  have hsmall : ∀ i ∈ nonzeroSupport u, |u i| ≤ 1 / (2 * (K : ℝ)) := by
    intro i hi
    exact (lt_of_not_ge (fun h => hn ⟨i, hi, h⟩)).le
  have hpos : 0 < (K : ℝ) := by exact_mod_cast hK
  have hsum : (∑ i ∈ nonzeroSupport u, |u i|) ≤ 1/2 := by
    calc
      _ ≤ ∑ _i ∈ nonzeroSupport u, 1 / (2 * (K : ℝ)) :=
        Finset.sum_le_sum hsmall
      _ = (nonzeroSupport u).card * (1 / (2 * (K : ℝ))) := by simp
      _ ≤ (K : ℝ) * (1 / (2 * (K : ℝ))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hu) (by positivity)
      _ = 1/2 := by field_simp
  have hsynthesis := (euclidean_mulVec_norm_le_sum_abs B hunit u).trans hsum
  have htriangle := norm_add_le (x - representationToEuclidean d (B.mulVec u))
    (representationToEuclidean d (B.mulVec u))
  rw [sub_add_cancel, hx] at htriangle
  linarith

/-- A restricted dictionary has the same inverse estimate on any two
admissible sparse codes. -/
theorem SparseLowerStableOn.code_distance {d M k : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ} {allowed : Finset (Fin M)}
    (h : SparseLowerStableOn B γ (2 * k) allowed)
    (u v : FeatureVector M)
    (hu : nonzeroSupport u ⊆ allowed) (hv : nonzeroSupport v ⊆ allowed)
    (hucard : (nonzeroSupport u).card ≤ k)
    (hvcard : (nonzeroSupport v).card ≤ k) :
    γ * ‖representationToEuclidean M (u - v)‖ ≤
      ‖representationToEuclidean d (B.mulVec u - B.mulVec v)‖ := by
  have hsub := nonzeroSupport_sub_subset u v
  have hallowed := hsub.trans (Finset.union_subset hu hv)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [Matrix.mulVec_sub] using h (u - v) hallowed (by omega)

/-- Nearby approximate reconstructions have nearby sparse codes. This
three-term estimate keeps approximation error separate from input distance. -/
theorem SparseLowerStableOn.code_distance_le_three_errors {d M k : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ} {allowed : Finset (Fin M)}
    (h : SparseLowerStableOn B γ (2 * k) allowed)
    (u v : FeatureVector M) (x y : EuclideanRepresentation d)
    (hu : nonzeroSupport u ⊆ allowed) (hv : nonzeroSupport v ⊆ allowed)
    (hucard : (nonzeroSupport u).card ≤ k)
    (hvcard : (nonzeroSupport v).card ≤ k) :
    γ * ‖representationToEuclidean M (u - v)‖ ≤
      ‖representationToEuclidean d (B.mulVec u) - x‖ + ‖x - y‖ +
        ‖y - representationToEuclidean d (B.mulVec v)‖ := by
  have hfirst := h.code_distance u v hu hv hucard hvcard
  refine hfirst.trans ?_
  simp only [map_sub]
  calc
    _ = ‖(representationToEuclidean d (B.mulVec u) - x) + (x - y) +
        (y - representationToEuclidean d (B.mulVec v))‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- Euclidean coefficient distance controls every coordinate difference. -/
theorem abs_coordinate_sub_le_euclidean_norm {M : ℕ}
    (u v : FeatureVector M) (i : Fin M) :
    |u i - v i| ≤ ‖representationToEuclidean M (u - v)‖ := by
  simpa only [Real.norm_eq_abs] using
    PiLp.norm_apply_le (representationToEuclidean M (u - v)) i

end PKG26AtomicFeatures
