import PKG26AtomicFeatures.PopulationRecovery

/-!
# Quantitative sparse stability

Source: `sections/theory.tex`, line 3, Overleaf snapshot of September 18, 2026.
Both norms below are Euclidean norms, including the coefficient norm.
An order larger than the number of columns means all coefficient vectors.
No column normalization is part of stability itself.
-/

namespace PKG26AtomicFeatures

/-- The paper's lower singular-value condition on all `s`-sparse vectors. -/
def SparseLowerStable {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (γ : ℝ) (s : ℕ) : Prop :=
  ∀ v : FeatureVector M, (nonzeroSupport v).card ≤ s →
    γ * ‖representationToEuclidean M v‖ ≤
      ‖representationToEuclidean d (matrix.mulVec v)‖

/-- Lowering the tested sparsity order preserves stability. -/
theorem SparseLowerStable.mono {d M s t : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable matrix γ s) (ht : t ≤ s) :
    SparseLowerStable matrix γ t :=
  fun v hv => h v (hv.trans ht)

/-- A positive stability margin excludes nonzero sparse kernel vectors. -/
theorem SparseLowerStable.kernel_eq_zero {d M s : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable matrix γ s) (hγ : 0 < γ)
    (v : FeatureVector M) (hv : (nonzeroSupport v).card ≤ s)
    (hzero : matrix.mulVec v = 0) : v = 0 := by
  have hbound := h v hv
  rw [hzero, map_zero, norm_zero] at hbound
  have hn : ‖representationToEuclidean M v‖ = 0 := by
    have := norm_nonneg (representationToEuclidean M v)
    nlinarith
  exact (representationToEuclidean M).injective (by simpa using norm_eq_zero.mp hn)

/-- Stability implies independence of every tested column set. -/
theorem SparseLowerStable.linearIndependent {d M s : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable matrix γ s) (hγ : 0 < γ)
    (coordinates : Finset (Fin M)) (hcard : coordinates.card ≤ s) :
    LinearIndependent ℝ (selectedColumns matrix coordinates) := by
  by_contra hdep
  obtain ⟨v, hv, hne, hzero⟩ :=
    exists_nonzero_kernel_code_of_dependent matrix coordinates hdep
  exact hne (h.kernel_eq_zero hγ v ((Finset.card_le_card hv).trans hcard) hzero)

/-- The finite-width spark cutoff retains globally injective dictionaries
even when the requested stability order exceeds their width. -/
theorem SparseLowerStable.min_lt_spark {d M s : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable matrix γ s) (hγ : 0 < γ) :
    min s M < spark matrix := by
  by_contra hn
  have hs : spark matrix ≤ min s M := Nat.le_of_not_gt hn
  obtain ⟨coordinates, hcard, hdep⟩ :=
    exists_dependent_card_eq_spark matrix (hs.trans (Nat.min_le_right _ _))
  exact hdep (h.linearIndependent hγ coordinates (by omega))

/-- Quantitative stability supplies uniqueness of sparse codes. -/
theorem SparseLowerStable.sparseInjective {d M K : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable matrix γ (2 * K)) (hγ : 0 < γ) :
    KSparseInjective matrix K :=
  (kSparseInjective_iff_min_lt_spark matrix).mpr (h.min_lt_spark hγ)

/-- Two `K`-sparse codes differ on at most `2K` coordinates. Thus the
paper's stability condition bounds their coefficient distance by their
reconstruction distance. -/
theorem SparseLowerStable.code_distance {d M K : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable matrix γ (2 * K))
    (u v : FeatureVector M)
    (hu : (nonzeroSupport u).card ≤ K) (hv : (nonzeroSupport v).card ≤ K) :
    γ * ‖representationToEuclidean M (u - v)‖ ≤
      ‖representationToEuclidean d (matrix.mulVec u - matrix.mulVec v)‖ := by
  have hcard := Finset.card_le_card (nonzeroSupport_sub_subset u v)
  have hunion := Finset.card_union_le (nonzeroSupport u) (nonzeroSupport v)
  simpa only [Matrix.mulVec_sub] using h (u - v) (by omega)

/-- Code errors are bounded by the two reconstruction errors relative to
one common target. This applies to an actual encoder and a selected linear
support encoder without assuming either encoder is optimal. -/
theorem SparseLowerStable.code_distance_le_residuals {d M K : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable matrix γ (2 * K))
    (u v : FeatureVector M) (x : RepresentationVector d)
    (hu : (nonzeroSupport u).card ≤ K) (hv : (nonzeroSupport v).card ≤ K) :
    γ * ‖representationToEuclidean M (u - v)‖ ≤
      ‖representationToEuclidean d (matrix.mulVec u - x)‖ +
        ‖representationToEuclidean d (x - matrix.mulVec v)‖ := by
  calc
    _ ≤ ‖representationToEuclidean d (matrix.mulVec u - matrix.mulVec v)‖ :=
      h.code_distance u v hu hv
    _ ≤ _ := by
      simp only [map_sub]
      convert norm_add_le
        (representationToEuclidean d (matrix.mulVec u) - representationToEuclidean d x)
        (representationToEuclidean d x - representationToEuclidean d (matrix.mulVec v)) using 1
      congr 1
      abel

/-- Squared form of the inverse estimate used before taking expectations
in the positive-loss recovery argument. -/
theorem SparseLowerStable.sq_code_distance_le_residuals {d M K : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (h : SparseLowerStable matrix γ (2 * K)) (hγ : 0 ≤ γ)
    (u v : FeatureVector M) (x : RepresentationVector d)
    (hu : (nonzeroSupport u).card ≤ K) (hv : (nonzeroSupport v).card ≤ K) :
    γ ^ 2 * ‖representationToEuclidean M (u - v)‖ ^ 2 ≤
      2 * (‖representationToEuclidean d (matrix.mulVec u - x)‖ ^ 2 +
        ‖representationToEuclidean d (x - matrix.mulVec v)‖ ^ 2) := by
  have hbound := h.code_distance_le_residuals u v x hu hv
  have hsq := (sq_le_sq₀ (mul_nonneg hγ (norm_nonneg _))
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hbound
  nlinarith [sq_nonneg (‖representationToEuclidean d (matrix.mulVec u - x)‖ -
    ‖representationToEuclidean d (x - matrix.mulVec v)‖)]

end PKG26AtomicFeatures
