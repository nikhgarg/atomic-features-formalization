import PKG26AtomicFeatures.EligibleSupportGeometry
import PKG26AtomicFeatures.LocalMatchedCoefficientEstimates

/-!
# Pointwise recovery on eligible supports

The signed projection code and the source-coordinate functional are
constructed from the dictionaries and their selected supports. Their local
estimates give orientation and coefficient-recovery bounds for the actual
sparse code. The residual in every conclusion is the actual reconstruction
residual; no auxiliary functional or projected code is a premise.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- A unit-upper dictionary synthesizes a supported cube vector with norm
at most the support-cardinality bound. -/
theorem source_synthesis_norm_le_of_cube_support {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (S : Finset (Fin M))
    (hunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hS : S.card ≤ K) (z : FeatureVector M)
    (hcube : ∀ j, 0 ≤ z j ∧ z j ≤ 1) (hz : nonzeroSupport z ⊆ S) :
    ‖representationToEuclidean d (A.mulVec z)‖ ≤ (K : ℝ) := by
  calc
    _ ≤ ∑ j ∈ nonzeroSupport z, |z j| := euclidean_mulVec_norm_le_sum_abs A hunit z
    _ ≤ ∑ _j ∈ nonzeroSupport z, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_of_nonneg (hcube j).1] using (hcube j).2
    _ = ((nonzeroSupport z).card : ℝ) := by simp
    _ ≤ (K : ℝ) := by exact_mod_cast (Finset.card_le_card hz).trans hS

/-- Orthogonal projection onto a stable learned support has an actual
signed code. Cube bounds and the projector gap control both its norm and
its distance from every actual sparse code. -/
theorem exists_supported_projection_code_of_cube_source {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (S : Finset (Fin M)) (T : Finset (Fin m)) (γ δ : ℝ)
    (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBstable : SparseLowerStable B γ (2 * K))
    (hS : S.card ≤ K) (hT : T.card ≤ K)
    (hgap : ‖(euclideanColumnSpan A S).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ)
    (z : FeatureVector M) (hcube : ∀ j, 0 ≤ z j ∧ z j ≤ 1)
    (hz : nonzeroSupport z ⊆ S) :
    ∃ v : FeatureVector m, nonzeroSupport v ⊆ T ∧
      representationToEuclidean d (B.mulVec v) =
        (euclideanColumnSpan B T).starProjection (representationToEuclidean d (A.mulVec z)) ∧
      ‖representationToEuclidean m v‖ ≤ (K : ℝ) / γ ∧
      ‖representationToEuclidean d (A.mulVec z) -
        representationToEuclidean d (B.mulVec v)‖ ≤ δ * (K : ℝ) ∧
      ∀ u : FeatureVector m, (nonzeroSupport u).card ≤ K →
        ‖representationToEuclidean m (u - v)‖ ≤
          (‖representationToEuclidean d (A.mulVec z) -
            representationToEuclidean d (B.mulVec u)‖ + δ * (K : ℝ)) / γ := by
  let f := representationToEuclidean d (A.mulVec z)
  obtain ⟨v, hv, hsyn⟩ := (mem_euclideanColumnSpan_iff_exists_code B T _).mp
    ((euclideanColumnSpan B T).starProjection_apply_mem f)
  have hfnorm : ‖f‖ ≤ (K : ℝ) := source_synthesis_norm_le_of_cube_support A S hAunit hS z hcube hz
  have hvcard : (nonzeroSupport v).card ≤ K := (Finset.card_le_card hv).trans hT
  have hvnorm : ‖representationToEuclidean m v‖ ≤ (K : ℝ) / γ := by
    apply (le_div_iff₀ hγ).mpr
    have hstable := hBstable v (hvcard.trans (by omega))
    rw [hsyn] at hstable
    have hcontract := (euclideanColumnSpan B T).norm_starProjection_apply_le f
    simpa only [mul_comm] using hstable.trans (hcontract.trans hfnorm)
  have hfmem : f ∈ euclideanColumnSpan A S :=
    (mem_euclideanColumnSpan_iff_exists_code A S _).mpr ⟨z, hz, rfl⟩
  have hgap' : ‖(euclideanColumnSpan B T).starProjection -
      (euclideanColumnSpan A S).starProjection‖ ≤ δ := by
    simpa only [norm_sub_rev] using hgap
  have hproj : ‖f - representationToEuclidean d (B.mulVec v)‖ ≤ δ * (K : ℝ) := by
    rw [hsyn]
    exact (projection_residual_le_of_mem_projector_bound (euclideanColumnSpan B T)
      (euclideanColumnSpan A S) δ hgap' f hfmem).trans
      (mul_le_mul_of_nonneg_left hfnorm hδ)
  refine ⟨v, hv, hsyn, hvnorm, hproj, ?_⟩
  intro u hu
  apply (le_div_iff₀ hγ).mpr
  have hdist := hBstable.code_distance_le_residuals u v (A.mulVec z) hu hvcard
  simp only [map_sub] at hdist
  rw [norm_sub_rev (representationToEuclidean d (B.mulVec u))
    (representationToEuclidean d (A.mulVec z))] at hdist
  simpa only [mul_comm] using hdist.trans (add_le_add le_rfl hproj)

/-- The ambient projected source coordinate supplies its norm, source-code
evaluation, diagonal value, and all off-matched-column estimates on an
eligible support. -/
theorem exists_source_coordinate_functional_on_eligible_support
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (S : ι → Finset (Fin M)) (G : Finset ι) (T : G → Finset (Fin m))
    (e : {i : Fin M // ∃ s : G, i ∈ S s.1} ≃ {j : Fin m // ∃ s : G, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s.1 ↔ (e i).1 ∈ T s)
    (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hAstable : SparseLowerStable A γ (2 * K))
    (hScard : ∀ s ∈ G, (S s).card ≤ K)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hgap : ∀ s, ‖(euclideanColumnSpan A (S s.1)).starProjection -
      (euclideanColumnSpan B (T s)).starProjection‖ ≤ δ)
    (i : {i : Fin M // ∃ s : G, i ∈ S s.1})
    (s : G) (hs : s.1 ∈ eligibleSupportIndices S G i.1) :
    ∃ L : EuclideanRepresentation d →L[ℝ] ℝ, ‖L‖ ≤ 1 / γ ∧
      (∀ z : FeatureVector M, nonzeroSupport z ⊆ S s.1 →
        L (representationToEuclidean d (A.mulVec z)) = z i.1) ∧
      L (representationToEuclidean d (A.col i.1)) = 1 ∧
      ∀ j ∈ T s, j ≠ (e i).1 →
        |L (representationToEuclidean d (B.col j))| ≤ 2 * δ / γ := by
  obtain ⟨C, hsupport, hC⟩ := exists_ambient_projected_support_coefficient_map
    A (S s.1) γ hγ hAstable (hScard s.1 s.2)
  let L := (PiLp.proj 2 (fun _ : Fin M => ℝ) i.1).comp C
  have hi : i.1 ∈ S s.1 := ((mem_eligibleSupportIndices S G i.1 s.1).mp hs).2.1
  refine ⟨L, projected_support_coordinate_norm_le A (S s.1) C γ hγ hAstable
    (hScard s.1 s.2) hsupport hC i.1, ?_, ?_, ?_⟩
  · intro z hz
    change (C (representationToEuclidean d (A.mulVec z))) i.1 = z i.1
    rw [projected_support_coefficient_of_supported_code A (S s.1) C γ hγ hAstable
      (hScard s.1 s.2) hsupport hC z hz]
    rfl
  · change (C (representationToEuclidean d (A.col i.1))) i.1 = 1
    rw [projected_support_coefficient_on_source_column A (S s.1) C γ hγ hAstable
      (hScard s.1 s.2) hsupport hC i.1 hi]
    simp only [representationToEuclidean, PiLp.continuousLinearEquiv_symm_apply,
      Pi.single_eq_same]
  · exact projected_coordinates_small_on_eligible_support A B S G T e hmem γ δ
      hγ hδ hAstable hScard hBunit hgap i s hs C hsupport hC

/-- A matched column close to the negative source atom forces the actual
residual to control the active source coordinate on every eligible support. -/
theorem eligible_support_negative_orientation_bound
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (S : ι → Finset (Fin M)) (G : Finset ι) (T : G → Finset (Fin m))
    (e : {i : Fin M // ∃ s : G, i ∈ S s.1} ≃ {j : Fin m // ∃ s : G, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s.1 ↔ (e i).1 ∈ T s)
    (γ δ q : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hδ : 0 ≤ δ)
    (hq : q ≤ γ / 2)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A γ (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hScard : ∀ s ∈ G, (S s).card ≤ K) (hTcard : ∀ s, (T s).card ≤ K)
    (hgap : ∀ s, ‖(euclideanColumnSpan A (S s.1)).starProjection -
      (euclideanColumnSpan B (T s)).starProjection‖ ≤ δ)
    (i : {i : Fin M // ∃ s : G, i ∈ S s.1})
    (s : G) (hs : s.1 ∈ eligibleSupportIndices S G i.1)
    (hnegative : ‖representationToEuclidean d (A.col i.1) +
      representationToEuclidean d (B.col (e i).1)‖ ≤ q)
    (z : FeatureVector M) (hcube : ∀ j, 0 ≤ z j ∧ z j ≤ 1)
    (hz : nonzeroSupport z ⊆ S s.1)
    (u : FeatureVector m) (hu : (nonzeroSupport u).card ≤ K) (hnonneg : ∀ j, 0 ≤ u j) :
    z i.1 ≤
      ‖representationToEuclidean d (A.mulVec z) -
        representationToEuclidean d (B.mulVec u)‖ / γ ^ 2 +
      4 * δ * (K : ℝ) ^ 2 / γ ^ 2 := by
  obtain ⟨L, hL, hsource, hdiag, hoff⟩ := exists_source_coordinate_functional_on_eligible_support
    A B S G T e hmem γ δ hγ hδ hAstable hScard hBunit hgap i s hs
  obtain ⟨v, hv, _, hvnorm, hproj, hcomparison⟩ :=
    exists_supported_projection_code_of_cube_source A B (S s.1) (T s) γ δ
      hγ hδ hAunit hBstable (hScard s.1 s.2) (hTcard s) (hgap s) z hcube hz
  have he : (e i).1 ∈ T s :=
    (hmem i s).mp ((mem_eligibleSupportIndices S G i.1 s.1).mp hs).2.1
  have hneg : L (representationToEuclidean d (B.col (e i).1)) ≤ -(1 / 2 : ℝ) := by
    have hbound : |1 + L (representationToEuclidean d (B.col (e i).1))| ≤ q / γ := by
      calc
        _ = ‖L (representationToEuclidean d (A.col i.1) +
            representationToEuclidean d (B.col (e i).1))‖ := by
          rw [map_add, hdiag, Real.norm_eq_abs]
        _ ≤ ‖L‖ * ‖representationToEuclidean d (A.col i.1) +
            representationToEuclidean d (B.col (e i).1)‖ := L.le_opNorm _
        _ ≤ (1 / γ) * q := mul_le_mul hL hnegative (norm_nonneg _) (by positivity)
        _ = q / γ := by ring
    have hhalf : q / γ ≤ 1 / 2 := (div_le_iff₀ hγ).mpr (by linarith)
    have hleft := (le_abs_self _).trans (hbound.trans hhalf)
    linarith
  exact matched_coefficient_negative_orientation_bound B L (T s) (e i).1
    (representationToEuclidean d (A.mulVec z)) u v (z i.1) γ δ
    ‖representationToEuclidean d (A.mulVec z) - representationToEuclidean d (B.mulVec u)‖
    hK hγ hγone hδ (hTcard s) he hv hL (hsource z hz) hneg
    (abs_functional_column_le_of_norm B L γ hγ hL (e i).1 (hBunit _)) hoff
    hvnorm hproj (hcomparison u hu) (hnonneg _)

/-- Positive proximity of the matched column controls the actual matched
code coordinate on an eligible support. -/
theorem eligible_support_positive_orientation_bound
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (S : ι → Finset (Fin M)) (G : Finset ι) (T : G → Finset (Fin m))
    (e : {i : Fin M // ∃ s : G, i ∈ S s.1} ≃ {j : Fin m // ∃ s : G, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s.1 ↔ (e i).1 ∈ T s)
    (γ δ q : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hδ : 0 ≤ δ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A γ (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hScard : ∀ s ∈ G, (S s).card ≤ K) (hTcard : ∀ s, (T s).card ≤ K)
    (hgap : ∀ s, ‖(euclideanColumnSpan A (S s.1)).starProjection -
      (euclideanColumnSpan B (T s)).starProjection‖ ≤ δ)
    (i : {i : Fin M // ∃ s : G, i ∈ S s.1})
    (s : G) (hs : s.1 ∈ eligibleSupportIndices S G i.1)
    (hpositive : ‖representationToEuclidean d (A.col i.1) -
      representationToEuclidean d (B.col (e i).1)‖ ≤ q)
    (z : FeatureVector M) (hcube : ∀ j, 0 ≤ z j ∧ z j ≤ 1)
    (hz : nonzeroSupport z ⊆ S s.1)
    (u : FeatureVector m) (hu : (nonzeroSupport u).card ≤ K) :
    |u (e i).1 - z i.1| ≤
      ‖representationToEuclidean d (A.mulVec z) -
        representationToEuclidean d (B.mulVec u)‖ / γ +
      (q * (K : ℝ) + 4 * δ * (K : ℝ) ^ 2) / γ ^ 2 := by
  obtain ⟨L, hL, hsource, hdiag, hoff⟩ := exists_source_coordinate_functional_on_eligible_support
    A B S G T e hmem γ δ hγ hδ hAstable hScard hBunit hgap i s hs
  obtain ⟨v, hv, _, hvnorm, hproj, hcomparison⟩ :=
    exists_supported_projection_code_of_cube_source A B (S s.1) (T s) γ δ
      hγ hδ hAunit hBstable (hScard s.1 s.2) (hTcard s) (hgap s) z hcube hz
  have he : (e i).1 ∈ T s :=
    (hmem i s).mp ((mem_eligibleSupportIndices S G i.1 s.1).mp hs).2.1
  have hpos : |L (representationToEuclidean d (B.col (e i).1)) - 1| ≤ q / γ := by
    calc
      _ = ‖L (representationToEuclidean d (B.col (e i).1) -
          representationToEuclidean d (A.col i.1))‖ := by
        rw [map_sub, hdiag, Real.norm_eq_abs]
      _ ≤ ‖L‖ * ‖representationToEuclidean d (B.col (e i).1) -
          representationToEuclidean d (A.col i.1)‖ := L.le_opNorm _
      _ ≤ (1 / γ) * q := mul_le_mul hL (by simpa only [norm_sub_rev] using hpositive)
        (norm_nonneg _) (by positivity)
      _ = q / γ := by ring
  exact matched_coefficient_positive_orientation_bound B L (T s) (e i).1
    (representationToEuclidean d (A.mulVec z)) u v (z i.1) γ δ
    ‖representationToEuclidean d (A.mulVec z) - representationToEuclidean d (B.mulVec u)‖ q
    hK hγ hγone hδ (hTcard s) he hv hL (hsource z hz) hpos hoff
    hvnorm hproj (hcomparison u hu)

/-- On any paired support, a coordinate absent from the learned support
is bounded by the actual reconstruction residual plus projection error. -/
theorem absent_matched_coordinate_le_actual_residual {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (S : Finset (Fin M)) (T : Finset (Fin m)) (γ δ : ℝ)
    (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBstable : SparseLowerStable B γ (2 * K))
    (hS : S.card ≤ K) (hT : T.card ≤ K)
    (hgap : ‖(euclideanColumnSpan A S).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ)
    (z : FeatureVector M) (hcube : ∀ j, 0 ≤ z j ∧ z j ≤ 1)
    (hz : nonzeroSupport z ⊆ S)
    (u : FeatureVector m) (hu : (nonzeroSupport u).card ≤ K) (j : Fin m) (hj : j ∉ T) :
    u j ≤ (‖representationToEuclidean d (A.mulVec z) -
      representationToEuclidean d (B.mulVec u)‖ + δ * (K : ℝ)) / γ := by
  obtain ⟨v, hv, _, _, _, hcomparison⟩ := exists_supported_projection_code_of_cube_source
    A B S T γ δ hγ hδ hAunit hBstable hS hT hgap z hcube hz
  exact actual_coordinate_le_of_projected_support_exclusion T u v j γ δ
    ‖representationToEuclidean d (A.mulVec z) - representationToEuclidean d (B.mulVec u)‖
    hv hj (hcomparison u hu)

end PKG26AtomicFeatures
