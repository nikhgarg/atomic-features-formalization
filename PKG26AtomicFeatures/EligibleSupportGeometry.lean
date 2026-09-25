import PKG26AtomicFeatures.SupportedCoordinateProjection
import PKG26AtomicFeatures.ExceptionalCompanionWeights

/-!
# Coordinate isolation on eligible supports

One membership-preserving matching of accurate support spans controls all
off-diagonal coordinates of an eligible support. A co-occurring atom only
needs some accurate support without the target; it need not be prevalent.
-/

namespace PKG26AtomicFeatures

/-- A column appearing in two paired learned spans has a small source
coordinate whenever the second source support excludes that coordinate. -/
theorem projected_coordinate_small_of_two_paired_spans {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (S S' : Finset (Fin M)) (T T' : Finset (Fin m))
    (C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M)
    (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hstable : SparseLowerStable A γ (2 * K)) (hS : S.card ≤ K) (hS' : S'.card ≤ K)
    (hsupport : ∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S)
    (hC : ∀ x, representationToEuclidean d
      (A.mulVec ((representationToEuclidean M).symm (C x))) =
        (euclideanColumnSpan A S).starProjection x)
    (hgap : ‖(euclideanColumnSpan A S).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ)
    (hgap' : ‖(euclideanColumnSpan A S').starProjection -
      (euclideanColumnSpan B T').starProjection‖ ≤ δ)
    (i : Fin M) (hi : i ∉ S') (j : Fin m) (hj : j ∈ T) (hj' : j ∈ T')
    (hunit : ‖representationToEuclidean d (B.col j)‖ ≤ 1) :
    |(C (representationToEuclidean d (B.col j))) i| ≤ 2 * δ / γ := by
  have hmem (U : Finset (Fin m)) (hjU : j ∈ U) :
      representationToEuclidean d (B.col j) ∈ euclideanColumnSpan B U := by
    apply (mem_euclideanColumnSpan_iff_exists_code B U _).mpr
    exact ⟨Pi.single j 1, nonzeroSupport_subset_of_mem_coordinateSpan
      (canonicalVector_mem_coordinateSpan U hjU), by simp only [Matrix.mulVec_single_one]⟩
  have hnear := projection_residual_le_of_mem_projector_bound
    (euclideanColumnSpan A S) (euclideanColumnSpan B T) δ hgap _ (hmem T hj)
  have hnear' := projection_residual_le_of_mem_projector_bound
    (euclideanColumnSpan A S') (euclideanColumnSpan B T') δ hgap' _ (hmem T' hj')
  have hbound : δ * ‖representationToEuclidean d (B.col j)‖ ≤ δ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit hδ
  simpa only [← two_mul] using projected_support_coordinate_le_of_two_residuals
    A S S' C γ hγ hstable hS hS' hsupport hC _ δ δ
    (hnear.trans hbound) (hnear'.trans hbound) i hi

/-- On an eligible source support, all matched learned columns except the
target have small target coordinates. The membership equivalence alone
supplies their source identities, including arbitrarily rare companions. -/
theorem projected_coordinates_small_on_eligible_support
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (S : ι → Finset (Fin M)) (G : Finset ι) (T : G → Finset (Fin m))
    (e : {i : Fin M // ∃ s : G, i ∈ S s.1} ≃ {j : Fin m // ∃ s : G, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s.1 ↔ (e i).1 ∈ T s)
    (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hstable : SparseLowerStable A γ (2 * K))
    (hcard : ∀ s ∈ G, (S s).card ≤ K)
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hgap : ∀ s, ‖(euclideanColumnSpan A (S s.1)).starProjection -
      (euclideanColumnSpan B (T s)).starProjection‖ ≤ δ)
    (i : {i : Fin M // ∃ s : G, i ∈ S s.1})
    (s : G) (hs : s.1 ∈ eligibleSupportIndices S G i.1)
    (C : EuclideanRepresentation d →L[ℝ] EuclideanRepresentation M)
    (hsupport : ∀ x, nonzeroSupport ((representationToEuclidean M).symm (C x)) ⊆ S s.1)
    (hC : ∀ x, representationToEuclidean d
      (A.mulVec ((representationToEuclidean M).symm (C x))) =
        (euclideanColumnSpan A (S s.1)).starProjection x) :
    ∀ j ∈ T s, j ≠ (e i).1 →
      |(C (representationToEuclidean d (B.col j))) i.1| ≤ 2 * δ / γ := by
  intro j hj hji
  let j' : {j : Fin m // ∃ s : G, j ∈ T s} := ⟨j, s, hj⟩
  let k := e.symm j'
  have hek : (e k).1 = j := congrArg Subtype.val (e.apply_symm_apply j')
  have hks : k.1 ∈ S s.1 := (hmem k s).mpr (by simpa only [hek] using hj)
  have hki : k.1 ≠ i.1 := by
    intro h
    have hki' : k = i := Subtype.ext h
    exact hji (hek.symm.trans (congrArg (fun l => (e l).1) hki'))
  obtain ⟨t, ht, hkt, hit⟩ := exists_selected_support_excluding_of_eligible
    S G i.1 s.1 hs k.1 hks hki
  have hjt : j ∈ T ⟨t, ht⟩ := by
    simpa only [hek] using (hmem k ⟨t, ht⟩).mp hkt
  exact projected_coordinate_small_of_two_paired_spans A B (S s.1) (S t)
    (T s) (T ⟨t, ht⟩) C γ δ hγ hδ hstable (hcard s.1 s.2) (hcard t ht)
    hsupport hC (hgap s) (hgap ⟨t, ht⟩) i.1 hit j hj hjt (hunit j)

end PKG26AtomicFeatures
