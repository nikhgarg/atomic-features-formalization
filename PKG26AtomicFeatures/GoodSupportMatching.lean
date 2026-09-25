import PKG26AtomicFeatures.WeightedGoodSupports
import PKG26AtomicFeatures.ApproximateSupportMatching

/-!
# Consistent matching from weighted support separation

Restrict the support family to its actual positive-weight, low-loss indices.
The weighted separation bound isolates every sufficiently prevalent atom in
that family. Approximate span matching then gives one membership-preserving
bijection of the good-support unions, with the singleton line estimate for
all such atoms under that same bijection.
-/

namespace PKG26AtomicFeatures

/-- The membership pattern on the subtype of good indices is exactly the
family of good containing indices after forgetting the subtype proof. -/
theorem supportMembershipPattern_good_indices_map
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ : ℝ) (i : Fin M) :
    (supportMembershipPattern (fun s : goodSupportIndices w loss τ => S s.1) i).map
        ⟨Subtype.val, Subtype.val_injective⟩ =
      goodContainingSupportIndices S w loss τ i := by
  classical
  ext s
  simp only [Finset.mem_map, mem_supportMembershipPattern,
    mem_goodContainingSupportIndices]
  constructor
  · rintro ⟨t, hi, rfl⟩
    exact ⟨(mem_goodSupportIndices w loss τ t.1).mp t.property, hi⟩
  · rintro ⟨hgood, hi⟩
    exact ⟨⟨s, (mem_goodSupportIndices w loss τ s).mpr hgood⟩, hi, rfl⟩

/-- Passing to the subtype of good indices preserves the full intersection
of the supports containing a source atom, including empty families. -/
theorem supportFamilyIntersection_good_membership_pattern
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ : ℝ) (i : Fin M) :
    supportFamilyIntersection (fun s : goodSupportIndices w loss τ => S s.1)
        (supportMembershipPattern (fun s : goodSupportIndices w loss τ => S s.1) i) =
      supportFamilyIntersection S (goodContainingSupportIndices S w loss τ i) := by
  classical
  ext j
  simp only [mem_supportFamilyIntersection, mem_supportMembershipPattern]
  constructor
  · intro hj s hs
    have hparts := (mem_goodContainingSupportIndices S w loss τ i s).mp hs
    exact hj ⟨s, (mem_goodSupportIndices w loss τ s).mpr hparts.1⟩ hparts.2
  · intro hj s hs
    exact hj s.1 ((mem_goodContainingSupportIndices S w loss τ i s.1).mpr
      ⟨(mem_goodSupportIndices w loss τ s.1).mp s.property, hs⟩)

/-- Loss below the separation scale places the atom in the actual good
support union. This does not assume a positive total loss. -/
theorem mem_good_support_union_of_separation_scale
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hτ : 0 < τ) (hρ : 0 < ρ) (hρone : ρ ≤ 1) (i : Fin M)
    (hsmall : weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i) :
    ∃ s : goodSupportIndices w loss τ, i ∈ S s.1 := by
  obtain ⟨s, hs⟩ := goodContainingSupportIndices_nonempty_of_separation_scale
    S w loss τ ρ hw hloss hτ hρ hρone i hsmall
  have hparts := (mem_goodContainingSupportIndices S w loss τ i s).mp hs
  exact ⟨⟨s, (mem_goodSupportIndices w loss τ s).mpr hparts.1⟩, hparts.2⟩

/-- Every membership-preserving matching of good-support unions has the
singleton line estimate for atoms isolated by actual weighted separation. -/
theorem matched_good_support_line_projector_bound
    {ι : Type*} [Fintype ι] {d M m K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hτ : 0 < τ) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ η : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1)
    (T : goodSupportIndices w loss τ → Finset (Fin m))
    (hScard : ∀ s, (S s).card ≤ K) (hTcard : ∀ s, (T s).card ≤ K)
    (hgap : ∀ s,
      ‖(euclideanColumnSpan A (S s.1)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          η / (2 * (1 + 2 * (K : ℝ) / min α γ)))
    (e : {i : Fin M // ∃ s : goodSupportIndices w loss τ, i ∈ S s.1} ≃
      {j : Fin m // ∃ s, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s.1 ↔ (e i).1 ∈ T s)
    (i : {i : Fin M // ∃ s : goodSupportIndices w loss τ, i ∈ S s.1})
    (hsep : ∀ j, j ≠ i.1 →
      ρ * supportMarginalWeight S w i.1 ≤ supportSeparationWeight S w i.1 j)
    (hsmall : weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i.1) :
    supportFamilyIntersection T (supportMembershipPattern T (e i).1) = {(e i).1} ∧
      ‖(euclideanColumnSpan A {i.1}).starProjection -
        (euclideanColumnSpan B {(e i).1}).starProjection‖ ≤ η / 2 := by
  classical
  have hsingle := (good_support_intersection_eq_singleton_of_separation
    S w loss τ ρ hw hloss hτ hρ hρone i.1 hsep hsmall).2
  have hsingle' :
      supportFamilyIntersection (fun s : goodSupportIndices w loss τ => S s.1)
        (supportMembershipPattern (fun s : goodSupportIndices w loss τ => S s.1) i.1) =
          {i.1} := by
    rw [supportFamilyIntersection_good_membership_pattern, hsingle]
  have hline := matched_line_projector_bound_of_singleton_intersection A B α γ η
    hAunit hBunit hAstable hBstable hα hγ hη hηone
    (fun s : goodSupportIndices w loss τ => S s.1) T
    (supportMembershipPattern (fun s : goodSupportIndices w loss τ => S s.1) i.1)
    (supportMembershipPattern_nonempty_of_mem_union _ i)
    (fun s _ => hScard s.1) (fun s _ => hTcard s) (fun s _ => hgap s)
    e hmem i hsingle'
  rwa [supportMembershipPattern_eq_of_membership_equiv _ T e hmem i] at hline

/-- When an atom has unavoidable companions, the same membership matching
controls their whole source span and the learned intersection containing its
matched coordinate. The companion set is derived from zero separation mass. -/
theorem matched_good_support_companion_projector_bound
    {ι : Type*} [Fintype ι] {d M m K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hτ : 0 < τ) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ η : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1)
    (T : goodSupportIndices w loss τ → Finset (Fin m))
    (hScard : ∀ s, (S s).card ≤ K) (hTcard : ∀ s, (T s).card ≤ K)
    (hgap : ∀ s,
      ‖(euclideanColumnSpan A (S s.1)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          η / (2 * (1 + 2 * (K : ℝ) / min α γ)))
    (e : {i : Fin M // ∃ s : goodSupportIndices w loss τ, i ∈ S s.1} ≃
      {j : Fin m // ∃ s, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s.1 ↔ (e i).1 ∈ T s)
    (i : {i : Fin M // ∃ s : goodSupportIndices w loss τ, i ∈ S s.1})
    (hsep : ∀ j, j ∉ forcedCompanionSet S w i.1 →
      ρ * supportMarginalWeight S w i.1 ≤ supportSeparationWeight S w i.1 j)
    (hsmall : weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i.1) :
    ‖(euclideanColumnSpan A (forcedCompanionSet S w i.1)).starProjection -
      (euclideanColumnSpan B
        (supportFamilyIntersection T (supportMembershipPattern T (e i).1))).starProjection‖ ≤
      η / 2 := by
  have hcompanions := (good_support_intersection_eq_forcedCompanionSet
    S w loss τ ρ hw hloss hτ hρ hρone i.1 hsep hsmall).2
  have hgeometry := matched_containing_intersections_projector_bound A B α γ η
    hAunit hBunit hAstable hBstable hα hγ hη hηone
    (fun s : goodSupportIndices w loss τ => S s.1) T
    (fun s => hScard s.1) hTcard hgap e hmem i
  rwa [supportFamilyIntersection_good_membership_pattern, hcompanions] at hgeometry

/-- One matching works simultaneously for every atom whose weighted
separation mass dominates the actual loss budget. Union membership and the
singleton source intersection are both derived, rather than assumed. -/
theorem exists_good_support_matching
    {ι : Type*} [Fintype ι] {d M m K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hτ : 0 < τ) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ η : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1)
    (T : goodSupportIndices w loss τ → Finset (Fin m))
    (hScard : ∀ s, (S s).card ≤ K) (hTcard : ∀ s, (T s).card ≤ K)
    (hgap : ∀ s,
      ‖(euclideanColumnSpan A (S s.1)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          η / (2 * (1 + 2 * (K : ℝ) / min α γ))) :
    ∃ e : {i : Fin M // ∃ s : goodSupportIndices w loss τ, i ∈ S s.1} ≃
        {j : Fin m // ∃ s, j ∈ T s},
      (∀ i s, i.1 ∈ S s.1 ↔ (e i).1 ∈ T s) ∧
      ∀ i : Fin M,
        (∀ j, j ≠ i →
          ρ * supportMarginalWeight S w i ≤ supportSeparationWeight S w i j) →
        weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i →
        ∃ hi : ∃ s : goodSupportIndices w loss τ, i ∈ S s.1,
          supportFamilyIntersection T (supportMembershipPattern T (e ⟨i, hi⟩).1) =
              {(e ⟨i, hi⟩).1} ∧
            ‖(euclideanColumnSpan A {i}).starProjection -
              (euclideanColumnSpan B {(e ⟨i, hi⟩).1}).starProjection‖ ≤ η / 2 := by
  classical
  obtain ⟨e, hmem⟩ := exists_support_membership_equiv_of_projector_bounds A B α γ η
    hAunit hBunit hAstable hBstable hα hγ hη hηone
    (fun s : goodSupportIndices w loss τ => S s.1) T
    (fun s => hScard s.1) hTcard hgap
  refine ⟨e, hmem, ?_⟩
  intro i hsep hsmall
  have hi := mem_good_support_union_of_separation_scale
    S w loss τ ρ hw hloss hτ hρ hρone i hsmall
  exact ⟨hi, matched_good_support_line_projector_bound S w loss τ ρ hw hloss hτ hρ hρone
    A B α γ η hAunit hBunit hAstable hBstable hα hγ hη hηone T hScard hTcard hgap
    e hmem ⟨i, hi⟩ hsep hsmall⟩

end PKG26AtomicFeatures
