import PKG26AtomicFeatures.StableSupportIntersections
import PKG26AtomicFeatures.SupportMembershipMatching

/-!
# One consistent matching of approximately equal support spans

Stable support intersections preserve every nonempty intersection cardinality.
The finite membership-pattern theorem therefore supplies one bijection of the
support unions preserving all support memberships. Under this same bijection,
an atom isolated by the intersection of its containing supports has a matched
learned line with the quantitative projector bound.

Only atoms in the support unions are matched. The family of supports may be
empty; then both unions are empty and the matching conclusion remains valid.
-/

namespace PKG26AtomicFeatures

/-- A membership-preserving bijection also preserves membership in every
intersection, for coordinates in the respective support unions. -/
theorem mem_support_intersection_iff_of_membership_equiv
    {ι : Type*} {M m : ℕ}
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m))
    (e : {i : Fin M // ∃ s, i ∈ S s} ≃ {j : Fin m // ∃ s, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s ↔ (e i).1 ∈ T s)
    (family : Finset ι) (i : {i : Fin M // ∃ s, i ∈ S s}) :
    i.1 ∈ supportFamilyIntersection S family ↔
      (e i).1 ∈ supportFamilyIntersection T family := by
  simp only [mem_supportFamilyIntersection]
  constructor
  · intro hi s hs
    exact (hmem i s).mp (hi s hs)
  · intro hi s hs
    exact (hmem i s).mpr (hi s hs)

/-- A nonempty support intersection equal to one source coordinate is equal
to its matched coordinate on the learned side. Nonemptiness ensures that any
coordinate in the target intersection lies in the target support union, so
surjectivity of the union bijection applies. -/
theorem support_intersection_singleton_of_membership_equiv
    {ι : Type*} {M m : ℕ}
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m))
    (e : {i : Fin M // ∃ s, i ∈ S s} ≃ {j : Fin m // ∃ s, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s ↔ (e i).1 ∈ T s)
    (family : Finset ι) (hne : family.Nonempty)
    (i : {i : Fin M // ∃ s, i ∈ S s})
    (hsingle : supportFamilyIntersection S family = {i.1}) :
    supportFamilyIntersection T family = {(e i).1} := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨s, hs⟩ := hne
    have hjunion : ∃ s, j ∈ T s :=
      ⟨s, (mem_supportFamilyIntersection T family j).mp hj s hs⟩
    let j' : {j : Fin m // ∃ s, j ∈ T s} := ⟨j, hjunion⟩
    have hinverse : (e.symm j').1 ∈ supportFamilyIntersection S family := by
      apply (mem_support_intersection_iff_of_membership_equiv S T e hmem family _).mpr
      simpa only [e.apply_symm_apply] using hj
    rw [hsingle, Finset.mem_singleton] at hinverse
    have hinverse' : e.symm j' = i := Subtype.ext hinverse
    have hequal : j' = e i := by simpa only [e.apply_symm_apply] using congrArg e hinverse'
    exact Finset.mem_singleton.mpr (congrArg Subtype.val hequal)
  · intro hj
    rw [Finset.mem_singleton] at hj
    subst j
    apply (mem_support_intersection_iff_of_membership_equiv S T e hmem family i).mp
    simp only [hsingle, Finset.mem_singleton]

/-- The source and learned coordinates selected by a membership equivalence
have exactly the same set of containing support indices. -/
theorem supportMembershipPattern_eq_of_membership_equiv
    {ι : Type*} [Fintype ι] {M m : ℕ}
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m))
    (e : {i : Fin M // ∃ s, i ∈ S s} ≃ {j : Fin m // ∃ s, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s ↔ (e i).1 ∈ T s)
    (i : {i : Fin M // ∃ s, i ∈ S s}) :
    supportMembershipPattern S i.1 = supportMembershipPattern T (e i).1 := by
  classical
  ext s
  simp only [mem_supportMembershipPattern]
  exact hmem i s

/-- A coordinate in the support union has at least one containing support. -/
theorem supportMembershipPattern_nonempty_of_mem_union
    {ι : Type*} [Fintype ι] {M : ℕ} (S : ι → Finset (Fin M))
    (i : {i : Fin M // ∃ s, i ∈ S s}) :
    (supportMembershipPattern S i.1).Nonempty := by
  obtain ⟨s, hs⟩ := i.property
  exact ⟨s, (mem_supportMembershipPattern S i.1 s).mpr hs⟩

/-- Approximate equality of all paired support spans supplies one bijection
between their unions preserving every membership. This includes an empty
support-index type and does not require either union to contain every atom. -/
theorem exists_support_membership_equiv_of_projector_bounds
    {ι : Type*} [Fintype ι] {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ η : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m))
    (hScard : ∀ s, (S s).card ≤ K) (hTcard : ∀ s, (T s).card ≤ K)
    (hgap : ∀ s,
      ‖(euclideanColumnSpan A (S s)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          η / (2 * (1 + 2 * (K : ℝ) / min α γ))) :
    ∃ e : {i : Fin M // ∃ s, i ∈ S s} ≃ {j : Fin m // ∃ s, j ∈ T s},
      ∀ i s, i.1 ∈ S s ↔ (e i).1 ∈ T s := by
  classical
  apply exists_support_membership_equiv_of_intersection_card_eq S T
  intro family hne
  have hcard := (stable_support_intersections A B α γ η hAunit hBunit
    hAstable hBstable hα hγ hη hηone S T family hne
    (fun s _ => hScard s) (fun s _ => hTcard s) (fun s _ => hgap s)).1
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert hcard using 1 <;> congr 1 <;> ext i <;> simp [supportFamilyIntersection]

/-- For any membership-preserving union bijection, every singleton source
intersection yields the corresponding singleton learned intersection and its
line-projector estimate. Thus the geometric matching agrees with the single
bijection used for all supports. -/
theorem matched_line_projector_bound_of_singleton_intersection
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ η : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m))
    (family : Finset ι) (hne : family.Nonempty)
    (hScard : ∀ s ∈ family, (S s).card ≤ K)
    (hTcard : ∀ s ∈ family, (T s).card ≤ K)
    (hgap : ∀ s ∈ family,
      ‖(euclideanColumnSpan A (S s)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          η / (2 * (1 + 2 * (K : ℝ) / min α γ)))
    (e : {i : Fin M // ∃ s, i ∈ S s} ≃ {j : Fin m // ∃ s, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s ↔ (e i).1 ∈ T s)
    (i : {i : Fin M // ∃ s, i ∈ S s})
    (hsingle : supportFamilyIntersection S family = {i.1}) :
    supportFamilyIntersection T family = {(e i).1} ∧
      ‖(euclideanColumnSpan A {i.1}).starProjection -
        (euclideanColumnSpan B {(e i).1}).starProjection‖ ≤ η / 2 := by
  have htarget := support_intersection_singleton_of_membership_equiv
    S T e hmem family hne i hsingle
  refine ⟨htarget, ?_⟩
  have hgeometry := (stable_support_intersections A B α γ η hAunit hBunit
    hAstable hBstable hα hγ hη hηone S T family hne hScard hTcard hgap).2
  simpa only [hsingle, htarget] using hgeometry

/-- Even when the containing supports do not isolate an atom, their full
intersection spans are close under the same membership bijection. The target
family consists precisely of the supports containing the matched coordinate.
This is the corresponding bound for atoms with unavoidable companions. -/
theorem matched_containing_intersections_projector_bound
    {ι : Type*} [Fintype ι] {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ η : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m))
    (hScard : ∀ s, (S s).card ≤ K) (hTcard : ∀ s, (T s).card ≤ K)
    (hgap : ∀ s,
      ‖(euclideanColumnSpan A (S s)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          η / (2 * (1 + 2 * (K : ℝ) / min α γ)))
    (e : {i : Fin M // ∃ s, i ∈ S s} ≃ {j : Fin m // ∃ s, j ∈ T s})
    (hmem : ∀ i s, i.1 ∈ S s ↔ (e i).1 ∈ T s)
    (i : {i : Fin M // ∃ s, i ∈ S s}) :
    ‖(euclideanColumnSpan A
        (supportFamilyIntersection S (supportMembershipPattern S i.1))).starProjection -
      (euclideanColumnSpan B
        (supportFamilyIntersection T (supportMembershipPattern T (e i).1))).starProjection‖ ≤
      η / 2 := by
  rw [← supportMembershipPattern_eq_of_membership_equiv S T e hmem i]
  exact (stable_support_intersections A B α γ η hAunit hBunit hAstable hBstable
    hα hγ hη hηone S T (supportMembershipPattern S i.1)
    (supportMembershipPattern_nonempty_of_mem_union S i)
    (fun s _ => hScard s) (fun s _ => hTcard s) (fun s _ => hgap s)).2

/-- One bijection simultaneously preserves all support memberships and
matches every source atom isolated by its containing supports to a learned
line within projector distance `η/2`. The learned singleton is derived from
the bijection; no separation property is imposed on atoms not isolated this
way, and no matching is asserted for atoms outside the support unions. -/
theorem exists_approximate_support_matching
    {ι : Type*} [Fintype ι] {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (α γ η : ℝ)
    (hAunit : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (hBunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hAstable : SparseLowerStable A α (2 * K))
    (hBstable : SparseLowerStable B γ (2 * K))
    (hα : 0 < α) (hγ : 0 < γ) (hη : 0 < η) (hηone : η < 1)
    (S : ι → Finset (Fin M)) (T : ι → Finset (Fin m))
    (hScard : ∀ s, (S s).card ≤ K) (hTcard : ∀ s, (T s).card ≤ K)
    (hgap : ∀ s,
      ‖(euclideanColumnSpan A (S s)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          η / (2 * (1 + 2 * (K : ℝ) / min α γ))) :
    ∃ e : {i : Fin M // ∃ s, i ∈ S s} ≃ {j : Fin m // ∃ s, j ∈ T s},
      (∀ i s, i.1 ∈ S s ↔ (e i).1 ∈ T s) ∧
      ∀ i, supportFamilyIntersection S (supportMembershipPattern S i.1) = {i.1} →
        supportFamilyIntersection T (supportMembershipPattern T (e i).1) = {(e i).1} ∧
          ‖(euclideanColumnSpan A {i.1}).starProjection -
            (euclideanColumnSpan B {(e i).1}).starProjection‖ ≤ η / 2 := by
  obtain ⟨e, hmem⟩ := exists_support_membership_equiv_of_projector_bounds A B α γ η
    hAunit hBunit hAstable hBstable hα hγ hη hηone S T hScard hTcard hgap
  refine ⟨e, hmem, ?_⟩
  intro i hsingle
  have hgeometry := matched_line_projector_bound_of_singleton_intersection A B α γ η
    hAunit hBunit hAstable hBstable hα hγ hη hηone S T
    (supportMembershipPattern S i.1) (supportMembershipPattern_nonempty_of_mem_union S i)
    (fun s _ => hScard s) (fun s _ => hTcard s) (fun s _ => hgap s) e hmem i hsingle
  rwa [supportMembershipPattern_eq_of_membership_equiv S T e hmem i] at hgeometry

end PKG26AtomicFeatures
