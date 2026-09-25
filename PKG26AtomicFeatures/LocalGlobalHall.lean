import PKG26AtomicFeatures.AppendixHall
import Mathlib.Combinatorics.Hall.Basic

/-!
# The source's local-to-global Hall lemma for arbitrary graphs

Source anchors: `theory.tex:76-86` and `proofs.tex:36-46` in the canonical
Overleaf snapshot `7bc55a1e3bd2e5c7776555abfafd23593662a4b2`.

The paper states the lemma for a bipartite graph without assuming either
vertex class is finite. Its printed tree argument establishes the Hall
inequality on every finite collection of left vertices. The upper bound for a
singleton also makes every individual right-neighborhood finite, so the
compactness form of Hall's theorem produces one matching on the entire left
vertex type. Restricting that matching gives the source's cardinal Hall
inequality for arbitrary left-vertex sets.
-/

namespace PKG26AtomicFeatures
namespace LocalGlobalHall

universe u

/-- The right-neighborhood of an arbitrary set of left vertices in the
source's bipartite graph. -/
def graphNeighborhood {Left Right : Type u} (edges : Left → Right → Prop)
    (vertices : Set Left) : Set Right :=
  {right | ∃ left ∈ vertices, edges left right}

/-- The source-literal local-to-global Hall lemma, including its matching and
cardinality conclusions, for possibly infinite vertex types.

The hypotheses compare cardinalities of arbitrary vertex sets with the finite
cardinals `2 * K`, `K`, and `2 * K - 1`. No local-finiteness premise is added:
it follows from the upper inequality applied to each singleton. -/
theorem local_to_global_hall
    {Left Right : Type u} (edges : Left → Right → Prop) (K : ℕ)
    (hK : 1 ≤ K)
    (hlower : ∀ vertices : Set Left,
      Cardinal.mk vertices ≤ ((2 * K : ℕ) : Cardinal.{u}) →
      Cardinal.mk vertices ≤ Cardinal.mk (graphNeighborhood edges vertices))
    (hupper : ∀ vertices : Set Left,
      Cardinal.mk vertices ≤ (K : Cardinal.{u}) →
      Cardinal.mk (graphNeighborhood edges vertices) ≤
        ((2 * K - 1 : ℕ) : Cardinal.{u})) :
    (∀ vertices : Set Left,
      Cardinal.mk vertices ≤ Cardinal.mk (graphNeighborhood edges vertices)) ∧
    (∃ matching : Left → Right,
      Function.Injective matching ∧ ∀ left, edges left (matching left)) ∧
    Cardinal.mk Left ≤ Cardinal.mk Right := by
  classical
  have hneighbor_finite (left : Left) :
      (graphNeighborhood edges ({left} : Set Left)).Finite := by
    apply Cardinal.lt_aleph0_iff_set_finite.mp
    have hsingleton : Cardinal.mk ({left} : Set Left) ≤ (K : Cardinal.{u}) := by
      simpa using hK
    exact (hupper ({left} : Set Left) hsingleton).trans_lt
      Cardinal.natCast_lt_aleph0
  let supports : Left → Finset Right := fun left => (hneighbor_finite left).toFinset
  have hsupports (left : Left) (right : Right) :
      right ∈ supports left ↔ edges left right := by
    simp [supports, graphNeighborhood]
  have hneighborhood (vertices : Finset Left) :
      graphNeighborhood edges (vertices : Set Left) =
        (vertices.biUnion supports : Set Right) := by
    ext right
    simp [graphNeighborhood, hsupports]
  have hlower_fin (vertices : Finset Left) (hcard : vertices.card ≤ 2 * K) :
      vertices.card ≤ (vertices.biUnion supports).card := by
    have hcard' : Cardinal.mk (vertices : Set Left) ≤
        ((2 * K : ℕ) : Cardinal.{u}) := by
      change Cardinal.mk {left // left ∈ vertices} ≤
        ((2 * K : ℕ) : Cardinal.{u})
      rw [Cardinal.mk_coe_finset]
      exact_mod_cast hcard
    have h := hlower (vertices : Set Left) hcard'
    rw [hneighborhood vertices] at h
    simpa [Cardinal.mk_fintype] using h
  have hupper_fin (vertices : Finset Left) (hcard : vertices.card ≤ K) :
      (vertices.biUnion supports).card ≤ 2 * K - 1 := by
    have hcard' : Cardinal.mk (vertices : Set Left) ≤ (K : Cardinal.{u}) := by
      simpa using hcard
    have h := hupper (vertices : Set Left) hcard'
    rw [hneighborhood vertices] at h
    simpa [Cardinal.mk_fintype] using h
  have hfiniteHall (vertices : Finset Left) :
      vertices.card ≤ (vertices.biUnion supports).card := by
    let inclusion : {left // left ∈ vertices} ↪ Left :=
      ⟨Subtype.val, Subtype.val_injective⟩
    let restricted : {left // left ∈ vertices} → Finset Right :=
      fun left => supports left
    have hlower_restricted :
        ∀ selected : Finset {left // left ∈ vertices}, selected.card ≤ 2 * K →
          selected.card ≤ (selected.biUnion restricted).card := by
      intro selected hselected
      let projected : Finset Left := selected.map inclusion
      have hprojected_card : projected.card = selected.card := by
        simp [projected]
      have hunion : projected.biUnion supports = selected.biUnion restricted := by
        ext right
        simp [projected, restricted, inclusion]
      rw [← hunion, ← hprojected_card]
      exact hlower_fin projected (by simpa [hprojected_card] using hselected)
    have hupper_restricted :
        ∀ selected : Finset {left // left ∈ vertices}, selected.card ≤ K →
          (selected.biUnion restricted).card ≤ 2 * K - 1 := by
      intro selected hselected
      let projected : Finset Left := selected.map inclusion
      have hprojected_card : projected.card = selected.card := by
        simp [projected]
      have hunion : projected.biUnion supports = selected.biUnion restricted := by
        ext right
        simp [projected, restricted, inclusion]
      rw [← hunion]
      exact hupper_fin projected (by simpa [hprojected_card] using hselected)
    have hrestricted : AppendixHall.GlobalHall restricted :=
      AppendixHall.local_hall_implies_global restricted K (2 * K - 1)
        (by omega) hlower_restricted hupper_restricted
    have hall_univ := hrestricted (Finset.univ : Finset {left // left ∈ vertices})
    change Finset.univ.card ≤ (Finset.univ.biUnion restricted).card at hall_univ
    have huniv_union :
        (Finset.univ.biUnion restricted) = vertices.biUnion supports := by
      ext right
      simp [restricted]
    rw [huniv_union] at hall_univ
    simpa using hall_univ
  obtain ⟨matching, hinjective, hmatching⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective supports).mp hfiniteHall
  have hedge (left : Left) : edges left (matching left) :=
    (hsupports left (matching left)).mp (hmatching left)
  refine ⟨?_, ⟨matching, hinjective, hedge⟩,
    Cardinal.mk_le_of_injective hinjective⟩
  intro vertices
  let restrictedMatching : vertices → graphNeighborhood edges vertices :=
    fun left => ⟨matching left, left, left.property, hedge left⟩
  refine Cardinal.mk_le_of_injective (f := restrictedMatching) ?_
  intro left₁ left₂ heq
  exact Subtype.ext (hinjective (congrArg Subtype.val heq))

end LocalGlobalHall
end PKG26AtomicFeatures
