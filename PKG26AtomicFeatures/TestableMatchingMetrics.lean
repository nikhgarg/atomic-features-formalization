import PKG26AtomicFeatures.SignedLineGeometry
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Testable matching metrics

For normalized dictionary columns, signed Euclidean inner product equals
cosine similarity. The metric below is the maximum cardinality of
a subset of the first dictionary that admits an injective threshold matching
into each comparison dictionary. The comparison widths may differ.

Common-reference recovery gives a lower bound for this actual maximum.
The reference index type may be a nested recoverable set or the intersection
of separately defined recoverable sets; no common prevalence ordering across
different laws is assumed.
-/

namespace PKG26AtomicFeatures

open scoped InnerProductSpace

/-- A selected subset of the first dictionary admits a separate injective
matching into every comparison dictionary at the given similarity threshold.
For unit columns, the comparison is signed cosine similarity. -/
def HasSimultaneousThresholdMatching
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ)
    (t : ℝ) (J : Finset (Fin m)) : Prop :=
  ∀ l, ∃ e : {j // j ∈ J} ↪ Fin (width l), ∀ j,
    t ≤ inner ℝ (representationToEuclidean d (B.col j.1))
      (representationToEuclidean d ((C l).col (e j)))

/-- All admissible column subsets, drawn from the finite powerset of the
first dictionary's column indices. -/
noncomputable def thresholdMatchingSubsets
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ) :
    Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (HasSimultaneousThresholdMatching width B C t)

@[simp] theorem mem_thresholdMatchingSubsets
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ) (J : Finset (Fin m)) :
    J ∈ thresholdMatchingSubsets width B C t ↔
      HasSimultaneousThresholdMatching width B C t J := by
  classical
  simp [thresholdMatchingSubsets]

/-- The paper's matching metric on normalized columns: an actual finite
maximum over admissible subsets, rather than a supplied matching witness. -/
noncomputable def testableMatchingMetric
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ) : ℕ :=
  (thresholdMatchingSubsets width B C t).sup Finset.card

/-- The empty subset is admissible at every threshold, even for a zero-width
comparison dictionary. -/
theorem empty_hasSimultaneousThresholdMatching
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ) :
    HasSimultaneousThresholdMatching width B C t ∅ := by
  classical
  letI : IsEmpty {j : Fin m // j ∈ (∅ : Finset (Fin m))} :=
    ⟨fun j => Finset.notMem_empty j.1 j.2⟩
  intro l
  exact ⟨Function.Embedding.ofIsEmpty, fun j => isEmptyElim j⟩

/-- Every admissible selected family supplies a lower bound on the metric. -/
theorem card_le_testableMatchingMetric
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ)
    (J : Finset (Fin m)) (hJ : HasSimultaneousThresholdMatching width B C t J) :
    J.card ≤ testableMatchingMetric width B C t :=
  Finset.le_sup ((mem_thresholdMatchingSubsets width B C t J).mpr hJ)

/-- The finite maximum is attained by an actual admissible subset. -/
theorem testableMatchingMetric_attained
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ) :
    ∃ J, HasSimultaneousThresholdMatching width B C t J ∧
      J.card = testableMatchingMetric width B C t := by
  have hne : (thresholdMatchingSubsets width B C t).Nonempty :=
    ⟨∅, (mem_thresholdMatchingSubsets width B C t ∅).mpr
      (empty_hasSimultaneousThresholdMatching width B C t)⟩
  obtain ⟨J, hJ, hcard⟩ := Finset.sup_mem_of_nonempty
    (f := Finset.card) hne
  exact ⟨J, (mem_thresholdMatchingSubsets width B C t J).mp hJ, hcard⟩

/-- The metric never exceeds the first dictionary's finite width. -/
theorem testableMatchingMetric_le_width
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ) :
    testableMatchingMetric width B C t ≤ m := by
  apply Finset.sup_le
  intro J _
  simpa only [Fintype.card_fin] using Finset.card_le_univ J

/-- Injectivity also bounds the metric by each comparison width. -/
theorem testableMatchingMetric_le_comparison_width
    {ι : Type*} {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ) (l : ι) :
    testableMatchingMetric width B C t ≤ width l := by
  obtain ⟨J, hJ, hcard⟩ := testableMatchingMetric_attained width B C t
  obtain ⟨e, _⟩ := hJ l
  rw [← hcard]
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective e e.injective

/-- With no comparison dictionaries, all columns satisfy the vacuous
matching requirement. Thus the metric equals the first width, for every
threshold. -/
theorem testableMatchingMetric_of_isEmpty
    {ι : Type*} [IsEmpty ι] {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ) (t : ℝ) :
    testableMatchingMetric width B C t = m := by
  apply le_antisymm (testableMatchingMetric_le_width width B C t)
  have h := card_le_testableMatchingMetric width B C t Finset.univ
    (fun l => isEmptyElim l)
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- Signed inner-product recovery calibrates to Euclidean distance with
the exact unit-vector constant. The endpoint `ε=0` is included. -/
theorem unit_atom_distance_le_of_inner_ge {d : ℕ}
    (a b : EuclideanRepresentation d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hinner : 1 - ε ^ 2 / 2 ≤ inner ℝ a b) :
    ‖a - b‖ ≤ ε := by
  have hsq := norm_sub_sq_real a b
  rw [ha, hb] at hsq
  nlinarith [norm_nonneg (a - b)]

/-- Two unit learned atoms within `ε` of a common reference have signed
inner product at least `1-2ε²`. The reference itself need not be normalized
for this distance-based implication. -/
theorem inner_ge_of_common_reference_distance {d : ℕ}
    (a b c : EuclideanRepresentation d) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hbclose : ‖b - a‖ ≤ ε) (hcclose : ‖c - a‖ ≤ ε) :
    1 - 2 * ε ^ 2 ≤ inner ℝ b c := by
  have hdist : ‖b - c‖ ≤ 2 * ε := by
    have htriangle := norm_sub_le_norm_sub_add_norm_sub b a c
    rw [norm_sub_rev a c] at htriangle
    linarith
  have hsq := norm_sub_sq_real b c
  rw [hb, hc] at hsq
  have hdist_sq : ‖b - c‖ ^ 2 ≤ (2 * ε) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hε)).mpr hdist
  nlinarith

/-- Injective recoveries of the same finite reference family provide
simultaneous matchings between actual dictionary columns. Different
comparison dictionaries may have different widths and different embeddings.
Taking the reference family to be an intersection handles separate laws
without identifying their recoverable prefixes. -/
theorem testableMatchingMetric_ge_of_common_reference_distance
    {I ι : Type*} [Fintype I] {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ)
    (a : I → EuclideanRepresentation d)
    (e₀ : I ↪ Fin m) (e : ∀ l, I ↪ Fin (width l))
    (hBunit : ∀ i, ‖representationToEuclidean d (B.col (e₀ i))‖ = 1)
    (hCunit : ∀ l i, ‖representationToEuclidean d ((C l).col (e l i))‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hBclose : ∀ i, ‖representationToEuclidean d (B.col (e₀ i)) - a i‖ ≤ ε)
    (hCclose : ∀ l i, ‖representationToEuclidean d ((C l).col (e l i)) - a i‖ ≤ ε) :
    Fintype.card I ≤ testableMatchingMetric width B C (1 - 2 * ε ^ 2) := by
  classical
  let J : Finset (Fin m) := Finset.univ.map e₀
  let f : I → {j // j ∈ J} := fun i =>
    ⟨e₀ i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i i' hii'
      exact e₀.injective (congrArg Subtype.val hii')
    · intro j
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp j.2
      exact ⟨i, Subtype.ext hi⟩
  let g : I ≃ {j // j ∈ J} := Equiv.ofBijective f hf
  have hmatch : HasSimultaneousThresholdMatching width B C (1 - 2 * ε ^ 2) J := by
    intro l
    refine ⟨g.symm.toEmbedding.trans (e l), ?_⟩
    intro j
    have hj : e₀ (g.symm j) = j.1 := congrArg Subtype.val (g.apply_symm_apply j)
    have hinner := inner_ge_of_common_reference_distance (a (g.symm j))
      (representationToEuclidean d (B.col (e₀ (g.symm j))))
      (representationToEuclidean d ((C l).col (e l (g.symm j))))
      (hBunit _) (hCunit _ _) ε hε (hBclose _) (hCclose _ _)
    change 1 - 2 * ε ^ 2 ≤ inner ℝ
      (representationToEuclidean d (B.col j.1))
      (representationToEuclidean d ((C l).col (e l (g.symm j))))
    rw [hj] at hinner
    exact hinner
  have hcard : J.card = Fintype.card I := by
    simp only [J, Finset.card_map, Finset.card_univ]
  rw [← hcard]
  exact card_le_testableMatchingMetric width B C _ J hmatch

/-- Signed cosine recovery at `1-ε²/2` for each unit reference atom implies
the testable threshold `1-2ε²` between every pair of recovered dictionaries.
This is the calibration used to instantiate the distance-based matching
bound from signed atom recovery. -/
theorem testableMatchingMetric_ge_of_common_reference_inner
    {I ι : Type*} [Fintype I] {d m : ℕ} (width : ι → ℕ)
    (B : Matrix (Fin d) (Fin m) ℝ)
    (C : ∀ l, Matrix (Fin d) (Fin (width l)) ℝ)
    (a : I → EuclideanRepresentation d) (ha : ∀ i, ‖a i‖ = 1)
    (e₀ : I ↪ Fin m) (e : ∀ l, I ↪ Fin (width l))
    (hBunit : ∀ i, ‖representationToEuclidean d (B.col (e₀ i))‖ = 1)
    (hCunit : ∀ l i, ‖representationToEuclidean d ((C l).col (e l i))‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hBinner : ∀ i, 1 - ε ^ 2 / 2 ≤
      inner ℝ (a i) (representationToEuclidean d (B.col (e₀ i))))
    (hCinner : ∀ l i, 1 - ε ^ 2 / 2 ≤
      inner ℝ (a i) (representationToEuclidean d ((C l).col (e l i)))) :
    Fintype.card I ≤ testableMatchingMetric width B C (1 - 2 * ε ^ 2) := by
  apply testableMatchingMetric_ge_of_common_reference_distance width B C a e₀ e
    hBunit hCunit ε hε
  · intro i
    simpa only [norm_sub_rev] using unit_atom_distance_le_of_inner_ge
      (a i) _ (ha i) (hBunit i) ε hε (hBinner i)
  · intro l i
    simpa only [norm_sub_rev] using unit_atom_distance_le_of_inner_ge
      (a i) _ (ha i) (hCunit l i) ε hε (hCinner l i)

end PKG26AtomicFeatures
