import PKG26AtomicFeatures.DictionaryModel

/-!
# Richness on relatively open coordinate sets

The richness definition in `theory.tex` requires only a nonempty relatively
open subset of each coordinate subspace to lie in the closure of the code
range. A finite union of proper linear subspaces cannot contain such a set.
Applying this fact to inverse images of alternative column spans recovers
the full subspace inclusion used by the rigidity argument.
-/

namespace PKG26AtomicFeatures

/-- Every `K`-coordinate subspace has a nonempty relatively open subset
contained in the ambient closure of the code range. -/
def OpenKRich {X : Type*} {M K : ℕ} (z : X → FeatureVector M) : Prop :=
  ∀ coordinates : Finset (Fin M), coordinates.card = K →
    ∃ region : Set (coordinateSpan coordinates),
      IsOpen region ∧ region.Nonempty ∧
        ∀ v ∈ region, (v : FeatureVector M) ∈ closure (Set.range z)

/-- Density in the entire coordinate subspace implies density on a
nonempty relatively open subset. -/
theorem KRich.openKRich {X : Type*} {M K : ℕ} {z : X → FeatureVector M}
    (hrich : KRich (K := K) z) : OpenKRich (K := K) z := by
  intro coordinates hcard
  refine ⟨Set.univ, isOpen_univ, Set.univ_nonempty, ?_⟩
  intro v _
  exact hrich coordinates hcard v.property

/-- A finite family of linear subspaces covering a nonempty open set must
contain the entire ambient finite-dimensional vector space. -/
theorem exists_submodule_eq_top_of_open_cover
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Finite ι]
    (targets : ι → Submodule ℝ V) (region : Set V)
    (hopen : IsOpen region) (hne : region.Nonempty)
    (hcover : region ⊆ ⋃ i, (targets i : Set V)) :
    ∃ i, targets i = ⊤ := by
  classical
  by_contra hnot
  have hproper : ∀ i, targets i ≠ ⊤ := by simpa using hnot
  have hempty : ∀ i, interior (targets i : Set V) = ∅ := by
    intro i
    by_contra hi
    exact hproper i ((targets i).eq_top_of_nonempty_interior'
      (Set.nonempty_iff_ne_empty.mpr hi))
  have hdense : Dense (⋂ i, (targets i : Set V)ᶜ) :=
    dense_iInter_of_isOpen
      (fun i => (targets i).closed_of_finiteDimensional.isOpen_compl)
      (fun i => interior_eq_empty_iff_dense_compl.mp (hempty i))
  obtain ⟨v, hv, havoid⟩ := hdense.inter_open_nonempty region hopen hne
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hv)
  exact (Set.mem_iInter.mp havoid i) hi

/-- Relatively open richness and two factorizations force every whole source
coordinate image into a single alternative span of at most `K'` columns.
The proof uses closed inverse images; it needs no equality between the image
of a closure and the closure of an image. -/
theorem exists_sparse_alternative_subspace_of_openKRich
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hrich : OpenKRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x))
    (coordinates : Finset (Fin M)) (hcoordinates : coordinates.card = K) :
    ∃ support : {s : Finset (Fin M') // s.card ≤ K'},
      Submodule.map matrix.mulVecLin (coordinateSpan coordinates) ≤
        columnSpan alternative support.1 := by
  classical
  let map := matrix.mulVecLin.comp (coordinateSpan coordinates).subtype
  let targets (s : {s : Finset (Fin M') // s.card ≤ K'}) :=
    Submodule.comap map (columnSpan alternative s.1)
  obtain ⟨region, hopen, hne, hregion⟩ := hrich coordinates hcoordinates
  have hclosure := closure_range_subset_iUnion_of_finite_submodules f
    (fun s : {s : Finset (Fin M') // s.card ≤ K'} => columnSpan alternative s.1)
    (range_subset_iUnion_sparse_columnSpan_of_factors alternative alternativeCode f
      halternativeSparse halternativeFactors)
  have hcover : region ⊆ ⋃ s, (targets s : Set (coordinateSpan coordinates)) := by
    intro v hv
    have hcontinuous : Continuous matrix.mulVecLin :=
      LinearMap.continuous_of_finiteDimensional _
    have himage : matrix.mulVecLin (v : FeatureVector M) ∈ closure (Set.range f) := by
      apply closure_mono (s := matrix.mulVecLin '' Set.range z) ?_
        (mem_closure_image hcontinuous.continuousAt (hregion v hv))
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, hfactors x⟩
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hclosure himage)
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨s, hs⟩ := exists_submodule_eq_top_of_open_cover targets region hopen hne hcover
  refine ⟨s, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have hmem : (⟨v, hv⟩ : coordinateSpan coordinates) ∈ targets s := by
    rw [hs]
    exact Submodule.mem_top
  exact hmem

end PKG26AtomicFeatures
