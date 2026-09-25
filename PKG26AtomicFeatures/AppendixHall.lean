import Mathlib.Combinatorics.Hall.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import PKG26AtomicFeatures.DictionaryModel

/-!
# Appendix matching machinery for the atomic-features rigidity argument

Source anchors: `audit/source_archive_surface.tex:1851-1887`.

The archived appendix reduces the dictionary-size bound to a finite family of
supports and then invokes Hall's marriage theorem. This module deliberately
states that finite combinatorial seam without choosing a corrected version of
the source theorem. The Hall endpoint and the source's local-to-global tree
argument are checked here. The density/factorization route now supplies one
alternative span per source coordinate set; the unresolved seam is the
stronger atom-indexed support family that must be compatible across those
coordinate-set choices.
-/

namespace PKG26AtomicFeatures
namespace AppendixHall

variable {Left Right : Type*} [Finite Left] [DecidableEq Right]

/-- The right-neighborhood of a finite collection of left vertices. -/
abbrev neighborhood (supports : Left → Finset Right) (vertices : Finset Left) : Finset Right :=
  vertices.biUnion supports

/-- The exact finite Hall condition for a family of candidate supports. -/
def GlobalHall (supports : Left → Finset Right) : Prop :=
  ∀ vertices : Finset Left, vertices.card ≤ (neighborhood supports vertices).card

/-- A global Hall condition produces an injective choice of one element from
each support. This is the final combinatorial endpoint used by the source
appendix after its local-to-global argument is discharged. -/
theorem exists_injective_representative_of_globalHall
    (supports : Left → Finset Right) (hall : GlobalHall supports) :
    ∃ representative : Left → Right,
      Function.Injective representative ∧
        ∀ vertex, representative vertex ∈ supports vertex := by
  exact (Finset.all_card_le_biUnion_card_iff_existsInjective' supports).mp hall

/-- Hall's endpoint immediately rules out a strictly smaller right vertex set.
This is the exact final cardinality step used in the appendix after constructing
the matching from columns of `A` to columns of the alternative dictionary. -/
theorem left_card_le_right_card_of_globalHall
    [Fintype Left] [Fintype Right]
    (supports : Left → Finset Right) (hall : GlobalHall supports) :
    Fintype.card Left ≤ Fintype.card Right := by
  obtain ⟨representative, hinjective, _⟩ :=
    exists_injective_representative_of_globalHall supports hall
  exact Fintype.card_le_of_injective representative hinjective

/-- Fin-indexed form of the appendix's matching conclusion: a Hall family from
the `M` original atoms to `M'` alternative atoms forces `M ≤ M'`. -/
theorem atom_count_le_alternative_count_of_globalHall
    {M M' : ℕ} (supports : Fin M → Finset (Fin M')) (hall : GlobalHall supports) :
    M ≤ M' := by
  simpa using left_card_le_right_card_of_globalHall supports hall

/-- The linear-algebraic lower-neighborhood step in the source appendix.

If the selected columns of the original dictionary are linearly independent
and lie in the span of the alternative columns indexed by their support
neighborhood, then that neighborhood has at least as many alternative columns.
This formalizes the rank/counting implication used to establish property (i)
of the source proof (`audit/source_archive_surface.tex:1856-1858`). It does
not supply the missing alternative-representation uniqueness premise used
later in that proof. -/
theorem card_le_neighborhood_of_linearIndependent_and_span
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    (a : Left → V) (b : Right → V)
    (supports : Left → Finset Right) (vertices : Finset Left)
    (h_independent : LinearIndependent R (fun i : {i // i ∈ vertices} => a i))
    (h_span : Set.range (fun i : {i // i ∈ vertices} => a i) ⊆
      Submodule.span R (Set.range
        (fun j : {j // j ∈ neighborhood supports vertices} => b j))) :
    vertices.card ≤ (neighborhood supports vertices).card := by
  letI : Fintype {i // i ∈ vertices} := Fintype.ofFinite _
  letI : Fintype {j // j ∈ neighborhood supports vertices} := Fintype.ofFinite _
  letI : Fintype (Set.range
      (fun j : {j // j ∈ neighborhood supports vertices} => b j)) :=
    (Set.finite_range _).fintype
  have h_cardinal := linearIndependent_le_span'
    (fun i : {i // i ∈ vertices} => a i) h_independent
    (Set.range (fun j : {j // j ∈ neighborhood supports vertices} => b j)) h_span
  have h_range : Fintype.card {i // i ∈ vertices} ≤
      Fintype.card (Set.range
        (fun j : {j // j ∈ neighborhood supports vertices} => b j)) := by
    rw [Cardinal.mk_fintype] at h_cardinal
    exact_mod_cast h_cardinal
  calc
    vertices.card = Fintype.card {i // i ∈ vertices} := by simp
    _ ≤ Fintype.card (Set.range
      (fun j : {j // j ∈ neighborhood supports vertices} => b j)) := h_range
    _ ≤ Fintype.card {j // j ∈ neighborhood supports vertices} :=
      Fintype.card_range_le _
    _ = (neighborhood supports vertices).card := by simp

/-- The rank/counting step specialized to dictionary columns. A selected
family of `A`-columns with cardinality below the spark cannot fit into the
span of fewer alternative `B`-columns. -/
theorem card_le_neighborhood_of_spark_and_span
    {d M M' : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M')) (vertices : Finset (Fin M))
    (hcard : vertices.card < spark matrix)
    (hspan : Set.range (selectedColumns matrix vertices) ⊆
      Submodule.span ℝ (Set.range
        (fun j : {j // j ∈ neighborhood supports vertices} =>
          fun row => alternative row j))) :
    vertices.card ≤ (neighborhood supports vertices).card := by
  refine card_le_neighborhood_of_linearIndependent_and_span
    (R := ℝ) (V := RepresentationVector d)
    (fun i row => matrix row i) (fun j row => alternative row j)
    supports vertices ?_ ?_
  · simpa [selectedColumns] using
      linearIndependent_of_card_lt_spark matrix vertices hcard
  · simpa [selectedColumns] using hspan

/-- The appendix's local lower Hall condition follows from `spark(A)=d+1`
when `2*K ≤ d`, provided the selected original columns lie in the span of the
alternative columns named by their support neighborhood. This is the exact
linear-algebra route used in property (i) of the source proof. -/
theorem local_hall_lower_of_spark_general_position
    {d M M' K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hspark : spark matrix = d + 1)
    (h_twoK_le_d : 2 * K ≤ d)
    (hspan : ∀ vertices : Finset (Fin M),
      Set.range (selectedColumns matrix vertices) ⊆
        Submodule.span ℝ (Set.range
          (fun j : {j // j ∈ neighborhood supports vertices} =>
            fun row => alternative row j))) :
    ∀ vertices : Finset (Fin M), vertices.card ≤ 2 * K →
      vertices.card ≤ (neighborhood supports vertices).card := by
  intro vertices hvertices
  apply card_le_neighborhood_of_spark_and_span matrix alternative supports vertices
  · rw [hspark]
    omega
  · exact hspan vertices

/-- Spark-adaptive form of the local lower Hall step.  Independence is needed
only through the chosen cutoff, so the cutoff may be any number strictly below
the actual source spark; no full-spark equality is required. -/
theorem local_hall_lower_up_to_of_spark
    {d M M' cutoff : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hcutoff_lt_spark : cutoff < spark matrix)
    (hspan : ∀ vertices : Finset (Fin M),
      Set.range (selectedColumns matrix vertices) ⊆
        Submodule.span ℝ (Set.range
          (fun j : {j // j ∈ neighborhood supports vertices} =>
            fun row => alternative row j))) :
    ∀ vertices : Finset (Fin M), vertices.card ≤ cutoff →
      vertices.card ≤ (neighborhood supports vertices).card := by
  intro vertices hvertices
  apply card_le_neighborhood_of_spark_and_span matrix alternative supports vertices
  · omega
  · exact hspan vertices

/-- Dimension-aware form of the appendix's local lower Hall step.  Full spark
in ambient dimension `d` supplies the rank/counting inequality through any
cutoff at most `d`; no relation between `2*K` and `d` is needed here. -/
theorem local_hall_lower_up_to_of_spark_general_position
    {d M M' cutoff : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hspark : spark matrix = d + 1)
    (hcutoff_le_d : cutoff ≤ d)
    (hspan : ∀ vertices : Finset (Fin M),
      Set.range (selectedColumns matrix vertices) ⊆
        Submodule.span ℝ (Set.range
          (fun j : {j // j ∈ neighborhood supports vertices} =>
            fun row => alternative row j))) :
    ∀ vertices : Finset (Fin M), vertices.card ≤ cutoff →
      vertices.card ≤ (neighborhood supports vertices).card := by
  intro vertices hvertices
  apply card_le_neighborhood_of_spark_and_span matrix alternative supports vertices
  · rw [hspark]
    omega
  · exact hspan vertices

/-- Atom-indexed alternative supports imply the selected-column span premise
used by the appendix's rank argument. This isolates the exact bridge that a
source proof must supply after choosing supports for individual atoms. -/
theorem selectedColumns_subset_columnSpan_of_atom_supports
    {d M M' : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i))
    (vertices : Finset (Fin M)) :
    Set.range (selectedColumns matrix vertices) ⊆
      columnSpan alternative (neighborhood supports vertices) := by
  rintro column ⟨coordinate, rfl⟩
  apply columnSpan_mono alternative
    (coordinates := supports coordinate.1)
  · intro alternativeCoordinate halternativeCoordinate
    exact Finset.mem_biUnion.mpr
      ⟨coordinate.1, coordinate.2, halternativeCoordinate⟩
  · exact hatom coordinate.1

/-- Atom-support specialization of the spark-adaptive local lower Hall bound. -/
theorem local_hall_lower_up_to_of_spark_and_atom_supports_general
    {d M M' cutoff : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hcutoff_lt_spark : cutoff < spark matrix)
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i)) :
    ∀ vertices : Finset (Fin M), vertices.card ≤ cutoff →
      vertices.card ≤ (neighborhood supports vertices).card := by
  apply local_hall_lower_up_to_of_spark
    matrix alternative supports hcutoff_lt_spark
  intro vertices
  simpa [columnSpan, selectedColumns] using
    selectedColumns_subset_columnSpan_of_atom_supports matrix alternative supports
      hatom vertices

/-- The source's small-set Hall lower bound follows once every original atom
has an alternative support and those supports are used as the Hall family. -/
theorem local_hall_lower_of_spark_and_atom_supports
    {d M M' K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hspark : spark matrix = d + 1)
    (h_twoK_le_d : 2 * K ≤ d)
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i)) :
    ∀ vertices : Finset (Fin M), vertices.card ≤ 2 * K →
      vertices.card ≤ (neighborhood supports vertices).card := by
  apply local_hall_lower_of_spark_general_position matrix alternative supports
    hspark h_twoK_le_d
  intro vertices
  simpa [columnSpan, selectedColumns] using
    selectedColumns_subset_columnSpan_of_atom_supports matrix alternative supports
      hatom vertices

/-- Atom-support specialization of the dimension-aware local lower Hall
bound. -/
theorem local_hall_lower_up_to_of_spark_and_atom_supports
    {d M M' cutoff : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hspark : spark matrix = d + 1)
    (hcutoff_le_d : cutoff ≤ d)
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i)) :
    ∀ vertices : Finset (Fin M), vertices.card ≤ cutoff →
      vertices.card ≤ (neighborhood supports vertices).card := by
  apply local_hall_lower_up_to_of_spark_general_position
    matrix alternative supports hspark hcutoff_le_d
  intro vertices
  simpa [columnSpan, selectedColumns] using
    selectedColumns_subset_columnSpan_of_atom_supports matrix alternative supports
      hatom vertices

/-- A finite union of linear subspaces cannot cover a vector subspace over an
infinite field unless one member already contains that whole subspace.

This is the finite-union step used in the archived appendix when it passes
from coverage of `span(A_S)` by candidate alternative spans to one particular
alternative span containing all of `span(A_S)`. -/
theorem exists_submodule_containing_of_finite_subspace_cover
    {R V ι : Type*} [Field R] [Infinite R] [AddCommGroup V] [Module R V]
    [Finite ι] (source : Submodule R V) (targets : ι → Submodule R V)
    (hcover : (source : Set V) ⊆ ⋃ i, (targets i : Set V)) :
    ∃ i, source ≤ targets i := by
  classical
  let restricted : ι → Subspace R source :=
    fun i => (targets i).comap source.subtype
  have hrestricted_cover : ⋃ i, (restricted i : Set source) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover x.2)
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  obtain ⟨i, htop⟩ :=
    Subspace.exists_eq_top_of_iUnion_eq_univ hrestricted_cover
  refine ⟨i, ?_⟩
  intro x hx
  have hx_restricted : (⟨x, hx⟩ : source) ∈ restricted i := by
    rw [htop]
    exact Submodule.mem_top
  exact hx_restricted

/-- A source `K`-coordinate image is contained in one alternative column span
of support size at most `K'`.  This derives the finite-cover premise used by
the appendix directly from both factorizations and the source K-richness
assumption; it makes no claim about choosing supports for individual original
atoms compatibly across different coordinate sets. -/
theorem exists_sparse_alternative_subspace_containing_coordinate_image
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternativeMatrix : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x, f x = alternativeMatrix.mulVec (alternativeCode x))
    (coordinates : Finset (Fin M)) (hcoordinates : coordinates.card = K) :
    ∃ support : {coordinates : Finset (Fin M') // coordinates.card ≤ K'},
      Submodule.map matrix.mulVecLin (coordinateSpan coordinates) ≤
        columnSpan alternativeMatrix support.1 := by
  apply exists_submodule_containing_of_finite_subspace_cover
    (Submodule.map matrix.mulVecLin (coordinateSpan coordinates))
    (fun support : {coordinates : Finset (Fin M') // coordinates.card ≤ K'} =>
      columnSpan alternativeMatrix support.1)
  simpa only [Submodule.map_coe] using
    image_coordinateSpan_subset_iUnion_sparse_columnSpan_of_kRich_and_factorizations
      matrix z f alternativeMatrix alternativeCode hrich hfactors halternativeSparse
      halternativeFactors coordinates hcoordinates

/-- Spark-local form of part (a).  The source factorization and richness
conditions prove the non-strict sparsity lower bound as soon as one knows
`K < spark matrix`; neither full spark nor a separate ambient-dimension
hypothesis is needed.  A source K-coordinate image has dimension K and is
contained in one alternative span of at most K' columns. -/
theorem source_sparsity_le_alternative_sparsity_of_lt_spark
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternativeMatrix : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hK_lt_spark : K < spark matrix)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x, f x = alternativeMatrix.mulVec (alternativeCode x)) :
    K ≤ K' := by
  classical
  by_cases hK_zero : K = 0
  · omega
  have hK_le_M : K ≤ M := by
    have hspark_bound := spark_le_column_count_succ matrix
    omega
  have hK_univ : K ≤ (Finset.univ : Finset (Fin M)).card := by
    simpa using hK_le_M
  obtain ⟨coordinates, _, hcoordinates_card⟩ :=
    Finset.exists_subset_card_eq hK_univ
  obtain ⟨support, hsupport_image⟩ :=
    exists_sparse_alternative_subspace_containing_coordinate_image
      matrix z f alternativeMatrix alternativeCode hrich hfactors halternativeSparse
      halternativeFactors coordinates hcoordinates_card
  let localSupports : Fin M → Finset (Fin M') := fun _ => support.1
  have hcoordinates_nonempty : coordinates.Nonempty := by
    apply Finset.card_ne_zero.mp
    rw [hcoordinates_card]
    exact hK_zero
  have hneighborhood : neighborhood localSupports coordinates = support.1 := by
    change coordinates.biUnion localSupports = support.1
    apply Finset.Subset.antisymm
    · intro alternativeCoordinate halternativeCoordinate
      obtain ⟨i, _, hi_support⟩ := Finset.mem_biUnion.mp halternativeCoordinate
      simpa [localSupports] using hi_support
    · intro alternativeCoordinate halternativeCoordinate
      obtain ⟨i, hi⟩ := hcoordinates_nonempty
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, by simpa [localSupports] using halternativeCoordinate⟩
  have hselected_span : Set.range (selectedColumns matrix coordinates) ⊆
      columnSpan alternativeMatrix support.1 := by
    rintro column ⟨coordinate, rfl⟩
    apply hsupport_image
    refine ⟨Pi.single coordinate.1 (1 : ℝ),
      canonicalVector_mem_coordinateSpan coordinates coordinate.2, ?_⟩
    ext row
    simp [selectedColumns]
  have hspan : Set.range (selectedColumns matrix coordinates) ⊆
      Submodule.span ℝ (Set.range
        (fun j : {j // j ∈ neighborhood localSupports coordinates} =>
          fun row => alternativeMatrix row j)) := by
    rw [hneighborhood]
    simpa [columnSpan, selectedColumns] using hselected_span
  have hcard_lt_spark : coordinates.card < spark matrix := by
    simpa [hcoordinates_card] using hK_lt_spark
  have hcard_le_support : coordinates.card ≤ support.1.card := by
    simpa [hneighborhood] using
      card_le_neighborhood_of_spark_and_span matrix alternativeMatrix localSupports
        coordinates hcard_lt_spark hspan
  calc
    K = coordinates.card := hcoordinates_card.symm
    _ ≤ support.1.card := hcard_le_support
    _ ≤ K' := support.2

/-- Full-spark specialization of part (a).  Under `spark matrix = d+1`, the
sharp ambient numerical premise is `K ≤ d` (not the unnecessarily strict
`K < d`). -/
theorem source_sparsity_le_alternative_sparsity
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternativeMatrix : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1)
    (hK_le_d : K ≤ d)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternativeMatrix.mulVec (alternativeCode x)) :
    K ≤ K' := by
  apply source_sparsity_le_alternative_sparsity_of_lt_spark
    matrix z f alternativeMatrix alternativeCode
  · rw [hspark]
    omega
  · exact hrich
  · exact hfactors
  · exact halternativeSparse
  · exact halternativeFactors

/-- Any failure of Hall has a minimum-cardinality witness, so every strictly
smaller left-vertex set satisfies Hall. This is the first minimal-violator
reduction in the source appendix (`audit/source_archive_surface.tex:1867-1869`). -/
theorem exists_card_minimal_hall_violator
    (supports : Left → Finset Right) (hnot : ¬ GlobalHall supports) :
    ∃ C : Finset Left,
      (neighborhood supports C).card < C.card ∧
      ∀ D : Finset Left, D.card < C.card →
        D.card ≤ (neighborhood supports D).card := by
  classical
  letI : Fintype Left := Fintype.ofFinite Left
  rw [GlobalHall] at hnot
  push Not at hnot
  let violators := Finset.univ.powerset.filter
    (fun C : Finset Left => (neighborhood supports C).card < C.card)
  have hviolators : violators.Nonempty := by
    obtain ⟨C, hC⟩ := hnot
    exact ⟨C, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ C), hC⟩⟩
  let cards := violators.image Finset.card
  have hcards : cards.Nonempty := by
    obtain ⟨C, hC⟩ := hviolators
    exact ⟨C.card, Finset.mem_image.mpr ⟨C, hC, rfl⟩⟩
  obtain ⟨C, hCviolator, hCcard⟩ := Finset.mem_image.mp
    (Finset.min'_mem cards hcards)
  refine ⟨C, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hCviolator).2
  · intro D hDsmaller
    by_contra hDhall
    have hDviolator : (neighborhood supports D).card < D.card :=
      Nat.lt_of_not_ge hDhall
    have hDmem : D ∈ violators := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ D), hDviolator⟩
    have hmin : C.card ≤ D.card := by
      rw [hCcard]
      exact Finset.min'_le cards D.card
        (Finset.mem_image.mpr ⟨D, hDmem, rfl⟩)
    exact (Nat.not_le_of_gt hDsmaller) hmin

omit [Finite Left] in
/-- A minimum-cardinality Hall violator has deficiency exactly one. This is
the cardinality fact used immediately after the minimal-violator choice in
the source appendix (`audit/source_archive_surface.tex:1867-1870`). -/
theorem card_neighborhood_add_one_eq_of_card_minimal_hall_violator
    (supports : Left → Finset Right) (C : Finset Left)
    (hbad : (neighborhood supports C).card < C.card)
    (hminimal : ∀ D : Finset Left, D.card < C.card →
      D.card ≤ (neighborhood supports D).card) :
    (neighborhood supports C).card + 1 = C.card := by
  classical
  have hCpos : 0 < C.card := by
    exact lt_of_le_of_lt (Nat.zero_le _) hbad
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hCpos
  have herase_smaller : (C.erase r).card < C.card := by
    rw [Finset.card_erase_of_mem hr]
    omega
  have herase_hall := hminimal (C.erase r) herase_smaller
  have hneighborhood_subset : neighborhood supports (C.erase r) ⊆
      neighborhood supports C := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨x, Finset.erase_subset _ _ hx, hy⟩
  have hC_le : C.card ≤ (neighborhood supports C).card + 1 := by
    rw [← Finset.card_erase_add_one hr]
    exact Nat.succ_le_succ
      (herase_hall.trans (Finset.card_le_card hneighborhood_subset))
  exact Nat.le_antisymm (Nat.succ_le_iff.mpr hbad) hC_le

omit [Finite Left] in
/-- The source lower-neighborhood condition forces every Hall violator to
have more than `2*K` vertices. -/
theorem succ_two_mul_le_card_of_hall_violator
    (supports : Left → Finset Right) (K : ℕ) (C : Finset Left)
    (hlower : ∀ vertices : Finset Left, vertices.card ≤ 2 * K →
      vertices.card ≤ (neighborhood supports vertices).card)
    (hbad : (neighborhood supports C).card < C.card) :
    2 * K + 1 ≤ C.card := by
  apply Nat.succ_le_iff.mpr
  by_contra hsmall
  exact (Nat.not_le_of_gt hbad) (hlower C (Nat.le_of_not_gt hsmall))

omit [Finite Left] in
/-- A local Hall lower bound through an arbitrary cardinality cutoff forces
every Hall violator to be strictly larger than that cutoff.  This is the
dimension-aware form of `succ_two_mul_le_card_of_hall_violator`; taking the
cutoff to be `min (2*K) d` is what permits the appendix argument to retain a
sharp dimension-limited conclusion when `2*K > d`. -/
theorem succ_cutoff_le_card_of_hall_violator
    (supports : Left → Finset Right) (cutoff : ℕ) (C : Finset Left)
    (hlower : ∀ vertices : Finset Left, vertices.card ≤ cutoff →
      vertices.card ≤ (neighborhood supports vertices).card)
    (hbad : (neighborhood supports C).card < C.card) :
    cutoff + 1 ≤ C.card := by
  apply Nat.succ_le_iff.mpr
  by_contra hsmall
  exact (Nat.not_le_of_gt hbad) (hlower C (Nat.le_of_not_gt hsmall))

omit [Finite Left] in
/-- Hall's theorem restricted to one finite left-vertex set. This supplies the
matching on `C \ {r}` used by the source's minimal-violator construction. -/
theorem exists_injective_representative_of_hall_on
    (supports : Left → Finset Right) (C : Finset Left)
    (hall_on : ∀ D : Finset Left, D ⊆ C →
      D.card ≤ (neighborhood supports D).card) :
    ∃ representative : {i // i ∈ C} → Right,
      Function.Injective representative ∧
        ∀ vertex : {i // i ∈ C}, representative vertex ∈ supports vertex := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun i : {i // i ∈ C} => supports i)).mp
  intro vertices
  rw [← Finset.image_biUnion]
  rw [← Finset.card_image_of_injective vertices Subtype.val_injective]
  apply hall_on (vertices.image Subtype.val)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact y.2

omit [Finite Left] in
/-- Removing any one vertex from a minimum-cardinality Hall violator leaves
the same right neighborhood. This exposes the surjective matching target used
in the source alternating-tree construction. -/
theorem neighborhood_erase_eq_of_card_minimal_hall_violator
    [DecidableEq Left]
    (supports : Left → Finset Right) (C : Finset Left)
    (hbad : (neighborhood supports C).card < C.card)
    (hminimal : ∀ D : Finset Left, D.card < C.card →
      D.card ≤ (neighborhood supports D).card)
    {r : Left} (hr : r ∈ C) :
    neighborhood supports (C.erase r) = neighborhood supports C := by
  classical
  have hdeficiency := card_neighborhood_add_one_eq_of_card_minimal_hall_violator
    supports C hbad hminimal
  have herase_smaller : (C.erase r).card < C.card := by
    rw [Finset.card_erase_of_mem hr]
    omega
  have herase_hall := hminimal (C.erase r) herase_smaller
  have hneighborhood_subset : neighborhood supports (C.erase r) ⊆
      neighborhood supports C := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨x, Finset.erase_subset _ _ hx, hy⟩
  apply Finset.eq_of_subset_of_card_le hneighborhood_subset
  have herase_card : (C.erase r).card = (neighborhood supports C).card := by
    rw [Finset.card_erase_of_mem hr]
    omega
  exact herase_card.symm.trans_le herase_hall

omit [Finite Left] in
/-- A minimum-cardinality Hall violator admits the source appendix's bijective
matching from `C \ {r}` onto `N(C)`. The theorem records only the finite
matching fact; the later alternating-tree construction remains separate. -/
theorem exists_bijective_representative_of_erase_of_card_minimal_hall_violator
    [DecidableEq Left]
    (supports : Left → Finset Right) (C : Finset Left)
    (hbad : (neighborhood supports C).card < C.card)
    (hminimal : ∀ D : Finset Left, D.card < C.card →
      D.card ≤ (neighborhood supports D).card)
    {r : Left} (hr : r ∈ C) :
    ∃ representative : {i // i ∈ C.erase r} →
      {j // j ∈ neighborhood supports C},
      Function.Bijective representative ∧
        ∀ vertex : {i // i ∈ C.erase r},
          (representative vertex : Right) ∈ supports vertex := by
  classical
  have herase_smaller : (C.erase r).card < C.card := by
    rw [Finset.card_erase_of_mem hr]
    omega
  obtain ⟨f, hfinjective, hfmem⟩ :=
    exists_injective_representative_of_hall_on supports (C.erase r) (by
      intro D hD
      exact hminimal D (lt_of_le_of_lt (Finset.card_le_card hD) herase_smaller))
  have hf_neighborhood (vertex : {i // i ∈ C.erase r}) :
      f vertex ∈ neighborhood supports C := by
    exact Finset.mem_biUnion.mpr
      ⟨vertex, Finset.erase_subset _ _ vertex.2, hfmem vertex⟩
  let representative : {i // i ∈ C.erase r} →
      {j // j ∈ neighborhood supports C} :=
    fun vertex => ⟨f vertex, hf_neighborhood vertex⟩
  have hrepresentative_injective : Function.Injective representative := by
    intro x y hxy
    apply hfinjective
    exact congrArg Subtype.val hxy
  have hdeficiency := card_neighborhood_add_one_eq_of_card_minimal_hall_violator
    supports C hbad hminimal
  have hcard : Fintype.card {i // i ∈ C.erase r} =
      Fintype.card {j // j ∈ neighborhood supports C} := by
    simp only [Fintype.card_coe]
    rw [Finset.card_erase_of_mem hr]
    omega
  refine ⟨representative,
    (Fintype.bijective_iff_injective_and_card representative).mpr
      ⟨hrepresentative_injective, hcard⟩, ?_⟩
  intro vertex
  exact hfmem vertex

omit [Finite Left] in
/-- Every proper subset of a cardinality-minimal Hall violator that contains
the distinguished root has an outgoing edge in the source's matched-support
relation. This is the extension step that makes the alternating tree span the
violator: otherwise the matching inverse embeds the subset's neighborhood in
the subset with the root removed, contradicting minimality. -/
theorem exists_outgoing_from_proper_subset_of_card_minimal_hall_violator
    [DecidableEq Left]
    (supports : Left → Finset Right) (C S : Finset Left)
    (hminimal : ∀ D : Finset Left, D.card < C.card →
      D.card ≤ (neighborhood supports D).card)
    {r : Left} (hrS : r ∈ S)
    (hSC : S ⊆ C) (hSlt : S.card < C.card)
    (matching : {i // i ∈ C.erase r} → {j // j ∈ neighborhood supports C})
    (hmatching_bijective : Function.Bijective matching) :
    ∃ i, i ∈ S ∧ ∃ j : {j // j ∈ C.erase r},
      (j : Left) ∉ S ∧ (matching j : Right) ∈ supports i := by
  classical
  by_contra hno
  push Not at hno
  have hneighborhood_subset : neighborhood supports S ⊆ neighborhood supports C := by
    intro y hy
    obtain ⟨i, hiS, hyi⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨i, hSC hiS, hyi⟩
  have hsurjective_on_neighborhood : ∀ y : {y // y ∈ neighborhood supports S},
      ∃ j : {j // j ∈ C.erase r}, matching j = ⟨y, hneighborhood_subset y.2⟩ := by
    intro y
    exact hmatching_bijective.2 ⟨y, hneighborhood_subset y.2⟩
  let inverse : {y // y ∈ neighborhood supports S} → {j // j ∈ C.erase r} :=
    fun y => Classical.choose (hsurjective_on_neighborhood y)
  have hinverse_spec (y : {y // y ∈ neighborhood supports S}) :
      matching (inverse y) = ⟨y, hneighborhood_subset y.2⟩ :=
    Classical.choose_spec (hsurjective_on_neighborhood y)
  have hinverse_mem (y : {y // y ∈ neighborhood supports S}) :
      (inverse y : Left) ∈ S := by
    obtain ⟨i, hiS, hyi⟩ := Finset.mem_biUnion.mp y.2
    by_contra hinverse_not_mem
    exact hno i hiS (inverse y) hinverse_not_mem (by
      rw [hinverse_spec y]
      exact hyi)
  have hinverse_injective : Function.Injective inverse := by
    intro y₁ y₂ h
    apply Subtype.ext
    have hmatching : matching (inverse y₁) = matching (inverse y₂) := by rw [h]
    have hvalue : (y₁ : Right) = y₂ := by
      have := congrArg Subtype.val hmatching
      simpa only [hinverse_spec] using this
    exact hvalue
  let inverseOnS : {y // y ∈ neighborhood supports S} → {j // j ∈ S.erase r} :=
    fun y => ⟨inverse y, Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp (inverse y).2).1, hinverse_mem y⟩⟩
  have hinverseOnS_injective : Function.Injective inverseOnS := by
    intro y₁ y₂ h
    apply hinverse_injective
    apply Subtype.ext
    exact congrArg (fun t : {j // j ∈ S.erase r} => (t : Left)) h
  have hcard : (neighborhood supports S).card ≤ (S.erase r).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective inverseOnS hinverseOnS_injective
  have hminimalS := hminimal S hSlt
  rw [Finset.card_erase_of_mem hrS] at hcard
  have hS_pos : 0 < S.card := Finset.card_pos.mpr ⟨r, hrS⟩
  have hcard_succ : (neighborhood supports S).card + 1 ≤ S.card :=
    (Nat.le_sub_iff_add_le (by omega)).mp hcard
  have hcontr : S.card + 1 ≤ S.card :=
    (Nat.succ_le_succ hminimalS).trans hcard_succ
  exact (Nat.not_succ_le_self S.card) hcontr

omit [Finite Left] in
/-- The outgoing-edge property builds a finite two-colored rooted tree prefix
without introducing an external graph representation. Every non-root vertex
in either color class has a matched-support edge to the opposite class. -/
theorem exists_bicolored_prefix_of_card_minimal_hall_violator
    [DecidableEq Left]
    (supports : Left → Finset Right) (C : Finset Left)
    (hminimal : ∀ D : Finset Left, D.card < C.card →
      D.card ≤ (neighborhood supports D).card)
    {r : Left} (hr : r ∈ C)
    (matching : {i // i ∈ C.erase r} → {j // j ∈ neighborhood supports C})
    (hmatching_bijective : Function.Bijective matching)
    (n : ℕ) (hn : n + 1 ≤ C.card) :
    ∃ P Q : Finset Left,
      P ⊆ C ∧ Q ⊆ C ∧ Disjoint P Q ∧ r ∈ P ∧ P.card + Q.card = n + 1 ∧
      (∀ v : {v // v ∈ C.erase r}, (v : Left) ∈ P →
        ∃ q, q ∈ Q ∧ (matching v : Right) ∈ supports q) ∧
      (∀ v : {v // v ∈ C.erase r}, (v : Left) ∈ Q →
        ∃ p, p ∈ P ∧ (matching v : Right) ∈ supports p) := by
  classical
  induction n with
  | zero =>
      refine ⟨{r}, ∅, ?_, ?_, ?_, Finset.mem_singleton_self r, by simp, ?_, ?_⟩
      · exact Finset.singleton_subset_iff.mpr hr
      · exact Finset.empty_subset _
      · exact Finset.disjoint_empty_right _
      · intro v hv
        have hvr : (v : Left) ≠ r := (Finset.mem_erase.mp v.2).1
        exact False.elim (hvr (Finset.mem_singleton.mp hv))
      · intro v hv
        simp at hv
  | succ n ih =>
      have hn_ih : n + 1 ≤ C.card := by omega
      obtain ⟨P, Q, hPC, hQC, hdisjoint, hrP, hcard, hPcolor, hQcolor⟩ := ih hn_ih
      let S := P ∪ Q
      have hrS : r ∈ S := Finset.mem_union_left _ hrP
      have hSC : S ⊆ C := Finset.union_subset hPC hQC
      have hS_card : S.card = n + 1 := by
        dsimp [S]
        rw [Finset.card_union_of_disjoint hdisjoint]
        exact hcard
      have hSlt : S.card < C.card := by
        rw [hS_card]
        omega
      obtain ⟨i, hiS, j, hjS, hmatch⟩ :=
        exists_outgoing_from_proper_subset_of_card_minimal_hall_violator
          supports C S hminimal hrS hSC hSlt matching hmatching_bijective
      rcases Finset.mem_union.mp hiS with hiP | hiQ
      · refine ⟨P, insert (j : Left) Q, hPC, ?_, ?_, hrP, ?_, ?_, ?_⟩
        · exact Finset.insert_subset (j.2 |> Finset.mem_erase.mp |> And.right) hQC
        · apply Finset.disjoint_left.mpr
          intro x hxP hxQ
          rcases Finset.mem_insert.mp hxQ with hxj | hxQ
          · subst x
            exact hjS (Finset.mem_union_left _ hxP)
          · exact Finset.disjoint_left.mp hdisjoint hxP hxQ
        · have hjQ : (j : Left) ∉ Q := by
            intro hjQ
            exact hjS (Finset.mem_union_right _ hjQ)
          simp [hjQ]
          omega
        · intro v hvP
          obtain ⟨q, hqQ, hqmatch⟩ := hPcolor v hvP
          exact ⟨q, Finset.mem_insert_of_mem hqQ, hqmatch⟩
        · intro v hvQ
          rcases Finset.mem_insert.mp hvQ with hvj | hvQ
          · have hv_eq : v = j := Subtype.ext hvj
            subst v
            exact ⟨i, hiP, hmatch⟩
          · exact hQcolor v hvQ
      · refine ⟨insert (j : Left) P, Q, ?_, hQC, ?_, Finset.mem_insert_of_mem hrP, ?_, ?_, ?_⟩
        · exact Finset.insert_subset (j.2 |> Finset.mem_erase.mp |> And.right) hPC
        · apply Finset.disjoint_left.mpr
          intro x hxP hxQ
          rcases Finset.mem_insert.mp hxP with hxj | hxP
          · subst x
            exact hjS (Finset.mem_union_right _ hxQ)
          · exact Finset.disjoint_left.mp hdisjoint hxP hxQ
        · have hjP : (j : Left) ∉ P := by
            intro hjP
            exact hjS (Finset.mem_union_left _ hjP)
          simp [hjP]
          omega
        · intro v hvP
          rcases Finset.mem_insert.mp hvP with hvj | hvP
          · have hv_eq : v = j := Subtype.ext hvj
            subst v
            exact ⟨i, hiQ, hmatch⟩
          · exact hPcolor v hvP
        · intro v hvQ
          obtain ⟨p, hpP, hpmatch⟩ := hQcolor v hvQ
          exact ⟨p, Finset.mem_insert_of_mem hpP, hpmatch⟩

/-- The finite local-Hall bridge asserted by the archived appendix.

The intended application takes `width = K'`, with `width + 1 ≤ 2*K` supplied
by `K' < 2K`. The lower bound is the source's property (i), from linear
independence of every collection of at most `2*K` original columns; the upper
bound is the source's property (ii), from the sparse support construction.
This makes explicit why a corrected theorem route needs the source's missing
`2*K ≤ d` independence range. Its proof must formalize the source's minimal Hall violator,
matching, and alternating-tree argument; that finite proof-support bridge is
fully checked below, but no source theorem currently depends on it.
-/
theorem local_hall_implies_global
    (supports : Left → Finset Right) (K width : ℕ)
    (hwidth : width + 1 ≤ 2 * K)
    (hlower : ∀ vertices : Finset Left, vertices.card ≤ 2 * K →
      vertices.card ≤ (neighborhood supports vertices).card)
    (hupper : ∀ vertices : Finset Left, vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ width) :
    GlobalHall supports := by
  classical
  by_contra hglobal
  obtain ⟨C, hbad, hminimal⟩ :=
    exists_card_minimal_hall_violator supports hglobal
  have hdeficiency :=
    card_neighborhood_add_one_eq_of_card_minimal_hall_violator
      supports C hbad hminimal
  have hC_large := succ_two_mul_le_card_of_hall_violator supports K C hlower hbad
  have hC_pos : 0 < C.card := by omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hC_pos
  have hneighborhood_erase :=
    neighborhood_erase_eq_of_card_minimal_hall_violator
      supports C hbad hminimal hr
  obtain ⟨matching, hmatching_bijective, hmatching_mem⟩ :=
    exists_bijective_representative_of_erase_of_card_minimal_hall_violator
      supports C hbad hminimal hr
  have hwidth_strict : width < 2 * K := by omega
  obtain ⟨P, Q, hPC, hQC, hdisjoint, hrP, hcard, hPcolor, hQcolor⟩ :=
    exists_bicolored_prefix_of_card_minimal_hall_violator
      supports C hminimal hr matching hmatching_bijective (2 * K) hC_large
  let V := (P.erase r) ∪ Q
  have hV_disjoint : Disjoint (P.erase r) Q := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxQ
    exact Finset.disjoint_left.mp hdisjoint (Finset.erase_subset _ _ hxP) hxQ
  have hV_card : V.card = 2 * K := by
    dsimp [V]
    rw [Finset.card_union_of_disjoint hV_disjoint, Finset.card_erase_of_mem hrP]
    have hP_pos : 0 < P.card := Finset.card_pos.mpr ⟨r, hrP⟩
    omega
  have hQ_not_r {v : Left} (hvQ : v ∈ Q) : v ≠ r := by
    intro hvr
    subst v
    exact Finset.disjoint_left.mp hdisjoint hrP hvQ
  have hvertexC_mem (v : {v // v ∈ V}) : (v : Left) ∈ C.erase r := by
    rcases Finset.mem_union.mp v.2 with hvP | hvQ
    · exact Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hvP).1, hPC (Finset.mem_erase.mp hvP).2⟩
    · exact Finset.mem_erase.mpr ⟨hQ_not_r hvQ, hQC hvQ⟩
  let vertexC : {v // v ∈ V} → {v // v ∈ C.erase r} :=
    fun v => ⟨v, hvertexC_mem v⟩
  have hmatchP_mem (v : {v // v ∈ V}) :
      (matching (vertexC v) : Right) ∈ neighborhood supports P := by
    rcases Finset.mem_union.mp v.2 with hvP | hvQ
    · exact Finset.mem_biUnion.mpr
        ⟨v, (Finset.mem_erase.mp hvP).2, hmatching_mem (vertexC v)⟩
    · obtain ⟨p, hpP, hpmatch⟩ := hQcolor (vertexC v) hvQ
      exact Finset.mem_biUnion.mpr ⟨p, hpP, hpmatch⟩
  have hmatchQ_mem (v : {v // v ∈ V}) :
      (matching (vertexC v) : Right) ∈ neighborhood supports Q := by
    rcases Finset.mem_union.mp v.2 with hvP | hvQ
    · obtain ⟨q, hqQ, hqmatch⟩ := hPcolor (vertexC v) (Finset.mem_erase.mp hvP).2
      exact Finset.mem_biUnion.mpr ⟨q, hqQ, hqmatch⟩
    · exact Finset.mem_biUnion.mpr ⟨v, hvQ, hmatching_mem (vertexC v)⟩
  let matchP : {v // v ∈ V} → {y // y ∈ neighborhood supports P} :=
    fun v => ⟨matching (vertexC v), hmatchP_mem v⟩
  let matchQ : {v // v ∈ V} → {y // y ∈ neighborhood supports Q} :=
    fun v => ⟨matching (vertexC v), hmatchQ_mem v⟩
  have hmatchP_injective : Function.Injective matchP := by
    intro v w h
    apply Subtype.ext
    have hmatching_eq : matching (vertexC v) = matching (vertexC w) := by
      apply Subtype.ext
      exact congrArg (fun y : {y // y ∈ neighborhood supports P} => (y : Right)) h
    have hvertex_eq := hmatching_bijective.1 hmatching_eq
    exact congrArg (fun t : {v // v ∈ C.erase r} => (t : Left)) hvertex_eq
  have hmatchQ_injective : Function.Injective matchQ := by
    intro v w h
    apply Subtype.ext
    have hmatching_eq : matching (vertexC v) = matching (vertexC w) := by
      apply Subtype.ext
      exact congrArg (fun y : {y // y ∈ neighborhood supports Q} => (y : Right)) h
    have hvertex_eq := hmatching_bijective.1 hmatching_eq
    exact congrArg (fun t : {v // v ∈ C.erase r} => (t : Left)) hvertex_eq
  have hP_lower : 2 * K ≤ (neighborhood supports P).card := by
    have hcard : V.card ≤ (neighborhood supports P).card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective matchP hmatchP_injective
    omega
  have hQ_lower : 2 * K ≤ (neighborhood supports Q).card := by
    have hcard : V.card ≤ (neighborhood supports Q).card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective matchQ hmatchQ_injective
    omega
  have hsmall : P.card ≤ K ∨ Q.card ≤ K := by omega
  rcases hsmall with hPsmall | hQsmall
  · have hP_upper := hupper P hPsmall
    omega
  · have hQ_upper := hupper Q hQsmall
    omega

/-- Dimension-aware local-to-global Hall bridge.

The lower Hall condition need only hold through `cutoff`, the neighborhood
width must be strictly below `cutoff`, and the smaller color class of a
`cutoff`-edge tree must still fit inside a source support of size `K`.  The
last requirement is exactly `cutoff ≤ 2*K`.  Thus the source application can
take `cutoff = min (2*K) d`: full spark supplies independence through `d`,
while K-richness supplies the neighborhood upper bound through `K`.

The adjustable cutoff separates the independence range from the size of
source supports, under the stated compatibility of atom supports. -/
theorem local_hall_implies_global_up_to
    (supports : Left → Finset Right) (K width cutoff : ℕ)
    (hcutoff : cutoff ≤ 2 * K)
    (hwidth : width + 1 ≤ cutoff)
    (hlower : ∀ vertices : Finset Left, vertices.card ≤ cutoff →
      vertices.card ≤ (neighborhood supports vertices).card)
    (hupper : ∀ vertices : Finset Left, vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ width) :
    GlobalHall supports := by
  classical
  by_contra hglobal
  obtain ⟨C, hbad, hminimal⟩ :=
    exists_card_minimal_hall_violator supports hglobal
  have hC_large :=
    succ_cutoff_le_card_of_hall_violator supports cutoff C hlower hbad
  have hC_pos : 0 < C.card := by omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hC_pos
  obtain ⟨matching, hmatching_bijective, hmatching_mem⟩ :=
    exists_bijective_representative_of_erase_of_card_minimal_hall_violator
      supports C hbad hminimal hr
  obtain ⟨P, Q, hPC, hQC, hdisjoint, hrP, hcard, hPcolor, hQcolor⟩ :=
    exists_bicolored_prefix_of_card_minimal_hall_violator
      supports C hminimal hr matching hmatching_bijective cutoff hC_large
  let V := (P.erase r) ∪ Q
  have hV_disjoint : Disjoint (P.erase r) Q := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxQ
    exact Finset.disjoint_left.mp hdisjoint (Finset.erase_subset _ _ hxP) hxQ
  have hV_card : V.card = cutoff := by
    dsimp [V]
    rw [Finset.card_union_of_disjoint hV_disjoint, Finset.card_erase_of_mem hrP]
    have hP_pos : 0 < P.card := Finset.card_pos.mpr ⟨r, hrP⟩
    omega
  have hQ_not_r {v : Left} (hvQ : v ∈ Q) : v ≠ r := by
    intro hvr
    subst v
    exact Finset.disjoint_left.mp hdisjoint hrP hvQ
  have hvertexC_mem (v : {v // v ∈ V}) : (v : Left) ∈ C.erase r := by
    rcases Finset.mem_union.mp v.2 with hvP | hvQ
    · exact Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hvP).1, hPC (Finset.mem_erase.mp hvP).2⟩
    · exact Finset.mem_erase.mpr ⟨hQ_not_r hvQ, hQC hvQ⟩
  let vertexC : {v // v ∈ V} → {v // v ∈ C.erase r} :=
    fun v => ⟨v, hvertexC_mem v⟩
  have hmatchP_mem (v : {v // v ∈ V}) :
      (matching (vertexC v) : Right) ∈ neighborhood supports P := by
    rcases Finset.mem_union.mp v.2 with hvP | hvQ
    · exact Finset.mem_biUnion.mpr
        ⟨v, (Finset.mem_erase.mp hvP).2, hmatching_mem (vertexC v)⟩
    · obtain ⟨p, hpP, hpmatch⟩ := hQcolor (vertexC v) hvQ
      exact Finset.mem_biUnion.mpr ⟨p, hpP, hpmatch⟩
  have hmatchQ_mem (v : {v // v ∈ V}) :
      (matching (vertexC v) : Right) ∈ neighborhood supports Q := by
    rcases Finset.mem_union.mp v.2 with hvP | hvQ
    · obtain ⟨q, hqQ, hqmatch⟩ := hPcolor (vertexC v) (Finset.mem_erase.mp hvP).2
      exact Finset.mem_biUnion.mpr ⟨q, hqQ, hqmatch⟩
    · exact Finset.mem_biUnion.mpr ⟨v, hvQ, hmatching_mem (vertexC v)⟩
  let matchP : {v // v ∈ V} → {y // y ∈ neighborhood supports P} :=
    fun v => ⟨matching (vertexC v), hmatchP_mem v⟩
  let matchQ : {v // v ∈ V} → {y // y ∈ neighborhood supports Q} :=
    fun v => ⟨matching (vertexC v), hmatchQ_mem v⟩
  have hmatchP_injective : Function.Injective matchP := by
    intro v w h
    apply Subtype.ext
    have hmatching_eq : matching (vertexC v) = matching (vertexC w) := by
      apply Subtype.ext
      exact congrArg (fun y : {y // y ∈ neighborhood supports P} => (y : Right)) h
    have hvertex_eq := hmatching_bijective.1 hmatching_eq
    exact congrArg (fun t : {v // v ∈ C.erase r} => (t : Left)) hvertex_eq
  have hmatchQ_injective : Function.Injective matchQ := by
    intro v w h
    apply Subtype.ext
    have hmatching_eq : matching (vertexC v) = matching (vertexC w) := by
      apply Subtype.ext
      exact congrArg (fun y : {y // y ∈ neighborhood supports Q} => (y : Right)) h
    have hvertex_eq := hmatching_bijective.1 hmatching_eq
    exact congrArg (fun t : {v // v ∈ C.erase r} => (t : Left)) hvertex_eq
  have hP_lower : cutoff ≤ (neighborhood supports P).card := by
    have hcard' : V.card ≤ (neighborhood supports P).card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective matchP hmatchP_injective
    omega
  have hQ_lower : cutoff ≤ (neighborhood supports Q).card := by
    have hcard' : V.card ≤ (neighborhood supports Q).card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective matchQ hmatchQ_injective
    omega
  have hsmall : P.card ≤ K ∨ Q.card ≤ K := by omega
  rcases hsmall with hPsmall | hQsmall
  · have hP_upper := hupper P hPsmall
    omega
  · have hQ_upper := hupper Q hQsmall
    omega

/-- The complete finite dictionary-counting consequence of the appendix.

Given the source's explicit rank/span lower condition and its support upper
condition, no alternative dictionary with a support width strictly below
`2*K` can have fewer atoms. The theorem packages only the finite seam; the
source-facing route must still derive an atom-compatible support family and
its small-set neighborhood upper bound from the stated factorization
hypotheses. -/
theorem atom_count_le_alternative_count_of_spark_and_local_supports
    {d M M' K width : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hspark : spark matrix = d + 1)
    (h_twoK_le_d : 2 * K ≤ d)
    (hwidth : width + 1 ≤ 2 * K)
    (hspan : ∀ vertices : Finset (Fin M),
      Set.range (selectedColumns matrix vertices) ⊆
        Submodule.span ℝ (Set.range
          (fun j : {j // j ∈ neighborhood supports vertices} =>
            fun row => alternative row j)))
    (hupper : ∀ vertices : Finset (Fin M), vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ width) :
    M ≤ M' := by
  apply atom_count_le_alternative_count_of_globalHall supports
  apply local_hall_implies_global supports K width hwidth
  · exact local_hall_lower_of_spark_general_position matrix alternative supports
      hspark h_twoK_le_d hspan
  · exact hupper

/-- A more source-shaped package of the appendix's counting endpoint. Once an
atom-indexed alternative support family has both its stated span membership
and the small-set neighborhood upper bound, spark general position and the
dimension condition force the alternative dictionary to have at least as many
atoms. -/
theorem atom_count_le_alternative_count_of_spark_and_atom_supports
    {d M M' K width : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (hspark : spark matrix = d + 1)
    (h_twoK_le_d : 2 * K ≤ d)
    (hwidth : width + 1 ≤ 2 * K)
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i))
    (hupper : ∀ vertices : Finset (Fin M), vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ width) :
    M ≤ M' := by
  apply atom_count_le_alternative_count_of_spark_and_local_supports
    matrix alternative supports hspark h_twoK_le_d hwidth ?_ hupper
  intro vertices
  simpa [columnSpan, selectedColumns] using
    selectedColumns_subset_columnSpan_of_atom_supports matrix alternative supports
      hatom vertices

/-- A compatible choice of one alternative support for every source
`K`-coordinate set supplies the appendix's small-set neighborhood upper
bound. The compatibility hypothesis is the precise unresolved replacement for
the appendix's unassumed alternative-representation uniqueness sentence. -/
theorem neighborhood_card_le_of_coordinate_support_compatibility
    {M M' K width : ℕ}
    (supports : Fin M → Finset (Fin M'))
    (coordinateSupports : Finset (Fin M) → Finset (Fin M'))
    (hK_le_M : K ≤ M)
    (hcompatible : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      ∀ i ∈ coordinateSet, supports i ⊆ coordinateSupports coordinateSet)
    (hwidth : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      (coordinateSupports coordinateSet).card ≤ width) :
    ∀ vertices : Finset (Fin M), vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ width := by
  classical
  intro vertices hvertices
  obtain ⟨coordinateSet, hvertices_subset, _, hcoordinateSet_card⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ vertices) hvertices
      (by simpa using hK_le_M)
  apply (Finset.card_le_card ?_).trans (hwidth coordinateSet hcoordinateSet_card)
  intro alternativeCoordinate halternativeCoordinate
  obtain ⟨i, hi_vertices, hi_support⟩ :=
    Finset.mem_biUnion.mp halternativeCoordinate
  exact hcompatible coordinateSet hcoordinateSet_card i
    (hvertices_subset hi_vertices) hi_support

/-- The local neighborhood cap is exactly the finite content of compatible
coordinate-plane supports.  In the reverse direction, take each coordinate
support to be the union of its atoms' fixed supports. -/
theorem exists_coordinateSupports_compatible_iff_local_neighborhood_cap
    {M M' K width : ℕ}
    (supports : Fin M → Finset (Fin M')) (hK_le_M : K ≤ M) :
    (∃ coordinateSupports : Finset (Fin M) → Finset (Fin M'),
      (∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
        ∀ i ∈ coordinateSet,
          supports i ⊆ coordinateSupports coordinateSet) ∧
      ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
        (coordinateSupports coordinateSet).card ≤ width) ↔
      ∀ vertices : Finset (Fin M), vertices.card ≤ K →
        (neighborhood supports vertices).card ≤ width := by
  constructor
  · rintro ⟨coordinateSupports, hcompatible, hwidth⟩
    exact neighborhood_card_le_of_coordinate_support_compatibility
      supports coordinateSupports hK_le_M hcompatible hwidth
  · intro hlocal
    refine ⟨fun coordinateSet => neighborhood supports coordinateSet, ?_, ?_⟩
    · intro coordinateSet _hcoordinate_card i hi j hj
      exact Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
    · intro coordinateSet hcoordinate_card
      exact hlocal coordinateSet hcoordinate_card.le

/-- Compatible atom and coordinate-set supports imply the full counting
conclusion of the Hall argument. -/
theorem atom_count_le_alternative_count_of_coordinate_support_compatibility
    {d M M' K width : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (coordinateSupports : Finset (Fin M) → Finset (Fin M'))
    (hspark : spark matrix = d + 1)
    (h_twoK_le_d : 2 * K ≤ d)
    (hwidth : width + 1 ≤ 2 * K)
    (hK_le_M : K ≤ M)
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i))
    (hcompatible : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      ∀ i ∈ coordinateSet, supports i ⊆ coordinateSupports coordinateSet)
    (hcoordinateWidth : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      (coordinateSupports coordinateSet).card ≤ width) :
    M ≤ M' := by
  apply atom_count_le_alternative_count_of_spark_and_atom_supports
    matrix alternative supports hspark h_twoK_le_d hwidth hatom
  exact neighborhood_card_le_of_coordinate_support_compatibility supports coordinateSupports
    hK_le_M hcompatible hcoordinateWidth

/-- Spark-adaptive compatible-support theorem through an arbitrary cutoff.

The local Hall tree uses only independence below `spark matrix`.  Consequently
any cutoff below the source spark and at most `2*K` yields the same global Hall
conclusion whenever the alternative width is strictly smaller than that
cutoff. -/
theorem atom_count_le_alternative_count_of_spark_cutoff_compatibility
    {d M M' K width cutoff : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (coordinateSupports : Finset (Fin M) → Finset (Fin M'))
    (hcutoff_le_twoK : cutoff ≤ 2 * K)
    (hcutoff_lt_spark : cutoff < spark matrix)
    (hwidth : width + 1 ≤ cutoff)
    (hK_le_M : K ≤ M)
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i))
    (hcompatible : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      ∀ i ∈ coordinateSet, supports i ⊆ coordinateSupports coordinateSet)
    (hcoordinateWidth : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      (coordinateSupports coordinateSet).card ≤ width) :
    M ≤ M' := by
  apply atom_count_le_alternative_count_of_globalHall supports
  apply local_hall_implies_global_up_to supports K width cutoff
  · exact hcutoff_le_twoK
  · exact hwidth
  · exact local_hall_lower_up_to_of_spark_and_atom_supports_general
      matrix alternative supports hcutoff_lt_spark hatom
  · exact neighborhood_card_le_of_coordinate_support_compatibility
      supports coordinateSupports hK_le_M hcompatible hcoordinateWidth

/-- Optimized spark-adaptive compatible-support theorem.

Taking the cutoff to be `min (2*K) (spark matrix - 1)` gives the strongest
bound justified by the source dictionary's actual independence range. -/
theorem atom_count_le_alternative_count_of_spark_compatibility
    {d M M' K width : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (coordinateSupports : Finset (Fin M) → Finset (Fin M'))
    (hwidth : width + 1 ≤ min (2 * K) (spark matrix - 1))
    (hK_le_M : K ≤ M)
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i))
    (hcompatible : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      ∀ i ∈ coordinateSet, supports i ⊆ coordinateSupports coordinateSet)
    (hcoordinateWidth : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      (coordinateSupports coordinateSet).card ≤ width) :
    M ≤ M' := by
  apply atom_count_le_alternative_count_of_spark_cutoff_compatibility
    matrix alternative supports coordinateSupports
      (cutoff := min (2 * K) (spark matrix - 1))
  · exact Nat.min_le_left _ _
  · exact lt_of_le_of_lt (Nat.min_le_right _ _)
      (Nat.sub_lt (spark_pos matrix) (by omega))
  · exact hwidth
  · exact hK_le_M
  · exact hatom
  · exact hcompatible
  · exact hcoordinateWidth

/-- Dimension-limited strengthening of the appendix conclusion.

Under the exact atom/coordinate support compatibility used by the matching
argument, an alternative support width strictly below `min (2*K) d` cannot
reduce the atom count.  Equivalently, any compatible factorization with fewer
atoms has width at least `min (2*K) d`.  This removes the unnecessary global
premise `2*K ≤ d` and matches the identity-dictionary obstruction when the
ambient dimension is smaller than `2*K`.

The compatibility premise remains essential: it is not derived from the
printed factorization hypotheses, and the source's assertion of unique
alternative representations was its attempted justification. -/
theorem atom_count_le_alternative_count_of_dimension_limited_compatibility
    {d M M' K width : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (supports : Fin M → Finset (Fin M'))
    (coordinateSupports : Finset (Fin M) → Finset (Fin M'))
    (hspark : spark matrix = d + 1)
    (hwidth : width + 1 ≤ min (2 * K) d)
    (hK_le_M : K ≤ M)
    (hatom : ∀ i : Fin M,
      (fun row => matrix row i) ∈ columnSpan alternative (supports i))
    (hcompatible : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      ∀ i ∈ coordinateSet, supports i ⊆ coordinateSupports coordinateSet)
    (hcoordinateWidth : ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
      (coordinateSupports coordinateSet).card ≤ width) :
    M ≤ M' := by
  apply atom_count_le_alternative_count_of_globalHall supports
  apply local_hall_implies_global_up_to supports K width (min (2 * K) d)
  · exact Nat.min_le_left _ _
  · exact hwidth
  · exact local_hall_lower_up_to_of_spark_and_atom_supports
      matrix alternative supports hspark (Nat.min_le_right _ _) hatom
  · exact neighborhood_card_le_of_coordinate_support_compatibility
      supports coordinateSupports hK_le_M hcompatible hcoordinateWidth

/-- In the equal-size, equal-sparsity endpoint, the two local Hall bounds
force every selected alternative support to be a singleton.  This is the
finite combinatorial core of the source's part-(b) route after the Hall
matching has been obtained: for every `K`-set containing `i`, its `K`
matched labels exhaust its neighborhood, and varying that set eliminates all
labels except the one matched to `i`.

This remains proof support.  Connecting these singleton supports to equality
of the two dictionary *codes* additionally uses the source model's sparse
representation semantics. -/
theorem supports_singleton_of_equal_width
    {M K : ℕ} (supports : Fin M → Finset (Fin M))
    (hKpos : 1 ≤ K) (hKltM : K < M)
    (hglobal : GlobalHall supports)
    (hupper : ∀ vertices : Finset (Fin M), vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ K) :
    ∃ matching : Fin M → Fin M,
      Function.Bijective matching ∧
        ∀ i, supports i = {matching i} := by
  classical
  obtain ⟨matching, hmatching_injective, hmatching_mem⟩ :=
    exists_injective_representative_of_globalHall supports hglobal
  have hmatching_bijective : Function.Bijective matching :=
    (Fintype.bijective_iff_injective_and_card matching).mpr
      ⟨hmatching_injective, rfl⟩
  refine ⟨matching, hmatching_bijective, ?_⟩
  intro i
  apply Finset.Subset.antisymm
  · intro j hj
    obtain ⟨q, hq⟩ := hmatching_bijective.2 j
    subst j
    by_cases hqi : q = i
    · subst q
      exact Finset.mem_singleton_self _
    · have hq_ne_i : q ≠ i := hqi
      have hq_mem_erase : q ∈ (Finset.univ : Finset (Fin M)).erase i := by
        exact Finset.mem_erase.mpr ⟨hq_ne_i, Finset.mem_univ _⟩
      have hcard_available :
          (((Finset.univ : Finset (Fin M)).erase i).erase q).card = M - 2 := by
        rw [Finset.card_erase_of_mem hq_mem_erase,
          Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      have hKminus_le : K - 1 ≤
          (((Finset.univ : Finset (Fin M)).erase i).erase q).card := by
        rw [hcard_available]
        omega
      obtain ⟨T, hTsub, hTcard⟩ :=
        Finset.exists_subset_card_eq hKminus_le
      let vertices := insert i T
      have hi_vertices : i ∈ vertices := Finset.mem_insert_self _ _
      have hq_not_vertices : q ∉ vertices := by
        intro hqvertices
        rcases Finset.mem_insert.mp hqvertices with hqi' | hqT
        · exact hqi hqi'
        · have hq_not_T : q ∉ T := by
            intro hqT'
            exact (Finset.mem_erase.mp (hTsub hqT')).1 rfl
          exact hq_not_T hqT
      have hi_not_T : i ∉ T := by
        intro hiT
        have hi_ne_i : i ≠ i :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp (hTsub hiT)).2).1
        exact hi_ne_i rfl
      have hvertices_card : vertices.card = K := by
        dsimp [vertices]
        rw [Finset.card_insert_of_notMem hi_not_T, hTcard]
        omega
      have himage_subset : vertices.image matching ⊆
          neighborhood supports vertices := by
        intro y hy
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_biUnion.mpr ⟨v, hv, hmatching_mem v⟩
      have hK_le_neighborhood : K ≤ (neighborhood supports vertices).card := by
        rw [← hvertices_card, ← Finset.card_image_of_injective vertices
          hmatching_injective]
        exact Finset.card_le_card himage_subset
      have hneighborhood_le_K := hupper vertices (by simpa [hvertices_card])
      have hneighborhood_card : (neighborhood supports vertices).card = K :=
        Nat.le_antisymm hneighborhood_le_K hK_le_neighborhood
      have himage_eq_neighborhood : vertices.image matching =
          neighborhood supports vertices := by
        apply Finset.eq_of_subset_of_card_le himage_subset
        rw [Finset.card_image_of_injective vertices hmatching_injective,
          hvertices_card, hneighborhood_card]
      have hmatching_q_neighborhood : matching q ∈
          neighborhood supports vertices := by
        exact Finset.mem_biUnion.mpr ⟨i, hi_vertices, hj⟩
      have hmatching_q_image : matching q ∈ vertices.image matching := by
        rw [himage_eq_neighborhood]
        exact hmatching_q_neighborhood
      obtain ⟨v, hvvertices, hvmatching⟩ :=
        Finset.mem_image.mp hmatching_q_image
      have hvq : v = q := hmatching_injective (by simpa using hvmatching)
      exact (hq_not_vertices (hvq ▸ hvvertices)).elim
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact hmatching_mem i

end AppendixHall
end PKG26AtomicFeatures
