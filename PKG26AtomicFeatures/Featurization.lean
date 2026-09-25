import PKG26AtomicFeatures.OpenRichness
import PKG26AtomicFeatures.ConditionalRigidity
import PKG26AtomicFeatures.DimensionCounterexample

/-!
# Identifiable sparse featurizations

A featurization is a sparse factorization whose matrix has spark greater than
twice the sparsity. Relatively open richness extends any alternative
factorization to the entire union of source coordinate subspaces. This
extension supplies the full-span hypotheses of the algebraic rigidity lemmas.
-/

namespace PKG26AtomicFeatures

/-- A sparse factorization with the strict spark bound ensuring recovery of
each feature vector from its represented output. -/
def IsFeaturization {X : Type*} {d M : ℕ} (K : ℕ)
    (matrix : Matrix (Fin d) (Fin M) ℝ) (code : X → FeatureVector M)
    (f : X → RepresentationVector d) : Prop :=
  KSparse (K := K) code ∧
    (∀ x, f x = matrix.mulVec (code x)) ∧ 2 * K < spark matrix

/-- The union of the column spans indexed by all subsets of exactly `K`
columns, denoted `U_K(A)` in the source. -/
def SparseSubspaceUnion {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (K : ℕ) : Set (RepresentationVector d) :=
  ⋃ coordinates : {s : Finset (Fin M) // s.card = K},
    (columnSpan matrix coordinates.1 : Set (RepresentationVector d))

/-- The source inclusion lemma for the current, relatively open richness
definition and exact-size support unions. -/
theorem featurization_subspace_union_inclusion
    {X : Type*} {d M M' K K' : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {code : X → FeatureVector M}
    {f : X → RepresentationVector d}
    {alternative : Matrix (Fin d) (Fin M') ℝ}
    {alternativeCode : X → FeatureVector M'}
    (hsource : IsFeaturization K matrix code f)
    (hrich : OpenKRich (K := K) code)
    (halt : IsFeaturization K' alternative alternativeCode f) :
    SparseSubspaceUnion matrix K ⊆ SparseSubspaceUnion alternative K' := by
  classical
  have hK' : K' ≤ M' := by
    have hbound := spark_le_column_count_succ alternative
    have := halt.2.2
    omega
  intro v hv
  obtain ⟨coordinates, hcoordinates⟩ := Set.mem_iUnion.mp hv
  obtain ⟨support, hspan⟩ :=
    exists_sparse_alternative_subspace_of_openKRich matrix code f alternative
      alternativeCode hrich hsource.2.1 halt.1 halt.2.1 coordinates.1 coordinates.2
  obtain ⟨larger, hcontains, hcard⟩ :=
    Finset.exists_superset_card_eq support.2 (by simpa using hK')
  apply Set.mem_iUnion.mpr
  refine ⟨⟨larger, hcard⟩, columnSpan_mono alternative hcontains ?_⟩
  rw [map_mulVecLin_coordinateSpan_eq_columnSpan] at hspan
  exact hspan hcoordinates

/-- Open richness gives the span-union inclusion for arbitrary sparse
factorizations. Capping the competitor budget at its width also covers
full-column-rank dictionaries with a sparsity budget larger than their width. -/
theorem sparse_factorization_subspace_union_inclusion
    {X : Type*} {d M M' K K' : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {code : X → FeatureVector M}
    {f : X → RepresentationVector d}
    {alternative : Matrix (Fin d) (Fin M') ℝ}
    {alternativeCode : X → FeatureVector M'}
    (hf : ∀ x, f x = matrix.mulVec (code x))
    (hrich : OpenKRich (K := K) code)
    (hu : KSparse (K := K') alternativeCode)
    (hBu : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    SparseSubspaceUnion matrix K ⊆ SparseSubspaceUnion alternative (min K' M') := by
  classical
  have hu' : KSparse (K := min K' M') alternativeCode := by
    intro x
    exact le_min (hu x) (by simpa using (nonzeroSupport (alternativeCode x)).card_le_univ)
  intro v hv
  obtain ⟨coordinates, hcoordinates⟩ := Set.mem_iUnion.mp hv
  obtain ⟨support, hspan⟩ :=
    exists_sparse_alternative_subspace_of_openKRich matrix code f alternative
      alternativeCode hrich hf hu' hBu coordinates.1 coordinates.2
  obtain ⟨larger, hcontains, hcard⟩ :=
    Finset.exists_superset_card_eq support.2 (by simp)
  apply Set.mem_iUnion.mpr
  refine ⟨⟨larger, hcard⟩, columnSpan_mono alternative hcontains ?_⟩
  rw [map_mulVecLin_coordinateSpan_eq_columnSpan] at hspan
  exact hspan hcoordinates

/-- The spark bound makes the coefficient vector at each input unique among
all vectors at the stated sparsity. -/
theorem featurization_unique_sparse_representation
    {X : Type*} {d M K : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {code : X → FeatureVector M}
    {f : X → RepresentationVector d}
    (h : IsFeaturization K matrix code f) (x : X) (v : FeatureVector M)
    (hv : f x = matrix.mulVec v) (hsparse : (nonzeroSupport v).card ≤ K) :
    v = code x := by
  apply (kSparseInjective_iff_min_lt_spark matrix).mpr
    ((Nat.min_le_left (2 * K) M).trans_lt h.2.2) v (code x) hsparse (h.1 x)
  exact hv.symm.trans (h.2.1 x)

/-- Every sparse source coefficient vector has an alternative coefficient
vector once relatively open richness gives containment of its coordinate span.
The alternative dictionary remains fixed throughout the extension. -/
theorem exists_alternative_code_on_universal_sparse_domain
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (code : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hK : K ≤ M) (hrich : OpenKRich (K := K) code)
    (hfactors : ∀ x, f x = matrix.mulVec (code x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ extended : UniversalSparseDomain M K → FeatureVector M',
      KSparse (K := K') extended ∧
        ∀ v, universalSparseRepresentation matrix v = alternative.mulVec (extended v) := by
  classical
  have hexists : ∀ v : UniversalSparseDomain M K, ∃ w : FeatureVector M',
      (nonzeroSupport w).card ≤ K' ∧ alternative.mulVec w = matrix.mulVec v.1 := by
    intro v
    obtain ⟨coordinates, hcontains, hcard⟩ :=
      Finset.exists_superset_card_eq v.2 (by simpa using hK)
    obtain ⟨support, hspan⟩ :=
      exists_sparse_alternative_subspace_of_openKRich matrix code f alternative
        alternativeCode hrich hfactors halternativeSparse halternativeFactors
        coordinates hcard
    have hmem : matrix.mulVec v.1 ∈ columnSpan alternative support.1 :=
      hspan ⟨v.1, mem_coordinateSpan_of_nonzeroSupport_subset hcontains, rfl⟩
    obtain ⟨w, hw, heq⟩ := exists_sparse_code_of_mem_columnSpan alternative support.1
      (matrix.mulVec v.1) hmem
    exact ⟨w, hw.trans support.2, heq⟩
  choose extended hsparse heq using hexists
  exact ⟨extended, hsparse, fun v => (heq v).symm⟩

/-- Source sparsity cannot decrease in an alternative featurization. -/
theorem featurization_sparsity_le
    {X : Type*} {d M M' K K' : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {code : X → FeatureVector M}
    {f : X → RepresentationVector d}
    {alternative : Matrix (Fin d) (Fin M') ℝ}
    {alternativeCode : X → FeatureVector M'}
    (hsource : IsFeaturization K matrix code f)
    (hrich : OpenKRich (K := K) code)
    (halt : IsFeaturization K' alternative alternativeCode f) : K ≤ K' := by
  have hK : K ≤ M := by
    have hbound := spark_le_column_count_succ matrix
    have := hsource.2.2
    omega
  obtain ⟨extended, hsparse, hfactors⟩ :=
    exists_alternative_code_on_universal_sparse_domain matrix code f alternative
      alternativeCode hK hrich hsource.2.1 halt.1 halt.2.1
  exact AppendixHall.source_sparsity_le_alternative_sparsity_of_lt_spark matrix
    universalSparseCode (universalSparseRepresentation matrix) alternative extended
    (by have := hsource.2.2; omega) universalSparseCode_rich (fun _ => rfl)
    hsparse hfactors

/-- A narrower identifiable featurization requires at least twice the source
sparsity. Both spark hypotheses are exactly those of the source definition. -/
theorem featurization_strict_width_sparsity
    {X : Type*} {d M M' K K' : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {code : X → FeatureVector M}
    {f : X → RepresentationVector d}
    {alternative : Matrix (Fin d) (Fin M') ℝ}
    {alternativeCode : X → FeatureVector M'}
    (hKpos : 0 < K) (hsource : IsFeaturization K matrix code f)
    (hrich : OpenKRich (K := K) code)
    (halt : IsFeaturization K' alternative alternativeCode f)
    (hwidth : M' < M) : 2 * K ≤ K' := by
  have hK : K ≤ M := by
    have hbound := spark_le_column_count_succ matrix
    have := hsource.2.2
    omega
  obtain ⟨extended, hsparse, hfactors⟩ :=
    exists_alternative_code_on_universal_sparse_domain matrix code f alternative
      alternativeCode hK hrich hsource.2.1 halt.1 halt.2.1
  have hinjective : KSparseInjective alternative (min K' M') := by
    apply (kSparseInjective_iff_min_lt_spark alternative).mpr
    have := halt.2.2
    omega
  have hbound := effective_sparsity_ge_spark_cutoff_of_strict_width matrix
    universalSparseCode (universalSparseRepresentation matrix) alternative extended
    hKpos hK hwidth hinjective universalSparseCode_rich (fun _ => rfl) hsparse hfactors
  have := hsource.2.2
  omega

/-- The LRH-style strict-width dichotomy needs only relatively open richness.
An arbitrary narrower alternative either reaches the source spark-adaptive
sparsity cutoff or has insufficient spark for unique sparse decoding. -/
theorem openRich_strict_width_dichotomy
    {X : Type*} {d M M' K K' : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {code : X → FeatureVector M}
    {f : X → RepresentationVector d}
    {alternative : Matrix (Fin d) (Fin M') ℝ}
    {alternativeCode : X → FeatureVector M'}
    (hKpos : 0 < K) (hsource : IsFeaturization K matrix code f)
    (hrich : OpenKRich (K := K) code)
    (hwidth : M' < M)
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' ∨
      spark alternative ≤ min (2 * min K' M') M' := by
  have hK : K ≤ M := by
    have hbound := spark_le_column_count_succ matrix
    have hspark := hsource.2.2
    omega
  obtain ⟨extended, hextSparse, hextFactors⟩ :=
    exists_alternative_code_on_universal_sparse_domain matrix code f alternative
      alternativeCode hK hrich hsource.2.1 halternativeSparse
      halternativeFactors
  exact spark_cutoff_le_effective_sparsity_or_alternative_spark_le
    matrix universalSparseCode (universalSparseRepresentation matrix) alternative
    extended hKpos hK hwidth universalSparseCode_rich (fun _ => rfl)
    hextSparse hextFactors

/-- Source-spark-free version for an arbitrary sparse factorization.  The
source spark enters only through the numerical value of the first branch; no
full-spark or source-identifiability assumption is needed to obtain the
dichotomy itself. -/
theorem openRich_factorization_spark_dichotomy
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (code : X → FeatureVector M)
    (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : OpenKRich (K := K) code)
    (hsourceSparse : KSparse (K := K) code)
    (hfactors : ∀ x, f x = matrix.mulVec (code x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' ∨
      spark alternative ≤ min (2 * min K' M') M' := by
  obtain ⟨extended, hextSparse, hextFactors⟩ :=
    exists_alternative_code_on_universal_sparse_domain matrix code f alternative
      alternativeCode hK_le_M hrich hfactors halternativeSparse
      halternativeFactors
  exact spark_cutoff_le_effective_sparsity_or_alternative_spark_le
    matrix universalSparseCode (universalSparseRepresentation matrix) alternative
    extended hKpos hK_le_M hwidth universalSparseCode_rich (fun _ => rfl)
    hextSparse hextFactors

/-- Dictionary-level form of the open-richness dichotomy in the paper's
full-spark regime.  It requires no identifiability premise on the alternative:
the adverse branch is that the alternative spark is too small. -/
theorem openRich_twoK_strict_width_dichotomy
    {X : Type*} {d M M' K K' : ℕ}
    (source : Dictionary X d M K)
    (alternative : Dictionary X d M' K')
    (f : X → RepresentationVector d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (h2K_le_d : 2 * K ≤ d) (hwidth : M' < M)
    (hsourceSpark : spark source.matrix = d + 1)
    (hsourceRich : OpenKRich (K := K) source.code)
    (hsourceFactors : Factors source f)
    (halternativeFactors : Factors alternative f) :
    2 * K ≤ min K' M' ∨
      spark alternative.matrix ≤ min (2 * min K' M') M' := by
  have hsource : IsFeaturization K source.matrix source.code f := by
    refine ⟨source.sparse, hsourceFactors, ?_⟩
    rw [hsourceSpark]
    omega
  exact openRich_strict_width_dichotomy hKpos hsource hsourceRich hwidth
    alternative.sparse halternativeFactors |>.imp
    (fun h => by simpa [hsourceSpark, Nat.min_eq_left h2K_le_d] using h)
    id

/-- Dictionary-level source-spark-free form.  This is the primitive recovery
principle: a strict width reduction either raises effective sparsity to the
source-adaptive spark cutoff or destroys sparse decodability of the alternative.
-/
theorem factorization_openRich_spark_dichotomy
    {X : Type*} {d M M' K K' : ℕ}
    (source : Dictionary X d M K)
    (alternative : Dictionary X d M' K')
    (f : X → RepresentationVector d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hsourceRich : OpenKRich (K := K) source.code)
    (hsourceFactors : Factors source f)
    (halternativeFactors : Factors alternative f) :
    min (2 * K) (spark source.matrix - 1) ≤ min K' M' ∨
      spark alternative.matrix ≤ min (2 * min K' M') M' := by
  exact openRich_factorization_spark_dichotomy source.matrix source.code f
    alternative.matrix alternative.code hKpos hK_le_M hwidth hsourceRich
    source.sparse hsourceFactors alternative.sparse halternativeFactors

/-- If the alternative is uniquely sparse decodable, the adverse branch is
excluded and the full `2*K` strict-width lower bound follows.  This is the
clean decoding formulation of the recovery principle. -/
theorem factorization_openRich_strict_width_twoK_of_injective_alternative
    {X : Type*} {d M M' K K' : ℕ}
    (source : Dictionary X d M K)
    (alternative : Dictionary X d M' K')
    (f : X → RepresentationVector d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (h2K_le_d : 2 * K ≤ d)
    (hwidth : M' < M)
    (hsourceSpark : spark source.matrix = d + 1)
    (hsourceRich : OpenKRich (K := K) source.code)
    (hsourceFactors : Factors source f)
    (halternativeInjective :
      KSparseInjective alternative.matrix (min K' M'))
    (halternativeFactors : Factors alternative f) :
    2 * K ≤ min K' M' := by
  rcases openRich_twoK_strict_width_dichotomy source alternative f hKpos
      (by
        have hbound := spark_le_column_count_succ source.matrix
        have hspark := hsourceSpark
        omega)
      h2K_le_d hwidth hsourceSpark hsourceRich hsourceFactors
      halternativeFactors with hlarge | hlow
  · exact hlarge
  · have hspark : min (2 * min K' M') M' < spark alternative.matrix :=
      (kSparseInjective_iff_min_lt_spark alternative.matrix).mp
        halternativeInjective
    omega

/-- Full source-range version with primitive richness.  If every source atom
ray is observed and the alternative is uniquely sparse decodable on the actual
range, then a strict width reduction forces the `2*K` sparsity cost.  Otherwise
the theorem records nonidentifiability directly on the observed range. -/
theorem factorization_openRich_twoK_or_range_nonidentifiable
    {X : Type*} {d M M' K K' : ℕ}
    (source : Dictionary X d M K)
    (alternative : Dictionary X d M' K')
    (f : X → RepresentationVector d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (h2K_le_d : 2 * K ≤ d)
    (hwidth : M' < M)
    (hsourceSpark : spark source.matrix = d + 1)
    (hsourceRays : SourceAtomRaysRealized source.code)
    (hsourceRich : OpenKRich (K := K) source.code)
    (hsourceFactors : Factors source f)
    (halternativeFactors : Factors alternative f) :
    2 * K ≤ min K' M' ∨
      ¬ UniquelySparseDecodableOn alternative.matrix
        (Set.range f) (min K' M') := by
  by_cases hdecodable : UniquelySparseDecodableOn alternative.matrix
      (Set.range f) (min K' M')
  · left
    obtain ⟨extended, hextSparse, hextFactors⟩ :=
      exists_alternative_code_on_universal_sparse_domain source.matrix
        source.code f alternative.matrix alternative.code
        hK_le_M
        hsourceRich hsourceFactors alternative.sparse halternativeFactors
    have hatomwise :=
      sourceAtomCodesUniqueAtWidth_of_uniquelySparseDecodableOn_range_of_rays
        source.matrix source.code f alternative.matrix hsourceRays hsourceFactors
          hdecodable
    have hbound :=
      effective_sparsity_ge_dimension_cutoff_of_strict_width_and_atomwise_unique
        source.matrix universalSparseCode
          (universalSparseRepresentation source.matrix) alternative.matrix extended
          hsourceSpark hKpos hK_le_M hwidth hatomwise universalSparseCode_rich
          (fun _ => rfl)
          hextSparse hextFactors
    simpa [Nat.min_eq_left h2K_le_d] using hbound
  · exact Or.inr hdecodable

/-- Equal-size featurizations agree in both columns and codes under one
common permutation and invertible diagonal scaling. -/
theorem featurization_equal_size_equivalent
    {X : Type*} {d M K : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {code : X → FeatureVector M}
    {f : X → RepresentationVector d}
    {alternative : Matrix (Fin d) (Fin M) ℝ}
    {alternativeCode : X → FeatureVector M}
    (hKpos : 0 < K) (hsource : IsFeaturization K matrix code f)
    (hrich : OpenKRich (K := K) code)
    (halt : IsFeaturization K alternative alternativeCode f) :
    DictionaryPairsEquivalentUpToPermutationAndScaling matrix code
      alternative alternativeCode := by
  have hK : K ≤ M := by
    have hbound := spark_le_column_count_succ matrix
    have := hsource.2.2
    omega
  obtain ⟨extended, hsparse, hfactors⟩ :=
    exists_alternative_code_on_universal_sparse_domain matrix code f alternative
      alternativeCode hK hrich hsource.2.1 halt.1 halt.2.1
  obtain ⟨permutation, scale, hscale, hcolumns, _⟩ :=
    equal_size_dictionary_and_code_identifiability matrix universalSparseCode
      (universalSparseRepresentation matrix) alternative extended hKpos hsource.2.2
      universalSparseCode_rich universalSparseCode_sparse (fun _ => rfl) hsparse hfactors
  refine ⟨permutation, scale, hscale, hcolumns, ?_⟩
  have halignedSparse := kSparse_alignAlternativeCode permutation scale hscale
    alternativeCode halt.1
  have hinjective : KSparseInjective matrix K :=
    (kSparseInjective_iff_min_lt_spark matrix).mpr
      ((Nat.min_le_left (2 * K) M).trans_lt hsource.2.2)
  intro x i
  have heq : code x = alignAlternativeCode permutation scale (alternativeCode x) := by
    apply hinjective _ _ (hsource.1 x) (halignedSparse x)
    exact (hsource.2.1 x).symm.trans ((halt.2.1 x).trans
      (mulVec_alignAlternativeCode matrix alternative permutation scale hcolumns
        (alternativeCode x)))
  have hi := congrFun heq (permutation i)
  simpa [alignAlternativeCode] using hi

/-- The neighbors in a finite bipartite graph of a finite left vertex set. -/
noncomputable def bipartiteNeighborhood {m n : ℕ}
    (edges : Fin m → Fin n → Prop) (vertices : Finset (Fin m)) : Finset (Fin n) := by
  classical
  exact vertices.biUnion (fun x => Finset.univ.filter (edges x))

/-- Local Hall inequalities and the small-neighborhood upper bound imply
global Hall, a matching saturating the left side, and the vertex-count bound. -/
theorem finite_local_to_global_hall
    {m n K : ℕ} (edges : Fin m → Fin n → Prop) (hK : 0 < K)
    (hlower : ∀ vertices : Finset (Fin m), vertices.card ≤ 2 * K →
      vertices.card ≤ (bipartiteNeighborhood edges vertices).card)
    (hupper : ∀ vertices : Finset (Fin m), vertices.card ≤ K →
      (bipartiteNeighborhood edges vertices).card ≤ 2 * K - 1) :
    (∀ vertices : Finset (Fin m),
      vertices.card ≤ (bipartiteNeighborhood edges vertices).card) ∧
    (∃ matching : Fin m → Fin n,
      Function.Injective matching ∧ ∀ x, edges x (matching x)) ∧ m ≤ n := by
  classical
  let supports : Fin m → Finset (Fin n) := fun x => Finset.univ.filter (edges x)
  have hglobal : AppendixHall.GlobalHall supports :=
    AppendixHall.local_hall_implies_global supports K (2 * K - 1)
      (by omega) hlower hupper
  obtain ⟨matching, hinjective, hmem⟩ :=
    AppendixHall.exists_injective_representative_of_globalHall supports hglobal
  refine ⟨hglobal, ⟨matching, hinjective, ?_⟩, ?_⟩
  · intro x
    simpa [supports] using hmem x
  · simpa using Fintype.card_le_of_injective matching hinjective

end PKG26AtomicFeatures
