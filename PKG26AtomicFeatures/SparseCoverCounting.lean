import PKG26AtomicFeatures.AppendixHall

namespace PKG26AtomicFeatures

open AppendixHall

/-- A finite family of blocks of size at most `width` that covers every
`K`-subset contains enough blocks to satisfy the elementary covering bound. -/
theorem choose_le_card_mul_choose_of_powersetCard_cover
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (source : Finset α) (targets : Finset ι) (blocks : ι → Finset α)
    (K width : ℕ)
    (hblock : ∀ target ∈ targets, (blocks target).card ≤ width)
    (hcover : ∀ subset ∈ source.powersetCard K,
      ∃ target ∈ targets, subset ⊆ blocks target) :
    source.card.choose K ≤ targets.card * width.choose K := by
  have hsubset : source.powersetCard K ⊆
      targets.biUnion (fun target => (blocks target).powersetCard K) := by
    intro subset hsubset_source
    obtain ⟨target, htarget, hsubset_block⟩ := hcover subset hsubset_source
    apply Finset.mem_biUnion.mpr
    exact ⟨target, htarget, Finset.mem_powersetCard.mpr
      ⟨hsubset_block, (Finset.mem_powersetCard.mp hsubset_source).2⟩⟩
  calc
    source.card.choose K = (source.powersetCard K).card := by simp
    _ ≤ (targets.biUnion (fun target => (blocks target).powersetCard K)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ target ∈ targets, ((blocks target).powersetCard K).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _target ∈ targets, width.choose K := by
      apply Finset.sum_le_sum
      intro target htarget
      simp only [Finset.card_powersetCard]
      exact Nat.choose_le_choose K (hblock target htarget)
    _ = targets.card * width.choose K := by simp

/-- The image of a coordinate subspace under matrix multiplication is the
span of the corresponding matrix columns. -/
theorem map_mulVecLin_coordinateSpan_eq_columnSpan
    {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (coordinates : Finset (Fin M)) :
    Submodule.map matrix.mulVecLin (coordinateSpan coordinates) =
      columnSpan matrix coordinates := by
  rw [coordinateSpan, Submodule.map_span, columnSpan]
  congr 1
  ext vector
  constructor
  · rintro ⟨basisVector, ⟨coordinate, rfl⟩, rfl⟩
    refine ⟨coordinate, ?_⟩
    ext row
    simp [selectedColumns]
  · rintro ⟨coordinate, rfl⟩
    refine ⟨Pi.single coordinate.1 (1 : ℝ), ⟨coordinate, rfl⟩, ?_⟩
    ext row
    simp [selectedColumns]

/-- Source atoms lying in one selected alternative column span. -/
noncomputable def sourceAtomsInColumnSpan
    {d M M' : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (support : Finset (Fin M')) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun i =>
    (fun row => matrix row i) ∈ columnSpan alternative support

@[simp] theorem mem_sourceAtomsInColumnSpan_iff
    {d M M' : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (support : Finset (Fin M')) (i : Fin M) :
    i ∈ sourceAtomsInColumnSpan matrix alternative support ↔
      (fun row => matrix row i) ∈ columnSpan alternative support := by
  classical
  simp [sourceAtomsInColumnSpan]

theorem source_support_subset_sourceAtomsInColumnSpan
    {d M M' : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    {sourceSupport : Finset (Fin M)} {alternativeSupport : Finset (Fin M')}
    (hspan : columnSpan matrix sourceSupport ≤
      columnSpan alternative alternativeSupport) :
    sourceSupport ⊆
      sourceAtomsInColumnSpan matrix alternative alternativeSupport := by
  intro i hi
  rw [mem_sourceAtomsInColumnSpan_iff]
  apply hspan
  apply Submodule.subset_span
  exact ⟨⟨i, hi⟩, rfl⟩

/-- A span of at most `width` alternative atoms contains at most `width`
source atoms whenever every `width+1` source atoms are independent. -/
theorem sourceAtomsInColumnSpan_card_le
    {d M M' width : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (support : Finset (Fin M'))
    (hsupport : support.card ≤ width)
    (hcutoff : width + 1 < spark matrix) :
    (sourceAtomsInColumnSpan matrix alternative support).card ≤ width := by
  classical
  by_contra hnot
  have hsucc : width + 1 ≤
      (sourceAtomsInColumnSpan matrix alternative support).card := by omega
  obtain ⟨vertices, hvertices_subset, hvertices_card⟩ :=
    Finset.exists_subset_card_eq hsucc
  let localSupports : Fin M → Finset (Fin M') := fun _ => support
  have hvertices_nonempty : vertices.Nonempty := by
    apply Finset.card_pos.mp
    rw [hvertices_card]
    omega
  have hneighborhood : neighborhood localSupports vertices = support := by
    change vertices.biUnion localSupports = support
    apply Finset.Subset.antisymm
    · intro alternativeCoordinate halternativeCoordinate
      obtain ⟨i, _, hi_support⟩ := Finset.mem_biUnion.mp halternativeCoordinate
      simpa [localSupports] using hi_support
    · intro alternativeCoordinate halternativeCoordinate
      obtain ⟨i, hi⟩ := hvertices_nonempty
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, by simpa [localSupports] using halternativeCoordinate⟩
  have hspan : Set.range (selectedColumns matrix vertices) ⊆
      Submodule.span ℝ (Set.range
        (fun j : {j // j ∈ neighborhood localSupports vertices} =>
          fun row => alternative row j)) := by
    rw [hneighborhood]
    intro column
    rintro ⟨i, rfl⟩
    have hi := hvertices_subset i.2
    simpa [columnSpan, selectedColumns] using
      (mem_sourceAtomsInColumnSpan_iff matrix alternative support i).mp hi
  have hcard_le := card_le_neighborhood_of_spark_and_span
    matrix alternative localSupports vertices (by omega) hspan
  rw [hneighborhood, hvertices_card] at hcard_le
  omega

/-- If every source `K`-span is contained in an alternative span generated by
at most `width` atoms, and `width+1` source atoms are always independent, then
the numbers of source and alternative supports obey the binomial capacity
bound. -/
theorem choose_bound_of_sparse_subspace_cover
    {d M M' K width : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (hwidth_le : width ≤ M')
    (hcutoff : width + 1 < spark matrix)
    (hcover : ∀ sourceSupport : Finset (Fin M), sourceSupport.card = K →
      ∃ alternativeSupport : Finset (Fin M'),
        alternativeSupport.card ≤ width ∧
          columnSpan matrix sourceSupport ≤
            columnSpan alternative alternativeSupport) :
    M.choose K ≤ M'.choose width * width.choose K := by
  classical
  let sourceUniverse : Finset (Fin M) := Finset.univ
  let targetUniverse : Finset (Fin M') := Finset.univ
  let targets : Finset (Finset (Fin M')) := targetUniverse.powersetCard width
  let blocks : Finset (Fin M') → Finset (Fin M) :=
    sourceAtomsInColumnSpan matrix alternative
  have hblock : ∀ target ∈ targets, (blocks target).card ≤ width := by
    intro target htarget
    apply sourceAtomsInColumnSpan_card_le matrix alternative target
    · exact (Finset.mem_powersetCard.mp htarget).2.le
    · exact hcutoff
  have hfinite_cover : ∀ subset ∈ sourceUniverse.powersetCard K,
      ∃ target ∈ targets, subset ⊆ blocks target := by
    intro subset hsubset
    obtain ⟨smallTarget, hsmallTargetCard, hspan⟩ :=
      hcover subset (Finset.mem_powersetCard.mp hsubset).2
    have hwidth_univ : width ≤ targetUniverse.card := by
      simpa [targetUniverse] using hwidth_le
    obtain ⟨target, hsmallTarget_subset, htarget_card⟩ :=
      Finset.exists_superset_card_eq hsmallTargetCard hwidth_univ
    have htarget_mem : target ∈ targets := by
      exact Finset.mem_powersetCard.mpr
        ⟨by simp [targetUniverse], htarget_card⟩
    refine ⟨target, htarget_mem, ?_⟩
    apply source_support_subset_sourceAtomsInColumnSpan matrix alternative
    exact hspan.trans (columnSpan_mono alternative hsmallTarget_subset)
  have hcount := choose_le_card_mul_choose_of_powersetCard_cover
    sourceUniverse targets blocks K width hblock hfinite_cover
  simpa [sourceUniverse, targetUniverse, targets] using hcount

/-- A sparsity cap can always be reduced to the number of available
coordinates. -/
theorem kSparse_min_columnCount
    {X : Type*} {M' K' : ℕ} (code : X → FeatureVector M')
    (hsparse : KSparse (K := K') code) :
    KSparse (K := min K' M') code := by
  intro x
  apply Nat.le_min.mpr
  exact ⟨hsparse x, by simpa using Finset.card_le_univ (nonzeroSupport (code x))⟩

/-- For positive subset size, the binomial coefficient is strictly increasing
once the ambient cardinality is at least that size. -/
theorem Nat.choose_lt_choose_of_lt
    {smaller larger K : ℕ} (hKpos : 0 < K) (hKsmall : K ≤ smaller)
    (hlt : smaller < larger) :
    smaller.choose K < larger.choose K := by
  have hstep : smaller.choose K < (smaller + 1).choose K := by
    rw [Nat.choose_succ_left smaller K hKpos]
    have hpositive : 0 < smaller.choose (K - 1) :=
      Nat.choose_pos (by omega)
    omega
  exact hstep.trans_le (Nat.choose_le_choose K (Nat.succ_le_of_lt hlt))

theorem Nat.le_of_choose_le_choose
    {left right K : ℕ} (hKpos : 0 < K) (hKright : K ≤ right)
    (hchoose : left.choose K ≤ right.choose K) :
    left ≤ right := by
  by_contra hnot
  have hstrict := Nat.choose_lt_choose_of_lt hKpos hKright
    (Nat.lt_of_not_ge hnot)
  omega

/-- Unconditional width--sparsity tradeoff derived directly from source
richness and two sparse factorizations.  No atom-compatible alternative
support family is assumed. -/
theorem choose_bound_of_kRich_and_factorizations
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hcutoff : min K' M' + 1 < spark matrix)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    M.choose K ≤ M'.choose (min K' M') * (min K' M').choose K := by
  apply choose_bound_of_sparse_subspace_cover matrix alternative
      (width := min K' M') (Nat.min_le_right _ _) hcutoff
  intro sourceSupport hsourceSupport
  obtain ⟨alternativeSupport, hspan⟩ :=
    exists_sparse_alternative_subspace_containing_coordinate_image
      matrix z f alternative alternativeCode hrich hfactors
      (kSparse_min_columnCount alternativeCode halternativeSparse)
      halternativeFactors sourceSupport hsourceSupport
  refine ⟨alternativeSupport.1, alternativeSupport.2, ?_⟩
  rw [← map_mulVecLin_coordinateSpan_eq_columnSpan]
  exact hspan

/-- Part (a) strengthened to the effective alternative sparsity: no code can
use more than the number of available alternative coordinates. -/
theorem source_sparsity_le_effective_alternative_sparsity
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hK_lt_spark : K < spark matrix)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    K ≤ min K' M' := by
  apply source_sparsity_le_alternative_sparsity_of_lt_spark
    matrix z f alternative alternativeCode hK_lt_spark hrich hfactors
    (kSparse_min_columnCount alternativeCode halternativeSparse)
    halternativeFactors

/-- Equal sparsity cannot reduce dictionary width.  This is the unconditional
strict-width endpoint behind `M' < M → K' ≥ K+1`; it uses no compatible
atom-support selection in the alternative dictionary. -/
theorem source_atom_count_le_of_equal_sparsity
    {X : Type*} {d M M' K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K)
    (hcutoff : K + 1 < spark matrix)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    M ≤ M' := by
  have hK_le_min := source_sparsity_le_effective_alternative_sparsity
    (K := K) (K' := K) matrix z f alternative alternativeCode (by omega)
    hrich hfactors halternativeSparse halternativeFactors
  have hK_le_M' : K ≤ M' := hK_le_min.trans (Nat.min_le_right _ _)
  have hmin : min K M' = K := Nat.min_eq_left hK_le_M'
  have hchoose := choose_bound_of_kRich_and_factorizations
    matrix z f alternative alternativeCode (by simpa [hmin] using hcutoff)
    hrich hfactors halternativeSparse halternativeFactors
  rw [hmin, Nat.choose_self, Nat.mul_one] at hchoose
  exact Nat.le_of_choose_le_choose hKpos hK_le_M' hchoose

/-- Any strict reduction in atom count requires a strict increase in sparsity.
This is the unconditional corrected form of the source theorem's width-drop
claim. -/
theorem alternative_sparsity_succ_le_of_fewer_atoms
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K)
    (hcutoff : K + 1 < spark matrix)
    (hfewer : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    K + 1 ≤ K' := by
  have hK_le_K' := source_sparsity_le_alternative_sparsity_of_lt_spark
    (K := K) (K' := K') matrix z f alternative alternativeCode (by omega)
    hrich hfactors halternativeSparse halternativeFactors
  by_contra hnot
  have hK'_eq : K' = K := by omega
  subst K'
  have hwidth := source_atom_count_le_of_equal_sparsity
    matrix z f alternative alternativeCode hKpos hcutoff hrich hfactors
    halternativeSparse halternativeFactors
  omega

/-- The strict-width correction is naturally a bound on *effective*
alternative sparsity.  Under the same assumptions as the declared-sparsity
version, both the declared budget and the number of available alternative
coordinates are at least `K + 1`. -/
theorem effective_alternative_sparsity_succ_le_of_fewer_atoms
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K)
    (hcutoff : K + 1 < spark matrix)
    (hfewer : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    K + 1 ≤ min K' M' := by
  have hK_le_min := source_sparsity_le_effective_alternative_sparsity
    matrix z f alternative alternativeCode (by omega) hrich hfactors
      halternativeSparse halternativeFactors
  by_contra hnot
  have hmin_eq : min K' M' = K := by omega
  have hchoose := choose_bound_of_kRich_and_factorizations
    matrix z f alternative alternativeCode (by simpa [hmin_eq] using hcutoff)
      hrich hfactors halternativeSparse halternativeFactors
  have hK_le_M' : K ≤ M' := hK_le_min.trans (Nat.min_le_right _ _)
  rw [hmin_eq, Nat.choose_self, Nat.mul_one] at hchoose
  have hwidth := Nat.le_of_choose_le_choose hKpos hK_le_M' hchoose
  omega

/-- Full-spark specialization: the manuscript's intended `1 ≤ K < d`
regime already implies the independence cutoff needed for the strict
`K+1` lower bound. -/
theorem alternative_sparsity_succ_le_of_fewer_atoms_full_spark
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1)
    (hKpos : 0 < K)
    (hK_lt_d : K < d)
    (hfewer : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    K + 1 ≤ K' := by
  apply alternative_sparsity_succ_le_of_fewer_atoms
    matrix z f alternative alternativeCode hKpos
  · rw [hspark]
    omega
  · exact hfewer
  · exact hrich
  · exact hfactors
  · exact halternativeSparse
  · exact halternativeFactors

end PKG26AtomicFeatures
