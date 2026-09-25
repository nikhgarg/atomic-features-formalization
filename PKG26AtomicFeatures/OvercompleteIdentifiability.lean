import PKG26AtomicFeatures.Featurization

/-!
# Exact atom recovery at arbitrary learned width

At equal sparsity, rich exact data and sparse injectivity of the alternative
dictionary force it to contain every source atom. Extra learned columns do
not weaken this conclusion. The source needs independence only through
`K + 1` columns; the alternative's sparse injectivity supplies compatibility
of all source-atom supports. Hall's theorem then gives a matching, and the
upper bound on every `K`-neighborhood forces all supports to be singletons.
-/

namespace PKG26AtomicFeatures

open AppendixHall
open scoped BigOperators

/-- A Hall family whose every `K`-neighborhood has at most `K` elements
consists of distinct singletons when `0 < K < M`. The right side may
have arbitrarily many vertices. -/
theorem supports_singleton_of_hall_and_neighborhood_upper
    {M M' K : ℕ} (supports : Fin M → Finset (Fin M'))
    (hKpos : 0 < K) (hKltM : K < M)
    (hglobal : GlobalHall supports)
    (hupper : ∀ vertices : Finset (Fin M), vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ K) :
    ∃ matching : Fin M → Fin M', Function.Injective matching ∧
      ∀ i, supports i = {matching i} := by
  classical
  obtain ⟨matching, hinjective, hmatching⟩ :=
    exists_injective_representative_of_globalHall supports hglobal
  have himage (vertices : Finset (Fin M)) (hcard : vertices.card = K) :
      vertices.image matching = neighborhood supports vertices := by
    have hsubset : vertices.image matching ⊆ neighborhood supports vertices := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_biUnion.mpr ⟨v, hv, hmatching v⟩
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_image_of_injective vertices hinjective, hcard]
    exact hupper vertices hcard.le
  have howner (i : Fin M) (j : Fin M') (hj : j ∈ supports i) :
      ∃ q, matching q = j := by
    obtain ⟨vertices, hcontains, hcard⟩ :=
      Finset.exists_superset_card_eq
        (show ({i} : Finset (Fin M)).card ≤ K by simp; omega)
        (show K ≤ Fintype.card (Fin M) by simpa using hKltM.le)
    have hi : i ∈ vertices := hcontains (Finset.mem_singleton_self i)
    have hmem : j ∈ neighborhood supports vertices :=
      Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
    rw [← himage vertices hcard] at hmem
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
    exact ⟨q, hq⟩
  refine ⟨matching, hinjective, ?_⟩
  intro i
  apply Finset.Subset.antisymm
  · intro j hj
    obtain ⟨q, hq⟩ := howner i j hj
    subst j
    by_cases hqi : q = i
    · subst q
      exact Finset.mem_singleton_self _
    · have hq_mem_erase : q ∈ (Finset.univ : Finset (Fin M)).erase i :=
        Finset.mem_erase.mpr ⟨hqi, Finset.mem_univ _⟩
      have hcard_available :
          (((Finset.univ : Finset (Fin M)).erase i).erase q).card = M - 2 := by
        rw [Finset.card_erase_of_mem hq_mem_erase,
          Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      have hKminus : K - 1 ≤
          (((Finset.univ : Finset (Fin M)).erase i).erase q).card := by
        rw [hcard_available]
        omega
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hKminus
      let vertices := insert i T
      have hi_vertices : i ∈ vertices := Finset.mem_insert_self _ _
      have hq_not_vertices : q ∉ vertices := by
        intro hqvertices
        rcases Finset.mem_insert.mp hqvertices with hqi' | hqT
        · exact hqi hqi'
        · exact (Finset.mem_erase.mp (hTsub hqT)).1 rfl
      have hi_not_T : i ∉ T := by
        intro hiT
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hTsub hiT)).2).1 rfl
      have hvertices_card : vertices.card = K := by
        dsimp [vertices]
        rw [Finset.card_insert_of_notMem hi_not_T, hTcard]
        omega
      have hmem : matching q ∈ neighborhood supports vertices :=
        Finset.mem_biUnion.mpr ⟨i, hi_vertices, hj⟩
      rw [← himage vertices hvertices_card] at hmem
      obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hmem
      exact (hq_not_vertices (hinjective heq ▸ hv)).elim
  · intro j hj
    rw [Finset.mem_singleton.mp hj]
    exact hmatching i

/-- Every source atom occurs as a distinct learned column, up to nonzero
scaling, in an exact equal-sparsity alternative of arbitrary width.
The source is rich on its `K`-supports, every `K + 1` source columns are
independent, and the alternative is injective on `K`-sparse codes. -/
theorem source_columns_embed_of_kRich_and_injective_alternative
    {X : Type*} {d M M' K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hKltM : K < M)
    (hcutoff : K + 1 < spark matrix)
    (hinjective : KSparseInjective alternative K)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin M', ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      ∀ i, matrix.col i = scale i • alternative.col (matching i) := by
  classical
  have hinjective_min : KSparseInjective alternative (min K M') := by
    intro u v hu hv heq
    exact hinjective u v (hu.trans (Nat.min_le_left _ _))
      (hv.trans (Nat.min_le_left _ _)) heq
  obtain ⟨supports, coordinateSupports, _, hatom, hcoordinate, hcompatible⟩ :=
    exists_compatible_supports_of_kRich_and_injective_alternative
      matrix z f alternative alternativeCode hKpos hKltM.le hinjective_min
      hrich hfactors halternativeSparse halternativeFactors
  have hupper : ∀ vertices : Finset (Fin M), vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ K := by
    apply neighborhood_card_le_of_coordinate_support_compatibility
      supports coordinateSupports hKltM.le hcompatible
    intro coordinates hcoordinates
    exact (hcoordinate coordinates hcoordinates).trans (Nat.min_le_left _ _)
  have hglobal : GlobalHall supports := by
    apply local_hall_implies_global_up_to supports K K (K + 1)
    · omega
    · omega
    · exact local_hall_lower_up_to_of_spark_and_atom_supports_general
        matrix alternative supports hcutoff hatom
    · exact hupper
  obtain ⟨matching, hmatching, hsingleton⟩ :=
    supports_singleton_of_hall_and_neighborhood_upper supports hKpos hKltM
      hglobal hupper
  have hscale_exists : ∀ i : Fin M, ∃ scale : ℝ,
      scale ≠ 0 ∧ matrix.col i = scale • alternative.col (matching i) := by
    intro i
    have hmem : matrix.col i ∈ ℝ ∙ alternative.col (matching i) := by
      rw [← familySpan_singleton (R := ℝ) alternative.col (matching i),
        familySpan_matrix_columns_eq_columnSpan]
      simpa [hsingleton i] using hatom i
    obtain ⟨scale, hscale⟩ := Submodule.mem_span_singleton.mp hmem
    have hsource_ne : matrix.col i ≠ 0 := by
      have hli := linearIndependent_of_card_lt_spark matrix
        ({i} : Finset (Fin M)) (by simp; omega)
      have hne := hli.ne_zero
        (⟨i, Finset.mem_singleton_self _⟩ : {j // j ∈ ({i} : Finset (Fin M))})
      simpa [selectedColumns] using hne
    refine ⟨scale, ?_, hscale.symm⟩
    intro hzero
    exact hsource_ne (by rw [← hscale, hzero]; simp)
  choose scale hscale hcolumns using hscale_exists
  exact ⟨⟨matching, hmatching⟩, scale, hscale, hcolumns⟩

/-- Relatively open richness suffices for exact atom recovery at arbitrary
learned width. The extension to all sparse source vectors is derived before
the algebraic identification theorem is applied. -/
theorem source_columns_embed_of_openRich_and_injective_alternative
    {X : Type*} {d M M' K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hKltM : K < M)
    (hcutoff : K + 1 < spark matrix)
    (hinjective : KSparseInjective alternative K)
    (hrich : OpenKRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin M', ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      ∀ i, matrix.col i = scale i • alternative.col (matching i) := by
  obtain ⟨extended, hsparse, hfactors'⟩ :=
    exists_alternative_code_on_universal_sparse_domain matrix z f alternative
      alternativeCode hKltM.le hrich hfactors halternativeSparse halternativeFactors
  exact source_columns_embed_of_kRich_and_injective_alternative matrix
    universalSparseCode (universalSparseRepresentation matrix) alternative extended
    hKpos hKltM hcutoff hinjective universalSparseCode_rich (fun _ => rfl)
    hsparse hfactors'

/-- Embed a source coefficient vector along distinct learned columns, using
the same scaling that expresses each source column in the learned dictionary. -/
noncomputable def embedSourceCode {M M' : ℕ} (matching : Fin M ↪ Fin M')
    (scale : Fin M → ℝ) (code : FeatureVector M) : FeatureVector M' :=
  fun j => ∑ i, if matching i = j then scale i * code i else 0

@[simp] theorem embedSourceCode_apply_matching {M M' : ℕ}
    (matching : Fin M ↪ Fin M') (scale : Fin M → ℝ) (code : FeatureVector M)
    (i : Fin M) :
    embedSourceCode matching scale code (matching i) = scale i * code i := by
  classical
  simp [embedSourceCode, matching.injective.eq_iff]

theorem nonzeroSupport_embedSourceCode_subset {M M' : ℕ}
    (matching : Fin M ↪ Fin M') (scale : Fin M → ℝ) (code : FeatureVector M) :
    nonzeroSupport (embedSourceCode matching scale code) ⊆
      (nonzeroSupport code).image matching := by
  classical
  intro j hj
  by_contra hnot
  have hzero : embedSourceCode matching scale code j = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with heq
    · have hcode : code i = 0 := by
        by_contra hcode
        exact hnot (Finset.mem_image.mpr
          ⟨i, (mem_nonzeroSupport_iff code i).mpr hcode, heq⟩)
      simp [hcode]
    · rfl
  exact (mem_nonzeroSupport_iff _ j).mp hj hzero

theorem mulVec_embedSourceCode {d M M' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (matching : Fin M ↪ Fin M') (scale : Fin M → ℝ)
    (hcolumns : ∀ i, matrix.col i = scale i • alternative.col (matching i))
    (code : FeatureVector M) :
    alternative.mulVec (embedSourceCode matching scale code) = matrix.mulVec code := by
  classical
  ext row
  simp only [Matrix.mulVec, dotProduct, embedSourceCode, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hentry := congrFun (hcolumns i) row
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hentry
  rw [hentry]
  simp only [mul_ite, mul_zero]
  simp [eq_comm, mul_assoc, mul_left_comm]

/-- Once source columns embed into an injective sparse alternative, every
observed alternative code is the correspondingly embedded source code.
In particular, all surplus learned coordinates are identically unused. -/
theorem alternative_code_eq_embedded_source_code
    {X : Type*} {d M M' K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (matching : Fin M ↪ Fin M') (scale : Fin M → ℝ)
    (hcolumns : ∀ i, matrix.col i = scale i • alternative.col (matching i))
    (hinjective : KSparseInjective alternative K)
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∀ x, alternativeCode x = embedSourceCode matching scale (z x) := by
  intro x
  apply hinjective _ _ (halternativeSparse x)
  · exact (Finset.card_le_card
      (nonzeroSupport_embedSourceCode_subset matching scale (z x))).trans
      (Finset.card_image_le.trans (hsourceSparse x))
  · exact (halternativeFactors x).symm.trans
      ((hfactors x).trans (mulVec_embedSourceCode matrix alternative matching
        scale hcolumns (z x)).symm)

/-- Source-faithful rigidity at arbitrary learned width: two exact
equal-sparsity factorizations with open support richness, source independence
through `K + 1`, and unique alternative sparse codes agree on all source
atoms and all observed codes. Extra learned columns have zero coefficients. -/
theorem dictionary_and_code_embedding_of_openRich_and_injective_alternative
    {X : Type*} {d M M' K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hKltM : K < M)
    (hcutoff : K + 1 < spark matrix)
    (hinjective : KSparseInjective alternative K)
    (hrich : OpenKRich (K := K) z)
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin M', ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      (∀ i, matrix.col i = scale i • alternative.col (matching i)) ∧
      (∀ x, alternativeCode x = embedSourceCode matching scale (z x)) ∧
      ∀ x j, j ∉ Set.range matching → alternativeCode x j = 0 := by
  classical
  obtain ⟨matching, scale, hscale, hcolumns⟩ :=
    source_columns_embed_of_openRich_and_injective_alternative matrix z f
      alternative alternativeCode hKpos hKltM hcutoff hinjective hrich hfactors
      halternativeSparse halternativeFactors
  have hcodes := alternative_code_eq_embedded_source_code matrix z f alternative
    alternativeCode matching scale hcolumns hinjective hsourceSparse hfactors
    halternativeSparse halternativeFactors
  refine ⟨matching, scale, hscale, hcolumns, hcodes, ?_⟩
  intro x j hj
  rw [hcodes x]
  apply Finset.sum_eq_zero
  intro i _
  have hne : matching i ≠ j := fun heq => hj ⟨i, heq⟩
  simp [hne]

/-- Two featurizations at the same sparsity agree on the entire source
dictionary and all observed coefficients, even if the alternative has extra
columns. The manuscript's strict spark assumptions imply the independence
and sparse-injectivity hypotheses of the arbitrary-width theorem. -/
theorem featurization_dictionary_and_code_embedding
    {X : Type*} {d M M' K : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {z : X → FeatureVector M}
    {f : X → RepresentationVector d}
    {alternative : Matrix (Fin d) (Fin M') ℝ}
    {alternativeCode : X → FeatureVector M'}
    (hKpos : 0 < K)
    (hsource : IsFeaturization K matrix z f)
    (hrich : OpenKRich (K := K) z)
    (halt : IsFeaturization K alternative alternativeCode f) :
    ∃ matching : Fin M ↪ Fin M', ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      (∀ i, matrix.col i = scale i • alternative.col (matching i)) ∧
      (∀ x, alternativeCode x = embedSourceCode matching scale (z x)) ∧
      ∀ x j, j ∉ Set.range matching → alternativeCode x j = 0 := by
  have hKltM : K < M := by
    have hbound := spark_le_column_count_succ matrix
    have hspark := hsource.2.2
    omega
  have hcutoff : K + 1 < spark matrix := by
    have hspark := hsource.2.2
    omega
  have hinjective : KSparseInjective alternative K :=
    (kSparseInjective_iff_min_lt_spark alternative).mpr
      ((Nat.min_le_left (2 * K) M').trans_lt halt.2.2)
  exact dictionary_and_code_embedding_of_openRich_and_injective_alternative
    matrix z f alternative alternativeCode hKpos hKltM hcutoff hinjective hrich
    hsource.1 hsource.2.1 halt.1 halt.2.1

/-- An equal-sparsity alternative featurization that actually uses every
learned coordinate has exactly the source width. Redundant unused columns
are the only possible width surplus under these hypotheses. -/
theorem featurization_width_eq_of_all_alternative_coordinates_used
    {X : Type*} {d M M' K : ℕ}
    {matrix : Matrix (Fin d) (Fin M) ℝ} {z : X → FeatureVector M}
    {f : X → RepresentationVector d}
    {alternative : Matrix (Fin d) (Fin M') ℝ}
    {alternativeCode : X → FeatureVector M'}
    (hKpos : 0 < K)
    (hsource : IsFeaturization K matrix z f)
    (hrich : OpenKRich (K := K) z)
    (halt : IsFeaturization K alternative alternativeCode f)
    (hused : ∀ j, ∃ x, alternativeCode x j ≠ 0) : M = M' := by
  obtain ⟨matching, _, _, _, _, hunused⟩ :=
    featurization_dictionary_and_code_embedding hKpos hsource hrich halt
  have hsurjective : Function.Surjective matching := by
    intro j
    by_contra hnot
    obtain ⟨x, hx⟩ := hused j
    exact hx (hunused x j hnot)
  simpa using Fintype.card_congr (Equiv.ofBijective matching
    ⟨matching.injective, hsurjective⟩)

end PKG26AtomicFeatures
