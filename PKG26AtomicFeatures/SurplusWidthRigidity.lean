import PKG26AtomicFeatures.ContinuousEncoderRigidity

/-!
# Rigidity below twice the source width

If one source atom is missing, every learned column used to span a source
support must share a different source index with every support using it.
Integer multiplicities of those indices force width at least `2 * M - K`.
No learned sparse-injectivity or encoder-continuity hypothesis is needed.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- If every `k` selected integer weights sum to more than `k`, all but
at most `k - 1` indices have weight at least two. Extending the exceptional
set to size `k` gives the sharp total bound. -/
theorem two_mul_card_le_sum_add_of_small_subsums
    {ι : Type*} [DecidableEq ι] (domain : Finset ι) (weight : ι → ℕ)
    (k : ℕ) (hk : k ≤ domain.card)
    (hsubsum : ∀ selected : Finset ι, selected ⊆ domain → selected.card = k →
      k + 1 ≤ ∑ i ∈ selected, weight i) :
    2 * domain.card + 1 ≤ (∑ i ∈ domain, weight i) + k := by
  classical
  let low := domain.filter (fun i => weight i ≤ 1)
  have hlow_domain : low ⊆ domain := Finset.filter_subset _ _
  have hlow_card : low.card < k := by
    by_contra hnot
    obtain ⟨selected, hselected, hcard⟩ :=
      Finset.exists_subset_card_eq (show k ≤ low.card by omega)
    have hupper : (∑ i ∈ selected, weight i) ≤ k := by
      calc
        (∑ i ∈ selected, weight i) ≤ ∑ _i ∈ selected, 1 :=
          Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp (hselected hi)).2)
        _ = k := by simp [hcard]
    have hlower := hsubsum selected (hselected.trans hlow_domain) hcard
    omega
  obtain ⟨selected, hlow_selected, hselected_domain, hcard⟩ :=
    Finset.exists_subsuperset_card_eq hlow_domain hlow_card.le hk
  have hremaining : ∀ i ∈ domain \ selected, 2 ≤ weight i := by
    intro i hi
    obtain ⟨hidomain, hinot⟩ := Finset.mem_sdiff.mp hi
    by_contra hnot
    have hilow : i ∈ low := Finset.mem_filter.mpr ⟨hidomain, by omega⟩
    exact hinot (hlow_selected hilow)
  have hremaining_sum : 2 * (domain \ selected).card ≤
      ∑ i ∈ domain \ selected, weight i := by
    calc
      2 * (domain \ selected).card = ∑ _i ∈ domain \ selected, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ domain \ selected, weight i := Finset.sum_le_sum hremaining
  have hselected_sum := hsubsum selected hselected_domain hcard
  have hsplit := Finset.sum_sdiff hselected_domain (f := weight)
  have hcard_split := Finset.card_sdiff_add_card_eq_card hselected_domain
  omega

/-- If each selected learned column shares a source index other than `i`
with every source support using it, then one missing atom costs width
at least `2 * M - K`. -/
theorem width_bound_of_other_index_on_every_selected_support
    {M m K : ℕ} (i : Fin M) (hKpos : 0 < K) (hKlt : K < M)
    (partner : Fin m → Fin M) (havoid : ∀ j, partner j ≠ i)
    (selected : CardSubset (Fin M) K → Finset (Fin m))
    (hcard : ∀ source, (selected source).card = K)
    (hpartner : ∀ source j, j ∈ selected source → partner j ∈ source.val) :
    2 * M ≤ m + K := by
  classical
  let domain : Finset (Fin M) := Finset.univ.erase i
  let weight (k : Fin M) := (Finset.univ.filter (fun j : Fin m => partner j = k)).card
  have hdomain : domain.card + 1 = M := by
    simp only [domain, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hsubsum (R : Finset (Fin M)) (hR : R ⊆ domain) (hRcard : R.card = K - 1) :
      K - 1 + 1 ≤ ∑ k ∈ R, weight k := by
    have hiR : i ∉ R := fun hi => (Finset.mem_erase.mp (hR hi)).1 rfl
    let source : CardSubset (Fin M) K :=
      ⟨insert i R, by rw [Finset.card_insert_of_notMem hiR, hRcard]; omega⟩
    have hcontained : selected source ⊆
        Finset.univ.filter (fun j : Fin m => partner j ∈ R) := by
      intro j hj
      have hmem := hpartner source j hj
      change partner j ∈ insert i R at hmem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_insert.mp hmem).resolve_left (havoid j)⟩
    have hle := Finset.card_le_card hcontained
    rw [hcard source] at hle
    simp only [weight]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    omega
  have htotal : (∑ k ∈ domain, weight k) = m := by
    simp only [weight]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    have hfilter : Finset.univ.filter (fun j : Fin m => partner j ∈ domain) =
        Finset.univ := by
      ext j
      simp [domain, havoid j]
    rw [hfilter, Finset.card_univ, Fintype.card_fin]
  have hbound := two_mul_card_le_sum_add_of_small_subsums domain weight (K - 1)
    (by omega) hsubsum
  rw [htotal] at hbound
  omega

/-- A vector outside one atom's line has a different nonzero source
coordinate that belongs to every sparse source space containing it.
Sparse injectivity makes that coordinate independent of the representation. -/
theorem exists_other_coordinate_in_all_source_supports
    {d M K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (hinjective : KSparseInjective matrix K) (i : Fin M)
    (v : RepresentationVector d) (hline : v ∉ ℝ ∙ matrix.col i)
    (hmem : ∃ source : CardSubset (Fin M) K, v ∈ columnSpan matrix source.val) :
    ∃ k : Fin M, k ≠ i ∧
      ∀ source : CardSubset (Fin M) K, v ∈ columnSpan matrix source.val → k ∈ source.val := by
  classical
  obtain ⟨source, hsource⟩ := hmem
  obtain ⟨code, hsupport, hcode⟩ :=
    exists_code_supported_on_of_mem_columnSpan matrix source.val v hsource
  have hnot_single : ¬nonzeroSupport code ⊆ {i} := by
    intro hsingle
    apply hline
    have hv : v ∈ columnSpan matrix {i} := by
      rw [← hcode]
      exact columnSpan_mono matrix hsingle (mulVec_mem_columnSpan_nonzeroSupport matrix code)
    simpa only [← familySpan_matrix_columns_eq_columnSpan, familySpan_singleton] using hv
  obtain ⟨k, hk, hki⟩ := Finset.not_subset.mp hnot_single
  refine ⟨k, by simpa using hki, ?_⟩
  intro other hother
  obtain ⟨otherCode, hother_support, hotherCode⟩ :=
    exists_code_supported_on_of_mem_columnSpan matrix other.val v hother
  have hequal : code = otherCode := hinjective code otherCode
    ((Finset.card_le_card hsupport).trans source.property.le)
    ((Finset.card_le_card hother_support).trans other.property.le)
    (hcode.trans hotherCode.symm)
  exact hother_support (hequal ▸ hk)

/-- Source support spaces represented with `K` learned columns force every
source atom to appear below width `2 * M - K`. The selected spaces are a
geometric intermediate premise, derived from richness by the final theorem. -/
theorem source_atoms_present_of_support_spans_and_surplus_width_bound
    {d M m K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (hinjective : KSparseInjective matrix K)
    (hKpos : 0 < K) (hKlt : K < M) (hwidth : m + K < 2 * M)
    (selected : CardSubset (Fin M) K → CardSubset (Fin m) K)
    (hspan : ∀ source, columnSpan matrix source.val =
      columnSpan alternative (selected source).val) :
    ∀ i : Fin M, ∃ j : Fin m, ∃ scale : ℝ,
      scale ≠ 0 ∧ alternative.col j = scale • matrix.col i := by
  classical
  have hspark := (kSparseInjective_iff_min_lt_spark matrix).mp hinjective
  have hKspark : K < spark matrix :=
    (Nat.le_min.mpr ⟨by omega, hKlt.le⟩).trans_lt hspark
  have htargetLI (source : CardSubset (Fin M) K) :
      LinearIndependent ℝ (selectedColumns alternative (selected source).val) := by
    have hdim : Module.finrank ℝ (columnSpan alternative (selected source).val) = K := by
      rw [← hspan source, finrank_columnSpan_eq_card matrix source.val
        (linearIndependent_of_card_lt_spark matrix source.val (by simpa [source.property])),
        source.property]
    rw [linearIndependent_iff_card_eq_finrank_span]
    simpa [selectedColumns, columnSpan, (selected source).property] using hdim.symm
  have hcolumn_mem (source : CardSubset (Fin M) K) (j : Fin m)
      (hj : j ∈ (selected source).val) : alternative.col j ∈ columnSpan matrix source.val := by
    rw [hspan source]
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  intro i
  by_contra hmissing
  push Not at hmissing
  have hpartners (j : Fin m) : ∃ k : Fin M, k ≠ i ∧
      ∀ source, j ∈ (selected source).val → k ∈ source.val := by
    by_cases hused : ∃ source, j ∈ (selected source).val
    · obtain ⟨source, hj⟩ := hused
      have hnonzero : alternative.col j ≠ 0 := by
        simpa [selectedColumns] using (htargetLI source).ne_zero ⟨j, hj⟩
      have hnotline : alternative.col j ∉ ℝ ∙ matrix.col i := by
        intro hline
        obtain ⟨scale, hscale⟩ := Submodule.mem_span_singleton.mp hline
        have hscale_ne : scale ≠ 0 := by
          intro hz
          apply hnonzero
          rw [← hscale, hz, zero_smul]
        exact hmissing j scale hscale_ne hscale.symm
      obtain ⟨k, hki, hcommon⟩ := exists_other_coordinate_in_all_source_supports matrix
        hinjective i (alternative.col j) hnotline ⟨source, hcolumn_mem source j hj⟩
      exact ⟨k, hki, fun other hother => hcommon other (hcolumn_mem other j hother)⟩
    · obtain ⟨k, _, hki⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (show ({i} : Finset (Fin M)).card < (Finset.univ : Finset (Fin M)).card by
          simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin]
          omega)
      exact ⟨k, by simpa using hki, fun source hj => (hused ⟨source, hj⟩).elim⟩
  choose partner havoid hpartner using hpartners
  have hbound := width_bound_of_other_index_on_every_selected_support i hKpos hKlt
    partner havoid (fun source => (selected source).val)
    (fun source => (selected source).property) (fun source j hj => hpartner j source hj)
  omega

/-- Relative open richness gives an equal-dimensional learned support at
arbitrary width. The exact support cardinality follows from source rank. -/
theorem exists_equal_card_alternative_span_of_openRich
    {X : Type*} {d M m K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (alternativeCode : X → FeatureVector m)
    (hKspark : K < spark matrix) (hrich : OpenKRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x))
    (source : CardSubset (Fin M) K) :
    ∃ target : CardSubset (Fin m) K,
      columnSpan matrix source.val = columnSpan alternative target.val := by
  classical
  obtain ⟨support, hcontain⟩ := exists_sparse_alternative_subspace_of_openKRich matrix
    z f alternative alternativeCode hrich hfactors halternativeSparse halternativeFactors
    source.val source.property
  rw [map_mulVecLin_coordinateSpan_eq_columnSpan] at hcontain
  have hdim : Module.finrank ℝ (columnSpan matrix source.val) = K := by
    rw [finrank_columnSpan_eq_card matrix source.val
      (linearIndependent_of_card_lt_spark matrix source.val (by simpa [source.property])),
      source.property]
  have htarget_dim := finrank_columnSpan_le_card alternative support.val
  have hdim_le := Submodule.finrank_mono hcontain
  have hcard : support.val.card = K := by
    rw [hdim] at hdim_le
    have hle := support.property
    omega
  refine ⟨⟨support.val, hcard⟩, Submodule.eq_of_le_of_finrank_le hcontain ?_⟩
  simpa [hdim, hcard] using htarget_dim

/-- Exact equal-sparsity factorization recovers every source column when
the learned width is less than `2 * M - K`.

The source is injective on `K`-sparse codes and relatively open-rich.
The learned dictionary and encoder need no injectivity, conditioning,
or continuity. Every source column embeds with a nonzero scale; surplus
learned coordinates need not be unused. -/
theorem source_columns_embed_below_twice_width_of_openRich
    {X : Type*} {d M m K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (alternativeCode : X → FeatureVector m)
    (hKpos : 0 < K) (hKlt : K < M) (hwidth : m + K < 2 * M)
    (hinjective : KSparseInjective matrix K) (hrich : OpenKRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin m, ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
        ∀ i, alternative.col (matching i) = scale i • matrix.col i := by
  classical
  have hspark := (kSparseInjective_iff_min_lt_spark matrix).mp hinjective
  have hKspark : K < spark matrix :=
    (Nat.le_min.mpr ⟨by omega, hKlt.le⟩).trans_lt hspark
  have hselected : ∀ source : CardSubset (Fin M) K,
      ∃ target : CardSubset (Fin m) K,
        columnSpan matrix source.val = columnSpan alternative target.val :=
    exists_equal_card_alternative_span_of_openRich matrix z f alternative alternativeCode
      hKspark hrich hfactors halternativeSparse halternativeFactors
  choose selected hspan using hselected
  have hpresent := source_atoms_present_of_support_spans_and_surplus_width_bound matrix
    alternative hinjective hKpos hKlt hwidth selected hspan
  choose matching scale hscale hcolumns using hpresent
  have hmatching : Function.Injective matching := by
    intro i k hik
    by_contra hne
    have himages : matrix.mulVec (Pi.single i (scale i)) =
        matrix.mulVec (Pi.single k (scale k)) := by
      rw [mulVec_single_real, mulVec_single_real, ← hcolumns i, ← hcolumns k, hik]
    have hcodes := hinjective _ _
      ((nonzeroSupport_single_card_le_one i (scale i)).trans hKpos)
      ((nonzeroSupport_single_card_le_one k (scale k)).trans hKpos) himages
    have hz := congrFun hcodes i
    have hzero : scale i = 0 := by simpa [Pi.single_apply, hne, Ne.symm hne] using hz
    exact hscale i hzero
  exact ⟨⟨matching, hmatching⟩, scale, hscale, hcolumns⟩

/-- Source-featurization specialization of the surplus-width theorem.
Only the source has the paper's spark condition; the learned pair need
only be an exact `K`-sparse factorization. -/
theorem source_featurization_columns_embed_below_twice_width
    {X : Type*} {d M m K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (alternativeCode : X → FeatureVector m)
    (hKpos : 0 < K) (hKlt : K < M) (hwidth : m + K < 2 * M)
    (hsource : IsFeaturization K matrix z f) (hrich : OpenKRich (K := K) z)
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin m, ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
        ∀ i, alternative.col (matching i) = scale i • matrix.col i := by
  exact source_columns_embed_below_twice_width_of_openRich matrix z f alternative
    alternativeCode hKpos hKlt hwidth
    ((kSparseInjective_iff_min_lt_spark matrix).mpr
      ((Nat.min_le_left (2 * K) M).trans_lt hsource.2.2))
    hrich hsource.2.1 halternativeSparse halternativeFactors

end PKG26AtomicFeatures
