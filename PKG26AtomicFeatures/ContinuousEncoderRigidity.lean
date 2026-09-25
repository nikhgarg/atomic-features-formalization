import PKG26AtomicFeatures.OvercompleteIdentifiability

/-!
# Exact atom recovery from continuity at source atoms

An exact sparse encoder that is continuous at a source atom cannot keep
using a learned column outside any source support space containing that
atom. A finite open-cover argument proves this local restriction. Source
independence then identifies the intersection of those spaces with the
source atom's line. No learned sparse-injectivity hypothesis is needed.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators Topology

/-- A learned coordinate active at a point of a fully reconstructed
`K`-dimensional source space must be a column in that space. Continuity
is required only at that point; learned columns may be dependent. -/
theorem active_column_mem_of_continuous_sparse_reconstruction
    {d m K : ℕ} (alternative : Matrix (Fin d) (Fin m) ℝ)
    (encoder : RepresentationVector d → FeatureVector m)
    (U : Submodule ℝ (RepresentationVector d))
    (hdim : Module.finrank ℝ U = K) (a : RepresentationVector d) (ha : a ∈ U)
    (hcontinuous : ContinuousWithinAt encoder (U : Set (RepresentationVector d)) a)
    (hsparse : ∀ x ∈ U, (nonzeroSupport (encoder x)).card ≤ K)
    (hexact : ∀ x ∈ U, alternative.mulVec (encoder x) = x)
    (j : Fin m) (hactive : encoder a j ≠ 0) :
    alternative.col j ∈ U := by
  classical
  let aU : U := ⟨a, ha⟩
  have hcoord : ContinuousAt (fun x : U => encoder (x : RepresentationVector d) j) aU :=
    (continuous_apply j).continuousAt.comp
      ((continuousWithinAt_iff_continuousAt_restrict encoder ha).mp hcontinuous)
  have hneighborhood : {x : U | encoder (x : RepresentationVector d) j ≠ 0} ∈ 𝓝 aU :=
    hcoord.eventually_ne hactive
  obtain ⟨region, hregion, hopen, hpoint⟩ := mem_nhds_iff.mp hneighborhood
  let targets (s : {s : Finset (Fin m) // s.card ≤ K ∧ j ∈ s}) :=
    Submodule.comap U.subtype (columnSpan alternative s.val)
  have hcover : region ⊆ ⋃ s, (targets s : Set U) := by
    intro x hx
    let support := nonzeroSupport (encoder (x : RepresentationVector d))
    have hj : j ∈ support := (mem_nonzeroSupport_iff _ _).mpr (hregion hx)
    let s : {s : Finset (Fin m) // s.card ≤ K ∧ j ∈ s} :=
      ⟨support, hsparse x x.property, hj⟩
    refine Set.mem_iUnion.mpr ⟨s, ?_⟩
    change (x : RepresentationVector d) ∈ columnSpan alternative support
    rw [← hexact x x.property]
    exact mulVec_mem_columnSpan_nonzeroSupport alternative _
  obtain ⟨s, hs⟩ := exists_submodule_eq_top_of_open_cover targets region hopen
    ⟨aU, hpoint⟩ hcover
  have hsubset : U ≤ columnSpan alternative s.val := by
    intro x hx
    have hmem : (⟨x, hx⟩ : U) ∈ targets s := by rw [hs]; exact Submodule.mem_top
    exact hmem
  have heq : U = columnSpan alternative s.val :=
    Submodule.eq_of_le_of_finrank_le hsubset
      ((finrank_columnSpan_le_card alternative s.val).trans (by simpa [hdim] using s.property.1))
  rw [heq]
  exact Submodule.subset_span ⟨⟨j, s.property.2⟩, rfl⟩

/-- Membership in a selected column span supplies a coefficient vector
supported inside the selected indices, not just a cardinality bound. -/
theorem exists_code_supported_on_of_mem_columnSpan
    {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (coordinates : Finset (Fin M)) (x : RepresentationVector d)
    (hx : x ∈ columnSpan matrix coordinates) :
    ∃ code : FeatureVector M,
      nonzeroSupport code ⊆ coordinates ∧ matrix.mulVec code = x := by
  rw [← map_mulVecLin_coordinateSpan_eq_columnSpan] at hx
  obtain ⟨code, hcode, heq⟩ := hx
  exact ⟨code, nonzeroSupport_subset_of_mem_coordinateSpan hcode, heq⟩

/-- The intersection of all `K`-column source spaces containing atom `i`
is its line. Independence through `K + 1` columns suffices. -/
theorem mem_source_atom_line_of_mem_all_support_spans
    {d M K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (hKpos : 0 < K) (hKlt : K < M) (hspark : K + 1 < spark matrix)
    (i : Fin M) (x : RepresentationVector d)
    (hmem : ∀ coordinates : Finset (Fin M), coordinates.card = K →
      i ∈ coordinates → x ∈ columnSpan matrix coordinates) :
    x ∈ ℝ ∙ matrix.col i := by
  classical
  obtain ⟨S, hcontains, hcard⟩ := Finset.exists_superset_card_eq
    (show ({i} : Finset (Fin M)).card ≤ K by simp; omega)
    (show K ≤ Fintype.card (Fin M) by simpa using hKlt.le)
  have hiS : i ∈ S := hcontains (Finset.mem_singleton_self i)
  obtain ⟨code, hsupport, hcode⟩ :=
    exists_code_supported_on_of_mem_columnSpan matrix S x (hmem S hcard hiS)
  obtain ⟨j, _, hjS⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show S.card < (Finset.univ : Finset (Fin M)).card by simpa [hcard] using hKlt)
  have hsingle : nonzeroSupport code ⊆ {i} := by
    intro k hk
    by_contra hki
    have hk_ne : k ≠ i := by simpa using hki
    have hkS : k ∈ S := hsupport hk
    have hjk : j ≠ k := fun heq => hjS (heq ▸ hkS)
    let T := insert j (S.erase k)
    have hj_erase : j ∉ S.erase k := fun hj => hjS (Finset.mem_of_mem_erase hj)
    have hTcard : T.card = K := by
      simp only [T, Finset.card_insert_of_notMem hj_erase, Finset.card_erase_of_mem hkS, hcard]
      omega
    have hiT : i ∈ T := Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨Ne.symm hk_ne, hiS⟩)
    obtain ⟨other, hother_support, hother⟩ :=
      exists_code_supported_on_of_mem_columnSpan matrix T x (hmem T hTcard hiT)
    have hunion : S ∪ T = insert j S := by
      ext l
      simp only [T, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
      aesop
    have hdiff_support : nonzeroSupport (code - other) ⊆ S ∪ T :=
      (nonzeroSupport_sub_subset code other).trans
        (Finset.union_subset_union hsupport hother_support)
    have hdiff_card : (nonzeroSupport (code - other)).card < spark matrix := by
      have hle := Finset.card_le_card hdiff_support
      rw [hunion, Finset.card_insert_of_notMem hjS, hcard] at hle
      exact hle.trans_lt hspark
    have hdiff_zero : matrix.mulVec (code - other) = 0 := by
      rw [Matrix.mulVec_sub, hcode, hother, sub_self]
    have heq : code = other := sub_eq_zero.mp
      (eq_zero_of_mulVec_eq_zero_of_support_lt_spark matrix _ hdiff_card hdiff_zero)
    have hkT : k ∈ T := hother_support (heq ▸ hk)
    simp only [T, Finset.mem_insert, Finset.mem_erase] at hkT
    rcases hkT with hkj | ⟨hkk, _⟩
    · exact hjk hkj.symm
    · exact hkk rfl
  have hx : x ∈ columnSpan matrix {i} := by
    rw [← hcode]
    exact columnSpan_mono matrix hsingle (mulVec_mem_columnSpan_nonzeroSupport matrix code)
  simpa only [← familySpan_matrix_columns_eq_columnSpan, familySpan_singleton] using hx

/-- A coordinate singleton is one-sparse, including when its coefficient is zero. -/
theorem nonzeroSupport_single_card_le_one {M : ℕ} (i : Fin M) (a : ℝ) :
    (nonzeroSupport (Pi.single i a : FeatureVector M)).card ≤ 1 := by
  classical
  have hsub : nonzeroSupport (Pi.single i a : FeatureVector M) ⊆ {i} := by
    intro j hj
    by_contra hji
    have hne : j ≠ i := by simpa using hji
    have hz : (Pi.single i a : FeatureVector M) j = 0 := by simp [hne]
    exact (mem_nonzeroSupport_iff _ _).mp hj hz
  simpa using Finset.card_le_card hsub

theorem mulVec_single_real {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (i : Fin M) (a : ℝ) :
    matrix.mulVec (Pi.single i a) = a • matrix.col i := by
  ext row
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

/-- Every nonzero reconstructed vector uses at least one nonzero column
with a nonzero coefficient. No independence of learned columns is assumed. -/
theorem exists_active_nonzero_column_of_mulVec_ne_zero
    {d m : ℕ} (matrix : Matrix (Fin d) (Fin m) ℝ) (code : FeatureVector m)
    (hne : matrix.mulVec code ≠ 0) :
    ∃ j, code j ≠ 0 ∧ matrix.col j ≠ 0 := by
  classical
  by_contra hnot
  push Not at hnot
  apply hne
  ext row
  change (∑ j, matrix row j * code j) = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : code j = 0
  · simp [hj]
  · have hcol := congrFun (hnot j hj) row
    simp only [Matrix.col_apply, Pi.zero_apply] at hcol
    simp [hcol]

/-- Exact equal-sparsity reconstruction with continuity at the pure source
atoms recovers every source column at arbitrary learned width.

The reconstruction and sparsity assumptions hold on the entire sparse
source image. The encoder only needs to be continuous relative to that image
at the finitely many pure source atoms. Independence through `K + 1` is sufficient;
the learned dictionary can have arbitrary dependencies and redundancy.
No conclusion that surplus learned coordinates are unused is asserted. -/
theorem source_columns_embed_of_encoder_continuous_at_atoms
    {d M m K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin m) ℝ)
    (encoder : RepresentationVector d → FeatureVector m)
    (hKpos : 0 < K) (hKlt : K < M) (hspark : K + 1 < spark matrix)
    (hcontinuous : ∀ i, ContinuousWithinAt encoder
      (SparseSubspaceUnion matrix K) (matrix.col i))
    (hsparse : ∀ code : FeatureVector M, (nonzeroSupport code).card ≤ K →
      (nonzeroSupport (encoder (matrix.mulVec code))).card ≤ K)
    (hexact : ∀ code : FeatureVector M, (nonzeroSupport code).card ≤ K →
      alternative.mulVec (encoder (matrix.mulVec code)) = matrix.mulVec code) :
    ∃ matching : Fin M ↪ Fin m, ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
        ∀ i, alternative.col (matching i) = scale i • matrix.col i := by
  classical
  have hsource_ne (i : Fin M) : matrix.col i ≠ 0 := by
    have hli := linearIndependent_of_card_lt_spark matrix ({i} : Finset (Fin M))
      (by simp; omega)
    have hne := hli.ne_zero (⟨i, Finset.mem_singleton_self _⟩ :
      {j // j ∈ ({i} : Finset (Fin M))})
    simpa [selectedColumns] using hne
  have hpoint_exact (i : Fin M) :
      alternative.mulVec (encoder (matrix.col i)) = matrix.col i := by
    simpa only [Matrix.mulVec_single_one] using
      hexact (Pi.single i 1) ((nonzeroSupport_single_card_le_one i 1).trans hKpos)
  have hcolumn_mem (i : Fin M) (j : Fin m) (hj : encoder (matrix.col i) j ≠ 0) :
      alternative.col j ∈ ℝ ∙ matrix.col i := by
    apply mem_source_atom_line_of_mem_all_support_spans matrix hKpos hKlt hspark i
    intro coordinates hcard hi
    have hdim : Module.finrank ℝ (columnSpan matrix coordinates) = K := by
      rw [finrank_columnSpan_eq_card matrix coordinates
        (linearIndependent_of_card_lt_spark matrix coordinates (by omega)), hcard]
    have hsource_mem : matrix.col i ∈ columnSpan matrix coordinates :=
      Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    apply active_column_mem_of_continuous_sparse_reconstruction alternative encoder
      (columnSpan matrix coordinates) hdim (matrix.col i) hsource_mem
      ((hcontinuous i).mono (fun x hx => Set.mem_iUnion.mpr ⟨⟨coordinates, hcard⟩, hx⟩))
    · intro x hx
      obtain ⟨code, hsupport, hcode⟩ :=
        exists_code_supported_on_of_mem_columnSpan matrix coordinates x hx
      rw [← hcode]
      exact hsparse code ((Finset.card_le_card hsupport).trans hcard.le)
    · intro x hx
      obtain ⟨code, hsupport, hcode⟩ :=
        exists_code_supported_on_of_mem_columnSpan matrix coordinates x hx
      rw [← hcode]
      exact hexact code ((Finset.card_le_card hsupport).trans hcard.le)
    · exact hj
  have hexists (i : Fin M) : ∃ j : Fin m, ∃ scale : ℝ,
      scale ≠ 0 ∧ alternative.col j = scale • matrix.col i := by
    obtain ⟨j, hj, hjne⟩ := exists_active_nonzero_column_of_mulVec_ne_zero alternative
      (encoder (matrix.col i)) (by rw [hpoint_exact]; exact hsource_ne i)
    obtain ⟨scale, hscale⟩ := Submodule.mem_span_singleton.mp (hcolumn_mem i j hj)
    refine ⟨j, scale, ?_, hscale.symm⟩
    intro hz
    exact hjne (by rw [← hscale, hz, zero_smul])
  choose matching scale hscale hcolumns using hexists
  have hinjective : Function.Injective matching := by
    intro i k hik
    by_contra hne
    have hsource_injective : KSparseInjective matrix 1 :=
      (kSparseInjective_iff_min_lt_spark matrix).mpr
        ((Nat.min_le_left (2 * 1) M).trans_lt (by omega))
    have himages : matrix.mulVec (Pi.single i (scale i)) =
        matrix.mulVec (Pi.single k (scale k)) := by
      rw [mulVec_single_real, mulVec_single_real, ← hcolumns i, ← hcolumns k, hik]
    have hcodes := hsource_injective _ _ (nonzeroSupport_single_card_le_one i (scale i))
      (nonzeroSupport_single_card_le_one k (scale k)) himages
    have hz := congrFun hcodes i
    have hzero : scale i = 0 := by simpa [Pi.single_apply, hne, Ne.symm hne] using hz
    exact hscale i hzero
  exact ⟨⟨matching, hinjective⟩, scale, hscale, hcolumns⟩

end PKG26AtomicFeatures
