import PKG26AtomicFeatures.SurplusWidthRigidity

/-!
# Exact rigidity from separating observed support patterns

At equal dictionary widths, source supports need only cover and separate
the source coordinates. Each used learned column has one consistent sparse
source representation. Those representations form an invertible square
matrix; a nonzero determinant term gives a single support-compatible column
permutation. Separation then forces each lifted column onto its source axis.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators Topology

/-- A nonzero determinant supplies a bijection supported on nonzero entries.
This is one term in the determinant expansion, not a separate matching premise. -/
theorem exists_permutation_nonzero_entries_of_det_ne_zero
    {M : ℕ} (C : Matrix (Fin M) (Fin M) ℝ) (hdet : C.det ≠ 0) :
    ∃ p : Equiv.Perm (Fin M), ∀ j, C (p j) j ≠ 0 := by
  classical
  rw [Matrix.det_apply'] at hdet
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hprod : (∏ j, C (p j) j) ≠ 0 := (mul_ne_zero_iff.mp hp).2
  exact ⟨p, fun j => (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ j)⟩

/-- Equal learned support spans lift consistently to sparse source coordinates.
Unused learned columns are assigned the zero vector. Sparse injectivity of
the source makes each lift independent of the support used to obtain it. -/
theorem exists_consistent_source_column_lifts
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (source : ι → CardSubset (Fin M) K)
    (target : ι → CardSubset (Fin m) K)
    (hinjective : KSparseInjective A K)
    (hspan : ∀ s, columnSpan A (source s).val = columnSpan B (target s).val) :
    ∃ code : Fin m → FeatureVector M,
      (∀ j s, j ∈ (target s).val →
        nonzeroSupport (code j) ⊆ (source s).val ∧ A.mulVec (code j) = B.col j) ∧
      (∀ j, (¬∃ s, j ∈ (target s).val) → code j = 0) := by
  classical
  have hmem (s : ι) (j : Fin m) (hj : j ∈ (target s).val) :
      B.col j ∈ columnSpan A (source s).val := by
    rw [hspan s]
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  have hexists (j : Fin m) : ∃ code : FeatureVector M,
      (∀ s, j ∈ (target s).val →
        nonzeroSupport code ⊆ (source s).val ∧ A.mulVec code = B.col j) ∧
      ((¬∃ s, j ∈ (target s).val) → code = 0) := by
    by_cases hused : ∃ s, j ∈ (target s).val
    · obtain ⟨s, hj⟩ := hused
      obtain ⟨code, hsupport, hcode⟩ :=
        exists_code_supported_on_of_mem_columnSpan A _ _ (hmem s j hj)
      refine ⟨code, ?_, fun hnot => (hnot ⟨s, hj⟩).elim⟩
      intro t ht
      obtain ⟨other, hotherSupport, hother⟩ :=
        exists_code_supported_on_of_mem_columnSpan A _ _ (hmem t j ht)
      have heq := hinjective code other
        ((Finset.card_le_card hsupport).trans (source s).property.le)
        ((Finset.card_le_card hotherSupport).trans (source t).property.le)
        (hcode.trans hother.symm)
      exact ⟨heq ▸ hotherSupport, hcode⟩
    · exact ⟨0, fun s hs => (hused ⟨s, hs⟩).elim, fun _ => rfl⟩
  choose code hcode hzero using hexists
  exact ⟨code, hcode, hzero⟩

/-- A linear combination supported on one learned support lifts inside its
source support and has the same reconstructed image. -/
theorem mulVec_source_lift_on_selected_support
    {d M m : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (code : Fin m → FeatureVector M)
    (source : Finset (Fin M)) (target : Finset (Fin m))
    (hcode : ∀ j ∈ target,
      nonzeroSupport (code j) ⊆ source ∧ A.mulVec (code j) = B.col j)
    (u : FeatureVector m) (hu : nonzeroSupport u ⊆ target) :
    nonzeroSupport (Matrix.mulVec (fun i j => code j i) u)
        ⊆ source ∧
      A.mulVec (Matrix.mulVec (fun i j => code j i) u) =
        B.mulVec u := by
  classical
  let C : Matrix (Fin M) (Fin m) ℝ := fun i j => code j i
  have hsum : C.mulVec u = ∑ j, u j • code j := by
    ext i
    simp [C, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hcoord : C.mulVec u ∈ coordinateSpan source := by
    rw [hsum]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : u j = 0
    · simp [hj]
    · exact Submodule.smul_mem _ _
        (mem_coordinateSpan_of_nonzeroSupport_subset
          (hcode j (hu ((mem_nonzeroSupport_iff _ _).mpr hj))).1)
  refine ⟨nonzeroSupport_subset_of_mem_coordinateSpan hcoord, ?_⟩
  change A.mulVecLin (C.mulVec u) = B.mulVec u
  rw [hsum, map_sum, Matrix.mulVec_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, op_smul_eq_smul]
  by_cases hj : u j = 0
  · simp [hj]
  · change u j • A.mulVec (code j) = u j • B.col j
    rw [(hcode j (hu ((mem_nonzeroSupport_iff _ _).mpr hj))).2]

/-- With equal widths, covering and separating source support patterns force
an exact permutation and scaling of columns. Equal support spans are an
intermediate geometric hypothesis; the final theorem derives them from
relative open richness and exact sparse factorization. -/
theorem columns_permute_of_separating_support_spans
    {ι : Type*} {d M K : ℕ}
    (A B : Matrix (Fin d) (Fin M) ℝ)
    (source target : ι → CardSubset (Fin M) K)
    (hKpos : 0 < K) (hinjective : KSparseInjective A K)
    (hcover : ∀ i, ∃ s, i ∈ (source s).val)
    (hseparate : ∀ i k, k ≠ i →
      ∃ s, i ∈ (source s).val ∧ k ∉ (source s).val)
    (hspan : ∀ s, columnSpan A (source s).val = columnSpan B (target s).val) :
    ∃ matching : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧ ∀ i, B.col (matching i) = scale i • A.col i := by
  classical
  obtain ⟨code, hcode, _⟩ :=
    exists_consistent_source_column_lifts A B source target hinjective hspan
  let C : Matrix (Fin M) (Fin M) ℝ := fun i j => code j i
  have hpreimage (i : Fin M) : ∃ u : FeatureVector M,
      C.mulVec u = Pi.single i 1 := by
    obtain ⟨s, hi⟩ := hcover i
    have hmem : A.col i ∈ columnSpan B (target s).val := by
      rw [← hspan s]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    obtain ⟨u, hu, himage⟩ := exists_code_supported_on_of_mem_columnSpan B _ _ hmem
    obtain ⟨hsupport, hlift⟩ := mulVec_source_lift_on_selected_support A B code
      (source s).val (target s).val (fun j hj => hcode j s hj) u hu
    refine ⟨u, hinjective _ _
      ((Finset.card_le_card hsupport).trans (source s).property.le)
      ((nonzeroSupport_single_card_le_one i 1).trans hKpos) ?_⟩
    rw [mulVec_single_real, one_smul]
    exact hlift.trans himage
  choose preimage hpreimage using hpreimage
  let inverse : Matrix (Fin M) (Fin M) ℝ := fun j i => preimage i j
  have hright : C * inverse = 1 := by
    ext i j
    have h := congrFun (hpreimage j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, inverse,
      Matrix.one_apply, Pi.single_apply, eq_comm] using h
  obtain ⟨p, hp⟩ := exists_permutation_nonzero_entries_of_det_ne_zero C
    (Matrix.det_ne_zero_of_right_inverse hright)
  have hselected (s : ι) : (target s).val.image p = (source s).val := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact (hcode j s hj).1 ((mem_nonzeroSupport_iff _ _).mpr (hp j))
    · simp only [Finset.card_image_of_injective _ p.injective,
        (source s).property, (target s).property, le_refl]
  have htarget (s : ι) (i : Fin M) (hi : i ∈ (source s).val) :
      p.symm i ∈ (target s).val := by
    rw [← hselected s] at hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have heq : j = p.symm i := by simpa using congrArg p.symm hji
    exact heq ▸ hj
  have hsingle (i : Fin M) :
      code (p.symm i) = Pi.single i (C i (p.symm i)) := by
    ext k
    by_cases hki : k = i
    · subst k
      simp [C]
    · have hzero : code (p.symm i) k = 0 := by
        obtain ⟨s, hi, hk⟩ := hseparate i k hki
        by_contra hnot
        exact hk ((hcode _ s (htarget s i hi)).1
          ((mem_nonzeroSupport_iff _ _).mpr hnot))
      simp [hki, hzero]
  refine ⟨p.symm, fun i => C i (p.symm i), ?_, ?_⟩
  · intro i
    simpa using hp (p.symm i)
  · intro i
    obtain ⟨s, hi⟩ := hcover i
    rw [← (hcode _ s (htarget s i hi)).2, hsingle i, mulVec_single_real]

/-- One relatively open source patch suffices to select one whole learned
support space. Richness on other supports is not needed for this step. -/
theorem exists_alternative_span_of_one_open_source_patch
    {X : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : X → RepresentationVector d)
    (B : Matrix (Fin d) (Fin m) ℝ) (alternativeCode : X → FeatureVector m)
    (source : Finset (Fin M))
    (hrich : ∃ region : Set (coordinateSpan source),
      IsOpen region ∧ region.Nonempty ∧
        ∀ v ∈ region, (v : FeatureVector M) ∈ closure (Set.range z))
    (hfactors : ∀ x, f x = A.mulVec (z x))
    (hsparse : KSparse (K := K) alternativeCode)
    (hexact : ∀ x, f x = B.mulVec (alternativeCode x)) :
    ∃ target : {s : Finset (Fin m) // s.card ≤ K},
      columnSpan A source ≤ columnSpan B target.val := by
  classical
  let map := A.mulVecLin.comp (coordinateSpan source).subtype
  let spaces (s : {s : Finset (Fin m) // s.card ≤ K}) :=
    Submodule.comap map (columnSpan B s.val)
  obtain ⟨region, hopen, hne, hregion⟩ := hrich
  have hclosure := closure_range_subset_iUnion_of_finite_submodules f
    (fun s : {s : Finset (Fin m) // s.card ≤ K} => columnSpan B s.val)
    (range_subset_iUnion_sparse_columnSpan_of_factors B alternativeCode f hsparse hexact)
  have hcover : region ⊆ ⋃ s, (spaces s : Set (coordinateSpan source)) := by
    intro v hv
    have hcontinuous : Continuous A.mulVecLin := LinearMap.continuous_of_finiteDimensional _
    have himage : A.mulVecLin (v : FeatureVector M) ∈ closure (Set.range f) := by
      apply closure_mono (s := A.mulVecLin '' Set.range z) ?_
        (mem_closure_image hcontinuous.continuousAt (hregion v hv))
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, hfactors x⟩
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hclosure himage)
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨s, hs⟩ := exists_submodule_eq_top_of_open_cover spaces region hopen hne hcover
  refine ⟨s, ?_⟩
  rw [← map_mulVecLin_coordinateSpan_eq_columnSpan]
  rintro _ ⟨v, hv, rfl⟩
  have hmem : (⟨v, hv⟩ : coordinateSpan source) ∈ spaces s := by
    rw [hs]
    exact Submodule.mem_top
  exact hmem

/-- Exact sparse reconstruction at equal width identifies all source columns
when the observed support patterns cover and separate the features.

The source has unique `K`-sparse codes. Each observed support only needs a
nonempty relatively open code patch in the range closure. The learned
dictionary needs neither sparse injectivity nor encoder continuity, and the
observed support family need not contain every `K`-subset or be regular. -/
theorem source_columns_permute_of_openRich_separating_patterns
    {X ι : Type*} {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : X → RepresentationVector d)
    (B : Matrix (Fin d) (Fin M) ℝ) (alternativeCode : X → FeatureVector M)
    (source : ι → CardSubset (Fin M) K)
    (hKpos : 0 < K) (hKle : K ≤ M) (hinjective : KSparseInjective A K)
    (hcover : ∀ i, ∃ s, i ∈ (source s).val)
    (hseparate : ∀ i k, k ≠ i →
      ∃ s, i ∈ (source s).val ∧ k ∉ (source s).val)
    (hrich : ∀ s, ∃ region : Set (coordinateSpan (source s).val),
      IsOpen region ∧ region.Nonempty ∧
        ∀ v ∈ region, (v : FeatureVector M) ∈ closure (Set.range z))
    (hfactors : ∀ x, f x = A.mulVec (z x))
    (hsparse : KSparse (K := K) alternativeCode)
    (hexact : ∀ x, f x = B.mulVec (alternativeCode x)) :
    ∃ matching : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧ ∀ i, B.col (matching i) = scale i • A.col i := by
  classical
  have hKspark : K < spark A :=
    (Nat.le_min.mpr ⟨by omega, hKle⟩).trans_lt
      ((kSparseInjective_iff_min_lt_spark A).mp hinjective)
  have hexists (s : ι) : ∃ target : CardSubset (Fin M) K,
      columnSpan A (source s).val = columnSpan B target.val := by
    obtain ⟨target, hcontain⟩ := exists_alternative_span_of_one_open_source_patch
      A z f B alternativeCode (source s).val (hrich s) hfactors hsparse hexact
    have hdim : Module.finrank ℝ (columnSpan A (source s).val) = K := by
      rw [finrank_columnSpan_eq_card A (source s).val
        (linearIndependent_of_card_lt_spark A (source s).val
          (by simpa [(source s).property] using hKspark)), (source s).property]
    have htarget_dim := finrank_columnSpan_le_card B target.val
    have hdim_le := Submodule.finrank_mono hcontain
    have hcard : target.val.card = K := by
      rw [hdim] at hdim_le
      have hle := target.property
      omega
    refine ⟨⟨target.val, hcard⟩, Submodule.eq_of_le_of_finrank_le hcontain ?_⟩
    simpa [hdim, hcard] using htarget_dim
  choose target hspan using hexists
  exact columns_permute_of_separating_support_spans A B source target
    hKpos hinjective hcover hseparate hspan

/-- Coverage alone forces the learned width to be at least the number of
source features in an exact equal-sparsity representation. Separation is
needed for identifying individual columns, not for this width bound. -/
theorem source_width_le_of_covering_support_spans
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (source : ι → CardSubset (Fin M) K) (target : ι → CardSubset (Fin m) K)
    (hKpos : 0 < K) (hinjective : KSparseInjective A K)
    (hcover : ∀ i, ∃ s, i ∈ (source s).val)
    (hspan : ∀ s, columnSpan A (source s).val = columnSpan B (target s).val) :
    M ≤ m := by
  classical
  obtain ⟨code, hcode, _⟩ :=
    exists_consistent_source_column_lifts A B source target hinjective hspan
  let C : Matrix (Fin M) (Fin m) ℝ := fun i j => code j i
  have hpreimage (i : Fin M) : ∃ u : FeatureVector m,
      C.mulVec u = Pi.single i 1 := by
    obtain ⟨s, hi⟩ := hcover i
    have hmem : A.col i ∈ columnSpan B (target s).val := by
      rw [← hspan s]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    obtain ⟨u, hu, himage⟩ := exists_code_supported_on_of_mem_columnSpan B _ _ hmem
    obtain ⟨hsupport, hlift⟩ := mulVec_source_lift_on_selected_support A B code
      (source s).val (target s).val (fun j hj => hcode j s hj) u hu
    refine ⟨u, hinjective _ _
      ((Finset.card_le_card hsupport).trans (source s).property.le)
      ((nonzeroSupport_single_card_le_one i 1).trans hKpos) ?_⟩
    rw [mulVec_single_real, one_smul]
    exact hlift.trans himage
  choose preimage hpreimage using hpreimage
  let inverse : Matrix (Fin m) (Fin M) ℝ := fun j i => preimage i j
  have hright : C * inverse = 1 := by
    ext i j
    have h := congrFun (hpreimage j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, inverse,
      Matrix.one_apply, Pi.single_apply, eq_comm] using h
  have hsurj : Function.Surjective C.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨inverse, hright⟩
  simpa [FeatureVector] using
    (LinearMap.finrank_le_finrank_of_surjective (f := C.mulVecLin) hsurj)

/-- Exact sparse factorization and open richness on a covering support family
exclude every narrower learned dictionary. No support separation, learned
sparse injectivity, or encoder continuity is assumed. -/
theorem source_width_le_of_openRich_covering_patterns
    {X ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : X → RepresentationVector d)
    (B : Matrix (Fin d) (Fin m) ℝ) (alternativeCode : X → FeatureVector m)
    (source : ι → CardSubset (Fin M) K)
    (hKpos : 0 < K) (hKle : K ≤ M) (hinjective : KSparseInjective A K)
    (hcover : ∀ i, ∃ s, i ∈ (source s).val)
    (hrich : ∀ s, ∃ region : Set (coordinateSpan (source s).val),
      IsOpen region ∧ region.Nonempty ∧
        ∀ v ∈ region, (v : FeatureVector M) ∈ closure (Set.range z))
    (hfactors : ∀ x, f x = A.mulVec (z x))
    (hsparse : KSparse (K := K) alternativeCode)
    (hexact : ∀ x, f x = B.mulVec (alternativeCode x)) :
    M ≤ m := by
  classical
  have hKspark : K < spark A :=
    (Nat.le_min.mpr ⟨by omega, hKle⟩).trans_lt
      ((kSparseInjective_iff_min_lt_spark A).mp hinjective)
  have hexists (s : ι) : ∃ target : CardSubset (Fin m) K,
      columnSpan A (source s).val = columnSpan B target.val := by
    obtain ⟨target, hcontain⟩ := exists_alternative_span_of_one_open_source_patch
      A z f B alternativeCode (source s).val (hrich s) hfactors hsparse hexact
    have hdim : Module.finrank ℝ (columnSpan A (source s).val) = K := by
      rw [finrank_columnSpan_eq_card A (source s).val
        (linearIndependent_of_card_lt_spark A (source s).val
          (by simpa [(source s).property] using hKspark)), (source s).property]
    have htarget_dim := finrank_columnSpan_le_card B target.val
    have hdim_le := Submodule.finrank_mono hcontain
    have hcard : target.val.card = K := by
      rw [hdim] at hdim_le
      have hle := target.property
      omega
    refine ⟨⟨target.val, hcard⟩, Submodule.eq_of_le_of_finrank_le hcontain ?_⟩
    simpa [hdim, hcard] using htarget_dim
  choose target hspan using hexists
  exact source_width_le_of_covering_support_spans A B source target
    hKpos hinjective hcover hspan

/-- At arbitrary learned width, two-sided sparse injectivity and separating
observed support spaces identify all source columns. Consistent lifts in
both directions identify an active learned column in each source atom line. -/
theorem columns_embed_of_separating_support_spans_and_injective_alternative
    {ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (source : ι → CardSubset (Fin M) K) (target : ι → CardSubset (Fin m) K)
    (hKpos : 0 < K) (hA : KSparseInjective A K) (hB : KSparseInjective B K)
    (hcover : ∀ i, ∃ s, i ∈ (source s).val)
    (hseparate : ∀ i k, k ≠ i →
      ∃ s, i ∈ (source s).val ∧ k ∉ (source s).val)
    (hspan : ∀ s, columnSpan A (source s).val = columnSpan B (target s).val) :
    ∃ matching : Fin M ↪ Fin m, ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧ ∀ i, B.col (matching i) = scale i • A.col i := by
  classical
  obtain ⟨sourceCode, hsourceCode, _⟩ :=
    exists_consistent_source_column_lifts A B source target hA hspan
  obtain ⟨learnedCode, hlearnedCode, _⟩ :=
    exists_consistent_source_column_lifts B A target source hB (fun s => (hspan s).symm)
  have hpresent (i : Fin M) : ∃ j : Fin m, ∃ scale : ℝ,
      scale ≠ 0 ∧ B.col j = scale • A.col i := by
    obtain ⟨s, hi⟩ := hcover i
    have hatom : A.col i ≠ 0 := by
      intro hzero
      have hcodes := hA (Pi.single i 1) 0
        ((nonzeroSupport_single_card_le_one i 1).trans hKpos)
        (by simp [nonzeroSupport])
        (by rw [mulVec_single_real, one_smul, hzero]; simp)
      have h := congrFun hcodes i
      simp at h
    obtain ⟨j, hj, hcolumn⟩ := exists_active_nonzero_column_of_mulVec_ne_zero B
      (learnedCode i) (by rw [(hlearnedCode i s hi).2]; exact hatom)
    have htarget (t : ι) (hit : i ∈ (source t).val) : j ∈ (target t).val :=
      (hlearnedCode i t hit).1 ((mem_nonzeroSupport_iff _ _).mpr hj)
    have hsingle : sourceCode j = Pi.single i (sourceCode j i) := by
      ext k
      by_cases hki : k = i
      · subst k
        simp
      · have hz : sourceCode j k = 0 := by
          obtain ⟨t, hit, hkt⟩ := hseparate i k hki
          by_contra hnot
          exact hkt ((hsourceCode j t (htarget t hit)).1
            ((mem_nonzeroSupport_iff _ _).mpr hnot))
        simp [hki, hz]
    have heq : B.col j = sourceCode j i • A.col i := by
      rw [← (hsourceCode j s (htarget s hi)).2, hsingle, mulVec_single_real]
      simp
    refine ⟨j, sourceCode j i, ?_, heq⟩
    intro hz
    exact hcolumn (by rw [heq, hz, zero_smul])
  choose matching scale hscale hcolumns using hpresent
  have hmatching : Function.Injective matching := by
    intro i k hik
    by_contra hne
    have himages : A.mulVec (Pi.single i (scale i)) =
        A.mulVec (Pi.single k (scale k)) := by
      rw [mulVec_single_real, mulVec_single_real, ← hcolumns i, ← hcolumns k, hik]
    have hcodes := hA _ _
      ((nonzeroSupport_single_card_le_one i (scale i)).trans hKpos)
      ((nonzeroSupport_single_card_le_one k (scale k)).trans hKpos) himages
    have hz := congrFun hcodes i
    have hzero : scale i = 0 := by simpa [Pi.single_apply, hne, Ne.symm hne] using hz
    exact hscale i hzero
  exact ⟨⟨matching, hmatching⟩, scale, hscale, hcolumns⟩

/-- Source-richness on a covering and separating support family suffices for
arbitrary-width exact rigidity when the learned sparse codes are unique.
Support probabilities and support-family regularity play no role. -/
theorem source_columns_embed_of_openRich_separating_patterns
    {X ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : X → RepresentationVector d)
    (B : Matrix (Fin d) (Fin m) ℝ) (alternativeCode : X → FeatureVector m)
    (source : ι → CardSubset (Fin M) K)
    (hKpos : 0 < K) (hKle : K ≤ M)
    (hA : KSparseInjective A K) (hB : KSparseInjective B K)
    (hcover : ∀ i, ∃ s, i ∈ (source s).val)
    (hseparate : ∀ i k, k ≠ i →
      ∃ s, i ∈ (source s).val ∧ k ∉ (source s).val)
    (hrich : ∀ s, ∃ region : Set (coordinateSpan (source s).val),
      IsOpen region ∧ region.Nonempty ∧
        ∀ v ∈ region, (v : FeatureVector M) ∈ closure (Set.range z))
    (hfactors : ∀ x, f x = A.mulVec (z x))
    (hsparse : KSparse (K := K) alternativeCode)
    (hexact : ∀ x, f x = B.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin m, ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧ ∀ i, B.col (matching i) = scale i • A.col i := by
  classical
  have hKspark : K < spark A :=
    (Nat.le_min.mpr ⟨by omega, hKle⟩).trans_lt
      ((kSparseInjective_iff_min_lt_spark A).mp hA)
  have hexists (s : ι) : ∃ target : CardSubset (Fin m) K,
      columnSpan A (source s).val = columnSpan B target.val := by
    obtain ⟨target, hcontain⟩ := exists_alternative_span_of_one_open_source_patch
      A z f B alternativeCode (source s).val (hrich s) hfactors hsparse hexact
    have hdim : Module.finrank ℝ (columnSpan A (source s).val) = K := by
      rw [finrank_columnSpan_eq_card A (source s).val
        (linearIndependent_of_card_lt_spark A (source s).val
          (by simpa [(source s).property] using hKspark)), (source s).property]
    have htarget_dim := finrank_columnSpan_le_card B target.val
    have hdim_le := Submodule.finrank_mono hcontain
    have hcard : target.val.card = K := by
      rw [hdim] at hdim_le
      have hle := target.property
      omega
    refine ⟨⟨target.val, hcard⟩, Submodule.eq_of_le_of_finrank_le hcontain ?_⟩
    simpa [hdim, hcard] using htarget_dim
  choose target hspan using hexists
  exact columns_embed_of_separating_support_spans_and_injective_alternative
    A B source target hKpos hA hB hcover hseparate hspan

/-- The support-pattern extension identifies both dictionaries and codes at
arbitrary learned width. Every surplus learned coordinate is unused, as
encoded by the support of `embedSourceCode`. -/
theorem dictionary_and_codes_embed_of_openRich_separating_patterns
    {X ι : Type*} {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (f : X → RepresentationVector d)
    (B : Matrix (Fin d) (Fin m) ℝ) (alternativeCode : X → FeatureVector m)
    (source : ι → CardSubset (Fin M) K)
    (hKpos : 0 < K) (hKle : K ≤ M)
    (hA : KSparseInjective A K) (hB : KSparseInjective B K)
    (hcover : ∀ i, ∃ s, i ∈ (source s).val)
    (hseparate : ∀ i k, k ≠ i →
      ∃ s, i ∈ (source s).val ∧ k ∉ (source s).val)
    (hrich : ∀ s, ∃ region : Set (coordinateSpan (source s).val),
      IsOpen region ∧ region.Nonempty ∧
        ∀ v ∈ region, (v : FeatureVector M) ∈ closure (Set.range z))
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = A.mulVec (z x))
    (hsparse : KSparse (K := K) alternativeCode)
    (hexact : ∀ x, f x = B.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin m, ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      (∀ i, A.col i = scale i • B.col (matching i)) ∧
      ∀ x, alternativeCode x = embedSourceCode matching scale (z x) := by
  obtain ⟨matching, scale, hscale, hcolumns⟩ :=
    source_columns_embed_of_openRich_separating_patterns A z f B alternativeCode
      source hKpos hKle hA hB hcover hseparate hrich hfactors hsparse hexact
  have hreverse (i : Fin M) : A.col i = (scale i)⁻¹ • B.col (matching i) := by
    rw [hcolumns i, smul_smul, inv_mul_cancel₀ (hscale i), one_smul]
  exact ⟨matching, fun i => (scale i)⁻¹, fun i => inv_ne_zero (hscale i), hreverse,
    alternative_code_eq_embedded_source_code A z f B alternativeCode matching
      (fun i => (scale i)⁻¹) hreverse hB hsourceSparse hfactors hsparse hexact⟩

end PKG26AtomicFeatures
