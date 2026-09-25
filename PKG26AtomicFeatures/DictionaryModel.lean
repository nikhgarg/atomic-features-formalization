import Mathlib

/-!
# Sparse dictionary model for the atomic-features draft

This module defines sparse codes, dictionary factorizations, spark, and
coordinate spans. `KRich` means density in entire coordinate subspaces;
`OpenRichness.lean` defines the weaker relatively open richness used in the
paper's rigidity results.
-/

namespace PKG26AtomicFeatures

/-- A feature-coordinate vector with `M` dictionary atoms. -/
abbrev FeatureVector (M : ℕ) := Fin M → ℝ

/-- A representation vector in ambient dimension `d`. -/
abbrev RepresentationVector (d : ℕ) := Fin d → ℝ

/-- The finite support of nonzero coordinates of a feature vector. This is the
literal finite-dimensional interpretation of the source notation `‖v‖₀`. -/
noncomputable def nonzeroSupport {M : ℕ} (v : FeatureVector M) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun coordinate => v coordinate ≠ 0

@[simp] theorem mem_nonzeroSupport_iff {M : ℕ} (v : FeatureVector M)
    (coordinate : Fin M) : coordinate ∈ nonzeroSupport v ↔ v coordinate ≠ 0 := by
  classical
  simp [nonzeroSupport]

/-- The alternative coordinates used by at least one code vector.  The
coordinate type is finite even when the input domain is not. -/
noncomputable def usedCodeCoordinates {X : Type*} {M : ℕ}
    (code : X → FeatureVector M) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun coordinate => ∃ x, code x coordinate ≠ 0

@[simp] theorem mem_usedCodeCoordinates_iff
    {X : Type*} {M : ℕ} (code : X → FeatureVector M)
    (coordinate : Fin M) :
    coordinate ∈ usedCodeCoordinates code ↔
      ∃ x, code x coordinate ≠ 0 := by
  classical
  simp [usedCodeCoordinates]

/-- Every individual code support lies in the globally used coordinate set. -/
theorem nonzeroSupport_subset_usedCodeCoordinates
    {X : Type*} {M : ℕ} (code : X → FeatureVector M) (x : X) :
    nonzeroSupport (code x) ⊆ usedCodeCoordinates code := by
  intro coordinate hcoordinate
  rw [mem_usedCodeCoordinates_iff]
  exact ⟨x, (mem_nonzeroSupport_iff (code x) coordinate).1 hcoordinate⟩

/-- A code is `K`-sparse exactly when every code vector has at most `K`
nonzero coordinates. -/
def KSparse {X : Type*} {M K : ℕ} (z : X → FeatureVector M) : Prop :=
  ∀ x, (nonzeroSupport (z x)).card ≤ K

/-- An `(M,K)`-dictionary from the draft: a matrix together with a `K`-sparse
feature code. The ambient representation dimension is `d`. -/
structure Dictionary (X : Type*) (d M K : ℕ) where
  matrix : Matrix (Fin d) (Fin M) ℝ
  code : X → FeatureVector M
  sparse : KSparse (K := K) code

/-- A dictionary factors a representation when its matrix times its code equals
the representation at every input, exactly as in the source definition. -/
def Factors {X : Type*} {d M K : ℕ}
    (dictionary : Dictionary X d M K) (f : X → RepresentationVector d) : Prop :=
  ∀ x, f x = dictionary.matrix.mulVec (dictionary.code x)

/-- The matrix component of the source phrase "equal up to permutation and
scaling": every column of the right matrix is a nonzero rescaling of a
permuted column of the left matrix. Matrix non-equivalence is enough to refute
dictionary equivalence under any standard code-compatible version of that
phrase. -/
def ColumnsEquivalentUpToPermutationAndScaling {d M : ℕ}
    (left right : Matrix (Fin d) (Fin M) ℝ) : Prop :=
  ∃ permutation : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
    (∀ column, scale column ≠ 0) ∧
      ∀ column, right.col column = scale column • left.col (permutation column)

/-- One common permutation and nonzero coordinate scaling align two complete
dictionary factorizations.  The coefficient law is written pointwise in the
paper's matrix and code primitives: when an alternative column is `scale`
times its matched source column, the matched source coefficient is `scale`
times the alternative coefficient. -/
def DictionaryPairsEquivalentUpToPermutationAndScaling
    {X : Type*} {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (code : X → FeatureVector M)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M) : Prop :=
  ∃ permutation : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
    (∀ i, scale i ≠ 0) ∧
    (∀ i, alternative.col i = scale i • matrix.col (permutation i)) ∧
    ∀ x i, code x (permutation i) = scale i * alternativeCode x i

/-- Pair-level permutation-and-scaling equivalence is reflexive. -/
theorem dictionaryPairsEquivalent_refl
    {X : Type*} {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (code : X → FeatureVector M) :
    DictionaryPairsEquivalentUpToPermutationAndScaling matrix code
      matrix code := by
  refine ⟨Equiv.refl _, fun _ => 1, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

/-- Pair-level permutation-and-scaling equivalence is symmetric. -/
theorem dictionaryPairsEquivalent_symm
    {X : Type*} {d M : ℕ}
    {matrix alternative : Matrix (Fin d) (Fin M) ℝ}
    {code alternativeCode : X → FeatureVector M}
    (hequivalent : DictionaryPairsEquivalentUpToPermutationAndScaling
      matrix code alternative alternativeCode) :
    DictionaryPairsEquivalentUpToPermutationAndScaling
      alternative alternativeCode matrix code := by
  obtain ⟨permutation, scale, hscale, hcolumns, hcodes⟩ := hequivalent
  refine ⟨permutation.symm, fun i => (scale (permutation.symm i))⁻¹,
    ?_, ?_, ?_⟩
  · intro i
    exact inv_ne_zero (hscale (permutation.symm i))
  · intro i
    have hcolumn := hcolumns (permutation.symm i)
    simp only [Equiv.apply_symm_apply] at hcolumn
    rw [hcolumn, inv_smul_smul₀ (hscale (permutation.symm i))]
  · intro x i
    have hcode := hcodes x (permutation.symm i)
    simp only [Equiv.apply_symm_apply] at hcode
    rw [hcode, inv_mul_cancel_left₀ (hscale (permutation.symm i))]

/-- Pair-level permutation-and-scaling equivalence is transitive. -/
theorem dictionaryPairsEquivalent_trans
    {X : Type*} {d M : ℕ}
    {first second third : Matrix (Fin d) (Fin M) ℝ}
    {firstCode secondCode thirdCode : X → FeatureVector M}
    (hfirst : DictionaryPairsEquivalentUpToPermutationAndScaling
      first firstCode second secondCode)
    (hsecond : DictionaryPairsEquivalentUpToPermutationAndScaling
      second secondCode third thirdCode) :
    DictionaryPairsEquivalentUpToPermutationAndScaling
      first firstCode third thirdCode := by
  obtain ⟨firstPermutation, firstScale, hfirstScale, hfirstColumns,
    hfirstCodes⟩ := hfirst
  obtain ⟨secondPermutation, secondScale, hsecondScale, hsecondColumns,
    hsecondCodes⟩ := hsecond
  refine ⟨secondPermutation.trans firstPermutation,
    fun i => secondScale i * firstScale (secondPermutation i), ?_, ?_, ?_⟩
  · intro i
    exact mul_ne_zero (hsecondScale i) (hfirstScale (secondPermutation i))
  · intro i
    rw [hsecondColumns i, hfirstColumns (secondPermutation i)]
    simp only [Equiv.trans_apply, mul_smul]
  · intro x i
    rw [Equiv.trans_apply, hfirstCodes x (secondPermutation i),
      hsecondCodes x i]
    ring

/-- The column family selected by a finite set of dictionary coordinates. -/
def selectedColumns {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (coordinates : Finset (Fin M)) : {i // i ∈ coordinates} → RepresentationVector d :=
  fun coordinate row => matrix row coordinate.1

/-- The subspace spanned by a selected finite family of dictionary columns. -/
noncomputable def columnSpan {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (coordinates : Finset (Fin M)) : Submodule ℝ (RepresentationVector d) :=
  Submodule.span ℝ (Set.range (selectedColumns matrix coordinates))

/-- Enlarging a selected column set can only enlarge its span. -/
theorem columnSpan_mono {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    {coordinates smaller : Finset (Fin M)} (hsubset : coordinates ⊆ smaller) :
    columnSpan matrix coordinates ≤ columnSpan matrix smaller := by
  apply Submodule.span_mono
  rintro column ⟨coordinate, rfl⟩
  exact ⟨⟨coordinate.1, hsubset coordinate.2⟩, rfl⟩

/-- A selected column span has dimension at most the number of selected
columns. -/
theorem finrank_columnSpan_le_card {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (coordinates : Finset (Fin M)) :
    Module.finrank ℝ (columnSpan matrix coordinates) ≤ coordinates.card := by
  rw [columnSpan]
  simpa only [Set.finrank, Fintype.card_coe] using
    (finrank_range_le_card (R := ℝ) (selectedColumns matrix coordinates))

/-- The finite selections of linearly dependent columns of a matrix. -/
noncomputable def dependentColumnSets {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ) :
    Finset (Finset (Fin M)) := by
  classical
  exact Finset.univ.powerset.filter fun coordinates =>
    ¬ LinearIndependent ℝ (selectedColumns matrix coordinates)

@[simp] theorem mem_dependentColumnSets_iff {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (coordinates : Finset (Fin M)) :
    coordinates ∈ dependentColumnSets matrix ↔
      ¬ LinearIndependent ℝ (selectedColumns matrix coordinates) := by
  classical
  simp [dependentColumnSets]

/-- The standard finite-matrix spark: the least number of linearly dependent
columns, with value `M+1` when every column set is independent. This supplies
the definition omitted by the source's nearby TODO. -/
noncomputable def spark {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ) : ℕ := by
  classical
  let dependentCards := (dependentColumnSets matrix).image Finset.card
  exact if h : dependentCards.Nonempty then dependentCards.min' h else M + 1

/-- A linearly dependent column selection has cardinality at least the spark. -/
theorem spark_le_card_of_dependent {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (coordinates : Finset (Fin M))
    (hdependent : ¬ LinearIndependent ℝ (selectedColumns matrix coordinates)) :
    spark matrix ≤ coordinates.card := by
  classical
  let dependentCards := (dependentColumnSets matrix).image Finset.card
  have hmembership : coordinates.card ∈ dependentCards := by
    exact Finset.mem_image.mpr ⟨coordinates, (mem_dependentColumnSets_iff matrix coordinates).mpr hdependent, rfl⟩
  have hnonempty : dependentCards.Nonempty := ⟨coordinates.card, hmembership⟩
  rw [spark]
  rw [dif_pos hnonempty]
  exact Finset.min'_le dependentCards coordinates.card hmembership

/-- The finite-matrix spark is positive: the empty column family is linearly
independent, while the all-independent fallback is `M + 1`. -/
theorem spark_pos {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ) :
    0 < spark matrix := by
  classical
  let dependentCards := (dependentColumnSets matrix).image Finset.card
  rw [spark]
  split_ifs with hnonempty
  · have hmin_mem : dependentCards.min' hnonempty ∈ dependentCards :=
      Finset.min'_mem dependentCards hnonempty
    obtain ⟨coordinates, hdependent, hmin_card⟩ :=
      Finset.mem_image.mp hmin_mem
    rw [← hmin_card]
    apply Finset.card_pos.mpr
    by_contra hcoordinates
    have hcoordinates_empty : coordinates = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcoordinates
    subst coordinates
    rw [mem_dependentColumnSets_iff] at hdependent
    exact hdependent linearIndependent_empty_type
  · omega

/-- The finite-matrix spark is never larger than one plus the number of
columns. -/
theorem spark_le_column_count_succ {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ) :
    spark matrix ≤ M + 1 := by
  classical
  let dependentCards := (dependentColumnSets matrix).image Finset.card
  rw [spark]
  split_ifs with hnonempty
  · have hmin_mem : dependentCards.min' hnonempty ∈ dependentCards :=
      Finset.min'_mem dependentCards hnonempty
    obtain ⟨coordinates, _, hmin_card⟩ := Finset.mem_image.mp hmin_mem
    rw [← hmin_card]
    exact Nat.le_succ_of_le (by simpa using Finset.card_le_univ coordinates)
  · exact Nat.le_refl _

/-- Under the source's general-position equality, the ambient dimension does
not exceed the number of dictionary columns. -/
theorem ambient_dimension_le_column_count_of_spark_eq {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (hspark : spark matrix = d + 1) :
    d ≤ M := by
  have hspark_bound := spark_le_column_count_succ matrix
  rw [hspark] at hspark_bound
  omega

/-- A matrix whose full column family is linearly independent has the maximal
finite spark value `M + 1`. -/
theorem spark_eq_column_count_succ_of_linearIndependent {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (hcolumns : LinearIndependent ℝ matrix.col) :
    spark matrix = M + 1 := by
  classical
  let dependentCards := (dependentColumnSets matrix).image Finset.card
  have hnone : ¬ dependentCards.Nonempty := by
    rintro ⟨cardinality, hcardinality⟩
    obtain ⟨coordinates, hdependent, _⟩ := Finset.mem_image.mp hcardinality
    rw [mem_dependentColumnSets_iff] at hdependent
    exact hdependent (by
      simpa [selectedColumns] using
        hcolumns.comp Subtype.val Subtype.val_injective)
  rw [spark]
  simp [dependentCards, hnone]

/-- The square identity dictionary has spark one larger than its ambient
dimension. -/
theorem spark_one (d : ℕ) :
    spark (1 : Matrix (Fin d) (Fin d) ℝ) = d + 1 := by
  apply spark_eq_column_count_succ_of_linearIndependent
  have hcolumns : (1 : Matrix (Fin d) (Fin d) ℝ).col =
      fun i => Pi.single i (1 : ℝ) := by
    funext i row
    simp [Matrix.one_apply, Pi.single_apply]
  rw [hcolumns]
  exact Pi.linearIndependent_single_one (Fin d) ℝ

/-- Every column selection smaller than the spark is linearly independent. -/
theorem linearIndependent_of_card_lt_spark {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (coordinates : Finset (Fin M))
    (hcard : coordinates.card < spark matrix) :
    LinearIndependent ℝ (selectedColumns matrix coordinates) := by
  by_contra hdependent
  have hspark := spark_le_card_of_dependent matrix coordinates hdependent
  omega

/-- Whenever the spark is at most the column count, some dependent column set
attains it exactly. The alternative value `M + 1` occurs precisely when no
dependent column set exists. -/
theorem exists_dependent_card_eq_spark
    {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (hspark : spark matrix ≤ M) :
    ∃ coordinates : Finset (Fin M),
      coordinates.card = spark matrix ∧
        ¬ LinearIndependent ℝ (selectedColumns matrix coordinates) := by
  classical
  let dependentCards := (dependentColumnSets matrix).image Finset.card
  have hnonempty : dependentCards.Nonempty := by
    by_contra hempty
    have hspark_eq : spark matrix = M + 1 := by
      rw [spark, dif_neg hempty]
    omega
  have hmin_mem : dependentCards.min' hnonempty ∈ dependentCards :=
    Finset.min'_mem dependentCards hnonempty
  obtain ⟨coordinates, hdependent, hcard⟩ :=
    Finset.mem_image.mp hmin_mem
  refine ⟨coordinates, ?_, ?_⟩
  · rw [spark, dif_pos hnonempty]
    exact hcard
  · exact (mem_dependentColumnSets_iff matrix coordinates).mp hdependent

/-- The coordinate subspace spanned by the canonical feature vectors indexed by
`coordinates`. This is the source's `span {e_i}_{i∈S}`. -/
noncomputable def coordinateSpan {M : ℕ} (coordinates : Finset (Fin M)) :
    Submodule ℝ (FeatureVector M) := by
  classical
  exact Submodule.span ℝ (Set.range fun coordinate : {i // i ∈ coordinates} =>
    Pi.single coordinate.1 (1 : ℝ))

/-- Every selected canonical coordinate vector lies in its coordinate span. -/
theorem canonicalVector_mem_coordinateSpan {M : ℕ} (coordinates : Finset (Fin M))
    {coordinate : Fin M} (hcoordinate : coordinate ∈ coordinates) :
    Pi.single coordinate (1 : ℝ) ∈ coordinateSpan coordinates := by
  apply Submodule.subset_span
  exact ⟨⟨coordinate, hcoordinate⟩, rfl⟩

/-- Membership in a coordinate span forces every coordinate outside the
selected set to vanish. -/
theorem eq_zero_of_mem_coordinateSpan_of_not_mem
    {M : ℕ} {coordinates : Finset (Fin M)} {v : FeatureVector M}
    (hv : v ∈ coordinateSpan coordinates) {coordinate : Fin M}
    (hcoordinate : coordinate ∉ coordinates) :
    v coordinate = 0 := by
  rw [coordinateSpan] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp [ne_of_mem_of_not_mem i.2 hcoordinate]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul scalar x _ hx => simp [hx]

/-- A vector in a coordinate span has no nonzero support outside that
coordinate set. -/
theorem nonzeroSupport_subset_of_mem_coordinateSpan
    {M : ℕ} {coordinates : Finset (Fin M)} {v : FeatureVector M}
    (hv : v ∈ coordinateSpan coordinates) :
    nonzeroSupport v ⊆ coordinates := by
  intro coordinate hnonzero
  by_contra hcoordinate
  have hzero := eq_zero_of_mem_coordinateSpan_of_not_mem hv hcoordinate
  exact (mem_nonzeroSupport_iff v coordinate).mp hnonzero hzero

/-- Conversely, a vector supported on a selected coordinate set belongs to
that coordinate span. -/
theorem mem_coordinateSpan_of_nonzeroSupport_subset
    {M : ℕ} {coordinates : Finset (Fin M)} {v : FeatureVector M}
    (hsupport : nonzeroSupport v ⊆ coordinates) :
    v ∈ coordinateSpan coordinates := by
  classical
  have hvzero : ∀ coordinate ∉ coordinates, v coordinate = 0 := by
    intro coordinate hcoordinate
    by_contra hnonzero
    exact hcoordinate
      (hsupport ((mem_nonzeroSupport_iff v coordinate).mpr hnonzero))
  have hvsum :
      v = ∑ coordinate ∈ coordinates,
        v coordinate • (Pi.single coordinate (1 : ℝ) : FeatureVector M) := by
    ext coordinate
    by_cases hcoordinate : coordinate ∈ coordinates
    · simp [Finset.sum_apply, Pi.single_apply, hcoordinate]
    · simp [Finset.sum_apply, Pi.single_apply, hcoordinate,
        hvzero coordinate hcoordinate]
  rw [hvsum]
  apply Submodule.sum_mem
  intro coordinate hcoordinate
  exact Submodule.smul_mem _ _
    (canonicalVector_mem_coordinateSpan coordinates hcoordinate)

theorem mem_coordinateSpan_iff_nonzeroSupport_subset
    {M : ℕ} {coordinates : Finset (Fin M)} {v : FeatureVector M} :
    v ∈ coordinateSpan coordinates ↔ nonzeroSupport v ⊆ coordinates :=
  ⟨nonzeroSupport_subset_of_mem_coordinateSpan,
    mem_coordinateSpan_of_nonzeroSupport_subset⟩

/-- Every matrix-vector product is in the span of precisely the columns at
which that vector is nonzero. -/
theorem mulVec_mem_columnSpan_nonzeroSupport {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (code : FeatureVector M) :
    matrix.mulVec code ∈ columnSpan matrix (nonzeroSupport code) := by
  classical
  rw [columnSpan, Matrix.mulVec_eq_sum]
  have hsum :
      (∑ coordinate : Fin M, MulOpposite.op (code coordinate) • matrix.transpose coordinate) =
        ∑ coordinate ∈ nonzeroSupport code,
          MulOpposite.op (code coordinate) • matrix.transpose coordinate := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro coordinate _ hnotmem
    have hzero : code coordinate = 0 := by
      by_contra hnonzero
      apply hnotmem
      simpa using hnonzero
    simp [hzero]
  rw [hsum]
  apply Submodule.sum_mem
  intro coordinate hcoordinate
  rw [op_smul_eq_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨coordinate, hcoordinate⟩, rfl⟩

/-- A code is `K`-rich when its image is dense in every `K`-coordinate
subspace. The inclusion into the closure is the ambient-space formulation of
the source phrase "dense in span{e_i}_{i∈S}". -/
def KRich {X : Type*} {M K : ℕ} (z : X → FeatureVector M) : Prop :=
  ∀ coordinates : Finset (Fin M), coordinates.card = K →
    (coordinateSpan coordinates : Set (FeatureVector M)) ⊆ closure (Set.range z)

/-- The empty coordinate family spans only the zero vector. -/
theorem coordinateSpan_empty (M : ℕ) :
    coordinateSpan (∅ : Finset (Fin M)) = ⊥ := by
  classical
  rw [coordinateSpan, Submodule.span_eq_bot]
  intro vector hvector
  obtain ⟨coordinate, rfl⟩ := hvector
  rcases coordinate with ⟨i, hi⟩
  simp at hi

/-- The zero code has sparsity level zero. This supplies the source-model
half of the printed theorem's `K = 0` endpoint check. -/
theorem zero_code_is_zero_sparse {X : Type*} (M : ℕ) :
    KSparse (K := 0) (fun _ : X => (0 : FeatureVector M)) := by
  intro x
  simp [nonzeroSupport]

/-- On a nonempty source domain, the zero code is also zero-rich: the only
coordinate subspace tested at `K = 0` is the zero subspace. -/
theorem zero_code_is_zero_rich {X : Type*} [Nonempty X] (M : ℕ) :
    KRich (K := 0) (fun _ : X => (0 : FeatureVector M)) := by
  intro coordinates hcoordinates v hv
  have hcoordinates_empty : coordinates = ∅ := Finset.card_eq_zero.mp hcoordinates
  subst coordinates
  have hv_zero : v = 0 := by
    rw [coordinateSpan_empty] at hv
    exact hv
  subst v
  let x : X := Classical.choice (inferInstance : Nonempty X)
  exact subset_closure ⟨x, rfl⟩

/-- Every matrix together with the zero code factors the zero representation
at sparsity level zero. -/
theorem zero_code_factors_zero {X : Type*} {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) :
    Factors
      { matrix := matrix
        code := fun _ : X => (0 : FeatureVector M)
        sparse := zero_code_is_zero_sparse M }
      (fun _ : X => (0 : RepresentationVector d)) := by
  intro x
  simp

/-- A concrete source-model witness for the `K = 0` endpoint: the zero code
is sparse, rich, and factors the zero representation through both a
general-position one-column dictionary and a distinct zero dictionary. -/
theorem zero_endpoint_factorization_witness :
    spark (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 + 1 ∧
    KRich (K := 0) (fun _ : PUnit => (0 : FeatureVector 1)) ∧
    Factors
      { matrix := (1 : Matrix (Fin 1) (Fin 1) ℝ)
        code := fun _ : PUnit => (0 : FeatureVector 1)
        sparse := zero_code_is_zero_sparse 1 }
      (fun _ : PUnit => (0 : RepresentationVector 1)) ∧
    Factors
      { matrix := (0 : Matrix (Fin 1) (Fin 1) ℝ)
        code := fun _ : PUnit => (0 : FeatureVector 1)
        sparse := zero_code_is_zero_sparse 1 }
      (fun _ : PUnit => (0 : RepresentationVector 1)) ∧
    (0 : Matrix (Fin 1) (Fin 1) ℝ) ≠ 1 := by
  refine ⟨by simpa using spark_one 1, zero_code_is_zero_rich 1,
    zero_code_factors_zero (1 : Matrix (Fin 1) (Fin 1) ℝ),
    zero_code_factors_zero (0 : Matrix (Fin 1) (Fin 1) ℝ), ?_⟩
  intro hzero_one
  have hentry := congrFun (congrFun hzero_one (0 : Fin 1)) (0 : Fin 1)
  norm_num at hentry

/-- The zero alternative matrix is not related to the one-dimensional identity
dictionary by a permutation and nonzero column scalings. -/
theorem zero_not_columnsEquivalentTo_one :
    ¬ ColumnsEquivalentUpToPermutationAndScaling
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rintro ⟨permutation, scale, hscale, hcolumns⟩
  have hentry := congrFun (hcolumns (0 : Fin 1)) (permutation (0 : Fin 1))
  have hscale_zero : scale (0 : Fin 1) = 0 := by
    simpa [Matrix.col_apply] using hentry.symm
  exact hscale (0 : Fin 1) hscale_zero

/-- Every representation in dimension `d` is `d`-sparse in the identity
coordinate system. -/
theorem representation_is_dimension_sparse {X : Type*} {d : ℕ}
    (f : X → RepresentationVector d) :
    KSparse (K := d) f := by
  intro x
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (by simpa using Finset.card_le_univ (nonzeroSupport (f x)))

/-- The `d`-column identity dictionary factors every representation using its
own coordinates. This is the alternative factorization in the dimensional
counterexample to the printed `2K` lower bound. -/
theorem identity_dictionary_factors {X : Type*} {d : ℕ}
    (f : X → RepresentationVector d) :
    Factors
      { matrix := (1 : Matrix (Fin d) (Fin d) ℝ)
        code := f
        sparse := representation_is_dimension_sparse f }
      f := by
  intro x
  simp

/-- The source richness condition transfers through a dictionary matrix: on
every source `K`-coordinate subspace, the linear image lies in the closure of
the observed representation range.  This is the topological half of the
appendix's intended `U_K(A)` coverage argument. -/
theorem image_coordinateSpan_subset_closure_range_of_kRich_and_factors
    {X : Type*} {d M K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (coordinates : Finset (Fin M)) (hcoordinates : coordinates.card = K) :
    matrix.mulVecLin '' (coordinateSpan coordinates : Set (FeatureVector M)) ⊆
      closure (Set.range f) := by
  intro y hy
  obtain ⟨v, hv, rfl⟩ := hy
  have hv_closure : v ∈ closure (Set.range z) :=
    hrich coordinates hcoordinates hv
  have hcontinuous : Continuous matrix.mulVecLin :=
    LinearMap.continuous_of_finiteDimensional _
  have himage_closure : matrix.mulVecLin v ∈
      closure (matrix.mulVecLin '' Set.range z) :=
    mem_closure_image hcontinuous.continuousAt hv_closure
  apply closure_mono ?_ himage_closure
  intro output houtput
  obtain ⟨code, ⟨x, rfl⟩, rfl⟩ := houtput
  exact ⟨x, hfactors x⟩

/-- A finite union of linear subspaces of the finite-dimensional representation
space is closed.  Thus a range contained in that union has its closure
contained in the same union. -/
theorem closure_range_subset_iUnion_of_finite_submodules
    {X ι : Type*} {d : ℕ} [Finite ι]
    (f : X → RepresentationVector d)
    (targets : ι → Submodule ℝ (RepresentationVector d))
    (hcover : Set.range f ⊆ ⋃ i, (targets i : Set (RepresentationVector d))) :
    closure (Set.range f) ⊆ ⋃ i, (targets i : Set (RepresentationVector d)) := by
  exact
    (isClosed_iUnion_of_finite fun i =>
      (targets i).closed_of_finiteDimensional).closure_subset_iff.mpr hcover

/-- A sparse factorization covers its observed range by the finite family of
column spans indexed by supports of size at most its sparsity level. -/
theorem range_subset_iUnion_sparse_columnSpan_of_factors
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (code : X → FeatureVector M) (f : X → RepresentationVector d)
    (hsparse : KSparse (K := K) code)
    (hfactors : ∀ x, f x = matrix.mulVec (code x)) :
    Set.range f ⊆ ⋃ support : {coordinates : Finset (Fin M) // coordinates.card ≤ K},
      (columnSpan matrix support.1 : Set (RepresentationVector d)) := by
  intro output houtput
  obtain ⟨x, rfl⟩ := houtput
  rw [hfactors x]
  refine Set.mem_iUnion.mpr ?_
  exact ⟨⟨nonzeroSupport (code x), hsparse x⟩,
    mulVec_mem_columnSpan_nonzeroSupport matrix (code x)⟩

/-- The density/factorization half of the appendix's intended subspace-cover
argument.  Once every observed representation lies in a finite union of
alternative subspaces, each source `K`-coordinate image lies in that same
union. -/
theorem image_coordinateSpan_subset_iUnion_of_finite_submodules_of_kRich_and_factors
    {X ι : Type*} {d M K : ℕ} [Finite ι]
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (targets : ι → Submodule ℝ (RepresentationVector d))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (hcover : Set.range f ⊆ ⋃ i, (targets i : Set (RepresentationVector d)))
    (coordinates : Finset (Fin M)) (hcoordinates : coordinates.card = K) :
    matrix.mulVecLin '' (coordinateSpan coordinates : Set (FeatureVector M)) ⊆
      ⋃ i, (targets i : Set (RepresentationVector d)) := by
  exact
    (image_coordinateSpan_subset_closure_range_of_kRich_and_factors matrix z f
      hrich hfactors coordinates hcoordinates).trans
      (closure_range_subset_iUnion_of_finite_submodules f targets hcover)

/-- The source assumptions actually yield the appendix's finite
alternative-subspace cover: every `K`-coordinate source image lies in the
union of alternative column spans with support size at most `K'`. -/
theorem image_coordinateSpan_subset_iUnion_sparse_columnSpan_of_kRich_and_factorizations
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
    matrix.mulVecLin '' (coordinateSpan coordinates : Set (FeatureVector M)) ⊆
      ⋃ support : {coordinates : Finset (Fin M') // coordinates.card ≤ K'},
        (columnSpan alternativeMatrix support.1 : Set (RepresentationVector d)) := by
  apply
    image_coordinateSpan_subset_iUnion_of_finite_submodules_of_kRich_and_factors
      matrix z f
      (fun support : {coordinates : Finset (Fin M') // coordinates.card ≤ K'} =>
        columnSpan alternativeMatrix support.1)
      hrich hfactors ?_ coordinates hcoordinates
  exact
    range_subset_iUnion_sparse_columnSpan_of_factors alternativeMatrix alternativeCode f
      halternativeSparse halternativeFactors

end PKG26AtomicFeatures
