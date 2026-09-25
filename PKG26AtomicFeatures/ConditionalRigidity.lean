import PKG26AtomicFeatures.GenericDimension
import PKG26AtomicFeatures.EqualSizeIdentifiability

/-!
# Strict-width rigidity or sparse-code nonidentifiability

This module proves a width-or-nonidentifiability dichotomy for sparse
factorizations. Every narrower alternative either reaches the spark-adaptive
effective-sparsity cutoff

`min (2*K) (spark A - 1) ≤ min K' M'`

or gives some true source atom two distinct sparse coefficient vectors. Hence
it fails unique sparse decoding on the closure of represented outputs; when a
nonzero point on every pure atomic ray is observed, the failure occurs on the
actual output range. For a full-spark source with `2*K ≤ d`, the numerical
branch is the advertised `2*K ≤ min K' M'`.

The module also proves the implication hierarchy used internally: global
sparse injectivity, data-relative unique decoding, atomwise unique codes, least
atom supports, compatible Hall witnesses, and the numerical cutoff. These implications separate the numerical obstruction from the uniqueness
of sparse codes.
-/

namespace PKG26AtomicFeatures

open AppendixHall

/-- At a fixed width, every source atom has at most one sparse coefficient
vector over the alternative dictionary.  This is a structural condition on
the two dictionary matrices themselves: the relevant fibers are

`{u | card (support u) ≤ width ∧ alternative.mulVec u = matrix.col i}`.

Existence of a member of each fiber follows separately from positive source
richness and the two factorizations. -/
def SourceAtomCodesUniqueAtWidth {d M M' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ) (width : ℕ) : Prop :=
  ∀ i : Fin M, ∀ left right : FeatureVector M',
    (nonzeroSupport left).card ≤ width →
    (nonzeroSupport right).card ≤ width →
    alternative.mulVec left = matrix.col i →
    alternative.mulVec right = matrix.col i →
    left = right

/-- A dictionary is uniquely sparsely decodable on a set of represented
outputs when every output in that set has at most one coefficient vector at
the stated width.  This is the data-relative identifiability property whose
failure is an interpretable adverse branch of the strict-width theorem. -/
def UniquelySparseDecodableOn {d M' : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (outputs : Set (RepresentationVector d)) (width : ℕ) : Prop :=
  ∀ output ∈ outputs, ∀ left right : FeatureVector M',
    (nonzeroSupport left).card ≤ width →
    (nonzeroSupport right).card ≤ width →
    alternative.mulVec left = output →
    alternative.mulVec right = output →
    left = right

/-- Every pure source atom occurs at an actual input rather than only as a
limit point supplied by richness. -/
def SourceAtomsRealized {X : Type*} {M : ℕ}
    (z : X → FeatureVector M) : Prop :=
  ∀ i : Fin M, ∃ x : X, z x = Pi.single i (1 : ℝ)

/-- A nonzero point on every atomic ray, rather than necessarily its normalized
basis vector, is observed by the source code.  This is the weaker primitive
needed to transfer an atomwise code collision from the closure onto the actual
output range. -/
def SourceAtomRaysRealized {X : Type*} {M : ℕ}
    (z : X → FeatureVector M) : Prop :=
  ∀ i : Fin M, ∃ x : X, ∃ coefficient : ℝ,
    coefficient ≠ 0 ∧
      z x = coefficient • (Pi.single i (1 : ℝ) : FeatureVector M)

/-- Exact realization of every normalized source atom supplies a nonzero point
on every atomic ray. -/
theorem sourceAtomRaysRealized_of_sourceAtomsRealized
    {X : Type*} {M : ℕ} {z : X → FeatureVector M}
    (hatoms : SourceAtomsRealized z) : SourceAtomRaysRealized z := by
  intro i
  obtain ⟨x, hx⟩ := hatoms i
  exact ⟨x, 1, one_ne_zero, by simpa using hx⟩

/-- Global sparse-code injectivity implies unique sparse decodability on every
chosen output set. -/
theorem uniquelySparseDecodableOn_of_kSparseInjective
    {d M' width : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (outputs : Set (RepresentationVector d))
    (hinjective : KSparseInjective alternative width) :
    UniquelySparseDecodableOn alternative outputs width := by
  intro output _houtput left right hleft hright hleft_factor hright_factor
  apply hinjective left right hleft hright
  rw [hleft_factor, hright_factor]

/-- Positive source richness puts every source atom in the closure of the
represented data. -/
theorem sourceColumn_mem_closure_range_of_kRich_and_factors
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (i : Fin M) : matrix.col i ∈ closure (Set.range f) := by
  classical
  have hsingleton_card : ({i} : Finset (Fin M)).card ≤ K := by
    simp
    omega
  obtain ⟨coordinates, hsingleton_subset, _hcoordinates_univ,
      hcoordinates_card⟩ :=
    Finset.exists_subsuperset_card_eq
      (Finset.subset_univ ({i} : Finset (Fin M))) hsingleton_card
        (by simpa using hK_le_M)
  apply image_coordinateSpan_subset_closure_range_of_kRich_and_factors
    matrix z f hrich hfactors coordinates hcoordinates_card
  refine ⟨Pi.single i (1 : ℝ),
    canonicalVector_mem_coordinateSpan coordinates
      (hsingleton_subset (Finset.mem_singleton_self i)), ?_⟩
  ext row
  simp

/-- Unique sparse decodability on the closure of the represented data implies
atomwise uniqueness, because positive richness places every source atom in
that closure. -/
theorem sourceAtomCodesUniqueAtWidth_of_uniquelySparseDecodableOn_closure
    {X : Type*} {d M M' K width : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (hdecodable : UniquelySparseDecodableOn alternative
      (closure (Set.range f)) width) :
    SourceAtomCodesUniqueAtWidth matrix alternative width := by
  intro i left right hleft hright hleft_factor hright_factor
  apply hdecodable (matrix.col i)
    (sourceColumn_mem_closure_range_of_kRich_and_factors
      matrix z f hKpos hK_le_M hrich hfactors i)
    left right hleft hright hleft_factor hright_factor

/-- If every pure source atom is actually realized, unique sparse decodability
on the observed output range already implies atomwise uniqueness. -/
theorem sourceAtomCodesUniqueAtWidth_of_uniquelySparseDecodableOn_range
    {X : Type*} {d M M' width : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (hatomsRealized : SourceAtomsRealized z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (hdecodable : UniquelySparseDecodableOn alternative
      (Set.range f) width) :
    SourceAtomCodesUniqueAtWidth matrix alternative width := by
  intro i left right hleft hright hleft_factor hright_factor
  obtain ⟨x, hx⟩ := hatomsRealized i
  have houtput : f x = matrix.col i := by
    rw [hfactors x, hx]
    ext row
    simp
  apply hdecodable (f x) ⟨x, rfl⟩ left right hleft hright
  · exact hleft_factor.trans houtput.symm
  · exact hright_factor.trans houtput.symm

/-- Realizing any nonzero point on each atomic ray is enough for unique sparse
decodability on the observed range to imply uniqueness at the normalized source
atoms.  Scaling preserves supports and can be cancelled because the realized
coefficient is nonzero. -/
theorem sourceAtomCodesUniqueAtWidth_of_uniquelySparseDecodableOn_range_of_rays
    {X : Type*} {d M M' width : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (hraysRealized : SourceAtomRaysRealized z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (hdecodable : UniquelySparseDecodableOn alternative
      (Set.range f) width) :
    SourceAtomCodesUniqueAtWidth matrix alternative width := by
  classical
  intro i left right hleft hright hleft_factor hright_factor
  obtain ⟨x, coefficient, hcoefficient, hx⟩ := hraysRealized i
  have houtput : f x = coefficient • matrix.col i := by
    rw [hfactors x, hx, Matrix.mulVec_smul]
    congr 1
    ext row
    simp
  have hsupport_smul (code : FeatureVector M') :
      nonzeroSupport (coefficient • code) = nonzeroSupport code := by
    ext coordinate
    simp [mem_nonzeroSupport_iff, hcoefficient]
  have hleft_scaled :
      (nonzeroSupport (coefficient • left)).card ≤ width := by
    simpa [hsupport_smul left] using hleft
  have hright_scaled :
      (nonzeroSupport (coefficient • right)).card ≤ width := by
    simpa [hsupport_smul right] using hright
  have hleft_factor_scaled :
      alternative.mulVec (coefficient • left) = f x := by
    rw [Matrix.mulVec_smul, hleft_factor, ← houtput]
  have hright_factor_scaled :
      alternative.mulVec (coefficient • right) = f x := by
    rw [Matrix.mulVec_smul, hright_factor, ← houtput]
  have hscaled := hdecodable (f x) ⟨x, rfl⟩
    (coefficient • left) (coefficient • right)
    hleft_scaled hright_scaled hleft_factor_scaled hright_factor_scaled
  exact smul_right_injective (FeatureVector M') hcoefficient hscaled

/-- Global sparse-code injectivity of the alternative dictionary is stronger
than atomwise uniqueness relative to a particular source dictionary. -/
theorem sourceAtomCodesUniqueAtWidth_of_kSparseInjective
    {d M M' width : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (hinjective : KSparseInjective alternative width) :
    SourceAtomCodesUniqueAtWidth matrix alternative width := by
  intro i left right hleft hright hleft_factor hright_factor
  apply hinjective left right hleft hright
  rw [hleft_factor, hright_factor]

/-- An atom has a least alternative support at a fixed width when it lies in
the span of one support of that width and this support is contained in every
other support of the same width that spans the atom.  This is the exact
choice-independent "support core" condition needed by the appendix.  It does
not require uniqueness of coefficients inside the core. -/
def HasLeastSupportAtWidth {d M' : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (atom : RepresentationVector d) (width : ℕ) : Prop :=
  ∃ core : Finset (Fin M'),
    core.card ≤ width ∧
      atom ∈ columnSpan alternative core ∧
      ∀ target : Finset (Fin M'), target.card ≤ width →
        atom ∈ columnSpan alternative target → core ⊆ target

/-- Primitive coefficient-fiber formulation of a least atom support.  There is
one sparse code for the atom whose nonzero coordinates occur in every other
sparse code for that same atom. -/
def HasLeastCodeSupportAtWidth {d M' : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (atom : RepresentationVector d) (width : ℕ) : Prop :=
  ∃ code : FeatureVector M',
    (nonzeroSupport code).card ≤ width ∧
      alternative.mulVec code = atom ∧
      ∀ other : FeatureVector M',
        (nonzeroSupport other).card ≤ width →
        alternative.mulVec other = atom →
        nonzeroSupport code ⊆ nonzeroSupport other

/-- The coefficient-fiber statement is equivalent to the support-core
statement used internally by the Hall argument. -/
theorem hasLeastCodeSupportAtWidth_iff_hasLeastSupportAtWidth
    {d M' width : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (atom : RepresentationVector d) :
    HasLeastCodeSupportAtWidth alternative atom width ↔
      HasLeastSupportAtWidth alternative atom width := by
  classical
  constructor
  · rintro ⟨code, hcode_card, hcode_factor, hcode_least⟩
    refine ⟨nonzeroSupport code, hcode_card, ?_, ?_⟩
    · rw [← hcode_factor]
      exact mulVec_mem_columnSpan_nonzeroSupport alternative code
    · intro target htarget_card hatom
      rw [← map_mulVecLin_coordinateSpan_eq_columnSpan] at hatom
      obtain ⟨targetCode, htargetCode_mem, htargetCode_eq⟩ := hatom
      have htargetCode_support : nonzeroSupport targetCode ⊆ target :=
        nonzeroSupport_subset_of_mem_coordinateSpan htargetCode_mem
      have htargetCode_card : (nonzeroSupport targetCode).card ≤ width :=
        (Finset.card_le_card htargetCode_support).trans htarget_card
      exact (hcode_least targetCode htargetCode_card
        (by simpa using htargetCode_eq)).trans htargetCode_support
  · rintro ⟨core, hcore_card, hcore_span, hcore_least⟩
    rw [← map_mulVecLin_coordinateSpan_eq_columnSpan] at hcore_span
    obtain ⟨code, hcode_mem, hcode_factor⟩ := hcore_span
    have hcode_support : nonzeroSupport code ⊆ core :=
      nonzeroSupport_subset_of_mem_coordinateSpan hcode_mem
    have hcode_card : (nonzeroSupport code).card ≤ width :=
      (Finset.card_le_card hcode_support).trans hcore_card
    refine ⟨code, hcode_card, (by simpa using hcode_factor), ?_⟩
    intro other hother_card hother_factor
    have hother_span : atom ∈
        columnSpan alternative (nonzeroSupport other) := by
      rw [← hother_factor]
      exact mulVec_mem_columnSpan_nonzeroSupport alternative other
    exact hcode_support.trans
      (hcore_least (nonzeroSupport other) hother_card hother_span)

/-- Every source atom has a least sparse-code support over the alternative
dictionary.  This aggregate premise refers only to the source and alternative
matrix primitives and the width. -/
def SourceAtomCodesHaveLeastSupportAtWidth {d M M' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ) (width : ℕ) : Prop :=
  ∀ i : Fin M,
    HasLeastCodeSupportAtWidth alternative (matrix.col i) width

/-- A model-level defect of an alternative dictionary relative to the source:
at least one source atom has no sparse representation support that persists in
every other sparse representation of that atom. -/
def SourceAtomSupportUnstableAtWidth {d M M' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ) (width : ℕ) : Prop :=
  ∃ i : Fin M,
    ¬ HasLeastCodeSupportAtWidth alternative (matrix.col i) width

/-- The aggregate least-support premise fails exactly when some source atom is
support-unstable at that width. -/
theorem not_sourceAtomCodesHaveLeastSupportAtWidth_iff_unstable
    {d M M' width : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (alternative : Matrix (Fin d) (Fin M') ℝ) :
    ¬ SourceAtomCodesHaveLeastSupportAtWidth matrix alternative width ↔
      SourceAtomSupportUnstableAtWidth matrix alternative width := by
  classical
  simp only [SourceAtomCodesHaveLeastSupportAtWidth,
    SourceAtomSupportUnstableAtWidth, not_forall]

/-- A unique sparse coefficient vector for an atom supplies its least support.
This is the primitive-to-proof-object bridge: uniqueness is stated in terms of
the alternative matrix equation, while the conclusion constructs the support
core consumed by the Hall proof. -/
theorem hasLeastSupportAtWidth_of_unique_code
    {d M' width : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (atom : RepresentationVector d) (code : FeatureVector M')
    (hcode_card : (nonzeroSupport code).card ≤ width)
    (hfactor : alternative.mulVec code = atom)
    (hunique : ∀ other : FeatureVector M',
      (nonzeroSupport other).card ≤ width →
      alternative.mulVec other = atom → code = other) :
    HasLeastSupportAtWidth alternative atom width := by
  classical
  refine ⟨nonzeroSupport code, hcode_card, ?_, ?_⟩
  · rw [← hfactor]
    exact mulVec_mem_columnSpan_nonzeroSupport alternative code
  · intro target htarget_card hatom
    rw [← map_mulVecLin_coordinateSpan_eq_columnSpan] at hatom
    obtain ⟨targetCode, htargetCode_mem, htargetCode_eq⟩ := hatom
    have htargetCode_support : nonzeroSupport targetCode ⊆ target :=
      nonzeroSupport_subset_of_mem_coordinateSpan htargetCode_mem
    have htargetCode_card : (nonzeroSupport targetCode).card ≤ width :=
      (Finset.card_le_card htargetCode_support).trans htarget_card
    have hcodes_equal : code = targetCode := by
      apply hunique targetCode htargetCode_card
      simpa using htargetCode_eq
    rw [hcodes_equal]
    exact htargetCode_support

/-- A unique sparse atom code also satisfies the equivalent primitive
least-support condition on its representation fiber. -/
theorem hasLeastCodeSupportAtWidth_of_unique_code
    {d M' width : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (atom : RepresentationVector d) (code : FeatureVector M')
    (hcode_card : (nonzeroSupport code).card ≤ width)
    (hfactor : alternative.mulVec code = atom)
    (hunique : ∀ other : FeatureVector M',
      (nonzeroSupport other).card ≤ width →
      alternative.mulVec other = atom → code = other) :
    HasLeastCodeSupportAtWidth alternative atom width := by
  apply (hasLeastCodeSupportAtWidth_iff_hasLeastSupportAtWidth
    alternative atom).2
  exact hasLeastSupportAtWidth_of_unique_code alternative atom code
    hcode_card hfactor hunique

/-- If a represented atom has no least sparse-code support, then its
alternative representation fiber contains a second, distinct sparse code. -/
theorem exists_distinct_sparse_code_of_not_hasLeastCodeSupportAtWidth
    {d M' width : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (atom : RepresentationVector d) (code : FeatureVector M')
    (hcode_card : (nonzeroSupport code).card ≤ width)
    (hfactor : alternative.mulVec code = atom)
    (hnotleast : ¬ HasLeastCodeSupportAtWidth alternative atom width) :
    ∃ other : FeatureVector M',
      (nonzeroSupport other).card ≤ width ∧
        alternative.mulVec other = atom ∧ code ≠ other := by
  classical
  by_contra hno_other
  apply hnotleast
  apply hasLeastCodeSupportAtWidth_of_unique_code alternative atom code
    hcode_card hfactor
  intro other hother_card hother_factor
  by_contra hcode_ne
  apply hno_other
  exact ⟨other, hother_card, hother_factor, hcode_ne⟩

/-- An explicit sparse representation has least support among all
representations at width `width` under the atom-local heterogeneous spark
test.  If its actual support has size `r`, the condition is
`min (r + width) M' < spark alternative`, strictly weaker than global
injectivity on all width-sparse codes whenever `r < width`. -/
theorem hasLeastSupportAtWidth_of_code_of_sum_spark
    {d M' width : ℕ}
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (atom : RepresentationVector d) (code : FeatureVector M')
    (hcode_card : (nonzeroSupport code).card ≤ width)
    (hfactor : atom = alternative.mulVec code)
    (hcutoff :
      min ((nonzeroSupport code).card + width) M' < spark alternative) :
    HasLeastSupportAtWidth alternative atom width := by
  classical
  refine ⟨nonzeroSupport code, hcode_card, ?_, ?_⟩
  · rw [hfactor]
    exact mulVec_mem_columnSpan_nonzeroSupport alternative code
  · intro target htarget_card hatom
    rw [← map_mulVecLin_coordinateSpan_eq_columnSpan] at hatom
    obtain ⟨targetCode, htargetCode_mem, htargetCode_eq⟩ := hatom
    have htargetCode_support : nonzeroSupport targetCode ⊆ target :=
      nonzeroSupport_subset_of_mem_coordinateSpan htargetCode_mem
    have htargetCode_card : (nonzeroSupport targetCode).card ≤ width :=
      (Finset.card_le_card htargetCode_support).trans htarget_card
    have hcodes_equal : code = targetCode := by
      apply eq_of_mulVec_eq_of_two_sparse_supports_of_sum_min_lt_spark
        alternative code targetCode (Nat.le_refl _) htargetCode_card hcutoff
      calc
        alternative.mulVec code = atom := hfactor.symm
        _ = alternative.mulVec targetCode := by
          simpa using htargetCode_eq.symm
    rw [hcodes_equal]
    exact htargetCode_support

/-- Least-support cores turn the plane-wise supports selected by richness into
one compatible atom-indexed support system.  This is the direct formalization
of the weakest clean structural repair proposed for the source appendix; it
uses neither global sparse-code injectivity nor unique coefficients. -/
theorem exists_compatible_supports_of_kRich_and_support_cores
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hcores : ∀ i : Fin M,
      HasLeastSupportAtWidth alternative (matrix.col i) (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ supports : Fin M → Finset (Fin M'),
      ∃ coordinateSupports : Finset (Fin M) → Finset (Fin M'),
      (∀ i, (supports i).card ≤ min K' M') ∧
      (∀ i, matrix.col i ∈ columnSpan alternative (supports i)) ∧
      (∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
        (coordinateSupports coordinateSet).card ≤ min K' M') ∧
      ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
        ∀ i ∈ coordinateSet,
          supports i ⊆ coordinateSupports coordinateSet := by
  classical
  choose supports hsupports_card hsupports_span hsupports_least using hcores
  have hcoordinate_exists : ∀ coordinateSet : Finset (Fin M),
      coordinateSet.card = K →
      ∃ target : Finset (Fin M'),
        target.card ≤ min K' M' ∧
          Submodule.map matrix.mulVecLin (coordinateSpan coordinateSet) ≤
            columnSpan alternative target := by
    intro coordinateSet hcoordinateSet
    obtain ⟨target, htarget⟩ :=
      AppendixHall.exists_sparse_alternative_subspace_containing_coordinate_image
        matrix z f alternative alternativeCode hrich hfactors
        (kSparse_min_columnCount alternativeCode halternativeSparse)
        halternativeFactors coordinateSet hcoordinateSet
    exact ⟨target.1, target.2, htarget⟩
  let coordinateSupports : Finset (Fin M) → Finset (Fin M') :=
    fun coordinateSet =>
      if h : coordinateSet.card = K then
        Classical.choose (hcoordinate_exists coordinateSet h)
      else ∅
  have hcoordinate_card : ∀ coordinateSet : Finset (Fin M),
      coordinateSet.card = K →
        (coordinateSupports coordinateSet).card ≤ min K' M' := by
    intro coordinateSet hcoordinateSet
    simp only [coordinateSupports, dif_pos hcoordinateSet]
    exact (Classical.choose_spec
      (hcoordinate_exists coordinateSet hcoordinateSet)).1
  have hcoordinate_span : ∀ coordinateSet : Finset (Fin M),
      coordinateSet.card = K →
      Submodule.map matrix.mulVecLin (coordinateSpan coordinateSet) ≤
        columnSpan alternative (coordinateSupports coordinateSet) := by
    intro coordinateSet hcoordinateSet
    simp only [coordinateSupports, dif_pos hcoordinateSet]
    exact (Classical.choose_spec
      (hcoordinate_exists coordinateSet hcoordinateSet)).2
  refine ⟨supports, coordinateSupports, hsupports_card, hsupports_span,
    hcoordinate_card, ?_⟩
  intro coordinateSet hcoordinateSet i hi
  apply hsupports_least i (coordinateSupports coordinateSet)
    (hcoordinate_card coordinateSet hcoordinateSet)
  apply hcoordinate_span coordinateSet hcoordinateSet
  rw [map_mulVecLin_coordinateSpan_eq_columnSpan]
  apply Submodule.subset_span
  exact ⟨⟨i, hi⟩, rfl⟩

/-- A width budget below the optimized source-spark Hall cutoff cannot reduce
the number of atoms when every source atom has a least alternative support at
that budget.  This is the Hall conclusion under the support-core premise
rather than the stronger global alternative-injectivity premise. -/
theorem atom_count_le_of_kRich_and_support_cores
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hK_le_M : K ≤ M)
    (hcutoff : min K' M' + 1 ≤ min (2 * K) (spark matrix - 1))
    (hcores : ∀ i : Fin M,
      HasLeastSupportAtWidth alternative (matrix.col i) (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    M ≤ M' := by
  obtain ⟨supports, coordinateSupports, _hsupport_card, hatom,
      hcoordinate_card, hcompatible⟩ :=
    exists_compatible_supports_of_kRich_and_support_cores
      matrix z f alternative alternativeCode hcores hrich hfactors
        halternativeSparse halternativeFactors
  exact AppendixHall.atom_count_le_alternative_count_of_spark_compatibility
    matrix alternative supports coordinateSupports hcutoff hK_le_M hatom
      hcompatible hcoordinate_card

/-- Contrapositive support-core theorem. Under strict width reduction, the
effective alternative sparsity reaches the source's optimized Hall cutoff.
This is the direct formal counterpart of the memo's `(Core) ⇒ (Hall-spark)`
route. -/
theorem effective_sparsity_ge_spark_cutoff_of_strict_width_and_support_cores
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hcores : ∀ i : Fin M,
      HasLeastSupportAtWidth alternative (matrix.col i) (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' := by
  by_contra hnot
  have hcutoff :
      min K' M' + 1 ≤ min (2 * K) (spark matrix - 1) := by
    omega
  have hcount := atom_count_le_of_kRich_and_support_cores
    matrix z f alternative alternativeCode hK_le_M hcutoff hcores hrich
      hfactors halternativeSparse halternativeFactors
  omega

/-- Under source full spark, least alternative supports yield the sharp
dimension-limited compatible Hall threshold `min (2*K) d`. -/
theorem effective_sparsity_ge_dimension_cutoff_of_strict_width_and_support_cores
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1)
    (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hcores : ∀ i : Fin M,
      HasLeastSupportAtWidth alternative (matrix.col i) (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) d ≤ min K' M' := by
  have hbound :=
    effective_sparsity_ge_spark_cutoff_of_strict_width_and_support_cores
      matrix z f alternative alternativeCode hK_le_M hwidth hcores hrich
        hfactors halternativeSparse halternativeFactors
  simpa [hspark] using hbound

/-- Primitive coefficient-fiber version of the support-core theorem.  The
additional premise says directly that every source atom has an alternative
sparse code whose support is contained in the support of every other sparse
code for that atom; the compatible Hall supports are derived, not assumed. -/
theorem effective_sparsity_ge_spark_cutoff_of_strict_width_and_least_code_supports
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hleast : SourceAtomCodesHaveLeastSupportAtWidth matrix alternative
      (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' := by
  apply effective_sparsity_ge_spark_cutoff_of_strict_width_and_support_cores
    matrix z f alternative alternativeCode hK_le_M hwidth
  · intro i
    exact (hasLeastCodeSupportAtWidth_iff_hasLeastSupportAtWidth
      alternative (matrix.col i)).1 (hleast i)
  · exact hrich
  · exact hfactors
  · exact halternativeSparse
  · exact halternativeFactors

/-- Under source full spark, the primitive least-code-support premise yields
the exact dimension-limited strict-width cutoff. -/
theorem effective_sparsity_ge_dimension_cutoff_of_strict_width_and_least_code_supports
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1)
    (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hleast : SourceAtomCodesHaveLeastSupportAtWidth matrix alternative
      (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) d ≤ min K' M' := by
  have hbound :=
    effective_sparsity_ge_spark_cutoff_of_strict_width_and_least_code_supports
      matrix z f alternative alternativeCode hK_le_M hwidth hleast hrich
        hfactors halternativeSparse halternativeFactors
  simpa [hspark] using hbound

/-- In the intended dimension range, the primitive least-code-support premise
recovers the paper's advertised declared-sparsity cliff. -/
theorem twoK_le_alternative_sparsity_of_strict_width_and_least_code_supports
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1) (h2K_le_d : 2 * K ≤ d)
    (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hleast : SourceAtomCodesHaveLeastSupportAtWidth matrix alternative
      (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 * K ≤ K' := by
  calc
    2 * K = min (2 * K) d := (Nat.min_eq_left h2K_le_d).symm
    _ ≤ min K' M' :=
      effective_sparsity_ge_dimension_cutoff_of_strict_width_and_least_code_supports
        matrix z f alternative alternativeCode hspark hK_le_M hwidth hleast
          hrich hfactors halternativeSparse halternativeFactors
    _ ≤ K' := Nat.min_le_left K' M'

/-- Universal source-side repair of the strict-width result.  Every narrower
alternative either pays the advertised effective `2*K` sparsity cost or is
support-unstable on at least one source atom.  Thus support stability appears
as an adverse conclusion about the alternative, not an added theorem premise. -/
theorem twoK_le_effective_sparsity_or_source_atom_support_unstable
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1) (h2K_le_d : 2 * K ≤ d)
    (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 * K ≤ min K' M' ∨
      SourceAtomSupportUnstableAtWidth matrix alternative (min K' M') := by
  by_cases hleast : SourceAtomCodesHaveLeastSupportAtWidth matrix alternative
      (min K' M')
  · left
    calc
      2 * K = min (2 * K) d := (Nat.min_eq_left h2K_le_d).symm
      _ ≤ min K' M' :=
        effective_sparsity_ge_dimension_cutoff_of_strict_width_and_least_code_supports
          matrix z f alternative alternativeCode hspark hK_le_M hwidth
            hleast hrich hfactors halternativeSparse halternativeFactors
  · right
    exact (not_sourceAtomCodesHaveLeastSupportAtWidth_iff_unstable
      matrix alternative).1 hleast

/-- Spark-adaptive form of the same universal dichotomy. -/
theorem spark_cutoff_le_effective_sparsity_or_source_atom_support_unstable
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' ∨
      SourceAtomSupportUnstableAtWidth matrix alternative (min K' M') := by
  by_cases hleast : SourceAtomCodesHaveLeastSupportAtWidth matrix alternative
      (min K' M')
  · left
    exact effective_sparsity_ge_spark_cutoff_of_strict_width_and_least_code_supports
      matrix z f alternative alternativeCode hK_le_M hwidth hleast hrich
        hfactors halternativeSparse halternativeFactors
  · right
    exact (not_sourceAtomCodesHaveLeastSupportAtWidth_iff_unstable
      matrix alternative).1 hleast

/-- More elementary consequence of the support-instability dichotomy.  A
narrow alternative below the `2*K` cliff must give some source atom two
distinct sparse coefficient vectors. -/
theorem twoK_le_effective_sparsity_or_source_atom_code_collision
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1) (h2K_le_d : 2 * K ≤ d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 * K ≤ min K' M' ∨
      ∃ i : Fin M, ∃ left right : FeatureVector M',
        (nonzeroSupport left).card ≤ min K' M' ∧
        (nonzeroSupport right).card ≤ min K' M' ∧
        alternative.mulVec left = matrix.col i ∧
        alternative.mulVec right = matrix.col i ∧ left ≠ right := by
  rcases twoK_le_effective_sparsity_or_source_atom_support_unstable
      matrix z f alternative alternativeCode hspark h2K_le_d hK_le_M
        hwidth hrich hfactors halternativeSparse halternativeFactors with
    htwoK | ⟨i, hi_unstable⟩
  · exact Or.inl htwoK
  · right
    obtain ⟨atomCode, hatomCode_card, hatomCode_factor⟩ :=
      exists_sparse_source_atom_factorization_of_kRich_and_factorizations
        matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
          halternativeSparse halternativeFactors
    obtain ⟨other, hother_card, hother_factor, hne⟩ :=
      exists_distinct_sparse_code_of_not_hasLeastCodeSupportAtWidth
        alternative (matrix.col i) (atomCode i) (hatomCode_card i)
          (hatomCode_factor i).symm hi_unstable
    exact ⟨i, atomCode i, other, hatomCode_card i, hother_card,
      (hatomCode_factor i).symm, hother_factor, hne⟩

/-- Spark-adaptive source-atom collision dichotomy.  This is the strongest
paper-facing primitive version before specializing the source to full spark. -/
theorem spark_cutoff_le_effective_sparsity_or_source_atom_code_collision
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' ∨
      ∃ i : Fin M, ∃ left right : FeatureVector M',
        (nonzeroSupport left).card ≤ min K' M' ∧
        (nonzeroSupport right).card ≤ min K' M' ∧
        alternative.mulVec left = matrix.col i ∧
        alternative.mulVec right = matrix.col i ∧ left ≠ right := by
  rcases spark_cutoff_le_effective_sparsity_or_source_atom_support_unstable
      matrix z f alternative alternativeCode hK_le_M hwidth hrich hfactors
        halternativeSparse halternativeFactors with
    hcutoff | ⟨i, hi_unstable⟩
  · exact Or.inl hcutoff
  · right
    obtain ⟨atomCode, hatomCode_card, hatomCode_factor⟩ :=
      exists_sparse_source_atom_factorization_of_kRich_and_factorizations
        matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
          halternativeSparse halternativeFactors
    obtain ⟨other, hother_card, hother_factor, hne⟩ :=
      exists_distinct_sparse_code_of_not_hasLeastCodeSupportAtWidth
        alternative (matrix.col i) (atomCode i) (hatomCode_card i)
          (hatomCode_factor i).symm hi_unstable
    exact ⟨i, atomCode i, other, hatomCode_card i, hother_card,
      (hatomCode_factor i).symm, hother_factor, hne⟩

/-- Atomwise uniqueness of the sparse alternative representation of every
source atom is a model-matrix premise that constructs the least-support cores
used by the Hall proof.  Unlike global sparse injectivity, it imposes no
condition on fibers over vectors that are not source atoms. -/
theorem effective_sparsity_ge_spark_cutoff_of_strict_width_and_atomwise_unique
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hatomwiseUnique :
      SourceAtomCodesUniqueAtWidth matrix alternative (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' := by
  obtain ⟨atomCode, hatomCode_card, hatomCode_factor⟩ :=
    exists_sparse_source_atom_factorization_of_kRich_and_factorizations
      matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
        halternativeSparse halternativeFactors
  apply effective_sparsity_ge_spark_cutoff_of_strict_width_and_support_cores
    matrix z f alternative alternativeCode hK_le_M hwidth
  · intro i
    apply hasLeastSupportAtWidth_of_unique_code alternative (matrix.col i)
      (atomCode i) (hatomCode_card i) (hatomCode_factor i).symm
    intro other hother_card hother_factor
    exact hatomwiseUnique i (atomCode i) other (hatomCode_card i)
      hother_card (hatomCode_factor i).symm hother_factor
  · exact hrich
  · exact hfactors
  · exact halternativeSparse
  · exact halternativeFactors

/-- Under source full spark, atomwise alternative-code uniqueness yields the
dimension-limited strict-width cutoff. -/
theorem effective_sparsity_ge_dimension_cutoff_of_strict_width_and_atomwise_unique
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hatomwiseUnique :
      SourceAtomCodesUniqueAtWidth matrix alternative (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) d ≤ min K' M' := by
  have hbound :=
    effective_sparsity_ge_spark_cutoff_of_strict_width_and_atomwise_unique
      matrix z f alternative alternativeCode hKpos hK_le_M hwidth
        hatomwiseUnique hrich hfactors halternativeSparse halternativeFactors
  simpa [hspark] using hbound

/-- In the intended dimension range, the primitive atomwise-uniqueness premise
recovers the paper's advertised declared-sparsity cliff. -/
theorem twoK_le_alternative_sparsity_of_strict_width_and_atomwise_unique
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1) (h2K_le_d : 2 * K ≤ d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hatomwiseUnique :
      SourceAtomCodesUniqueAtWidth matrix alternative (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 * K ≤ K' := by
  calc
    2 * K = min (2 * K) d := (Nat.min_eq_left h2K_le_d).symm
    _ ≤ min K' M' :=
      effective_sparsity_ge_dimension_cutoff_of_strict_width_and_atomwise_unique
        matrix z f alternative alternativeCode hspark hKpos hK_le_M hwidth
          hatomwiseUnique hrich hfactors halternativeSparse
          halternativeFactors
    _ ≤ K' := Nat.min_le_left K' M'

/-- Every narrower alternative either pays effective sparsity `2*K` or fails
unique sparse decoding on the closure of the represented data.  This is a
universal theorem with source-side assumptions only; decodability occurs in an
adverse conclusion, not as an added premise of the stated dichotomy. -/
theorem twoK_le_effective_sparsity_or_not_uniquelySparseDecodableOn_closure
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1) (h2K_le_d : 2 * K ≤ d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 * K ≤ min K' M' ∨
      ¬ UniquelySparseDecodableOn alternative
        (closure (Set.range f)) (min K' M') := by
  by_cases hdecodable : UniquelySparseDecodableOn alternative
      (closure (Set.range f)) (min K' M')
  · left
    calc
      2 * K = min (2 * K) d := (Nat.min_eq_left h2K_le_d).symm
      _ ≤ min K' M' :=
        effective_sparsity_ge_dimension_cutoff_of_strict_width_and_atomwise_unique
          matrix z f alternative alternativeCode hspark hKpos hK_le_M
            hwidth
            (sourceAtomCodesUniqueAtWidth_of_uniquelySparseDecodableOn_closure
              matrix z f alternative hKpos hK_le_M hrich hfactors
                hdecodable)
            hrich hfactors halternativeSparse halternativeFactors
  · exact Or.inr hdecodable

/-- Spark-adaptive form of the closure-relative sparse-identification
dichotomy. -/
theorem spark_cutoff_le_effective_sparsity_or_not_uniquelySparseDecodableOn_closure
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' ∨
      ¬ UniquelySparseDecodableOn alternative
        (closure (Set.range f)) (min K' M') := by
  by_cases hdecodable : UniquelySparseDecodableOn alternative
      (closure (Set.range f)) (min K' M')
  · left
    exact effective_sparsity_ge_spark_cutoff_of_strict_width_and_atomwise_unique
      matrix z f alternative alternativeCode hKpos hK_le_M hwidth
        (sourceAtomCodesUniqueAtWidth_of_uniquelySparseDecodableOn_closure
          matrix z f alternative hKpos hK_le_M hrich hfactors hdecodable)
        hrich hfactors halternativeSparse halternativeFactors
  · exact Or.inr hdecodable

/-- If a nonzero point on every pure source-atom ray is observed, the same
dichotomy puts the failure of unique sparse decoding on the actual data range
rather than only its closure. -/
theorem twoK_le_effective_sparsity_or_not_uniquelySparseDecodableOn_range
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1) (h2K_le_d : 2 * K ≤ d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hraysRealized : SourceAtomRaysRealized z)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 * K ≤ min K' M' ∨
      ¬ UniquelySparseDecodableOn alternative
        (Set.range f) (min K' M') := by
  by_cases hdecodable : UniquelySparseDecodableOn alternative
      (Set.range f) (min K' M')
  · left
    calc
      2 * K = min (2 * K) d := (Nat.min_eq_left h2K_le_d).symm
      _ ≤ min K' M' :=
        effective_sparsity_ge_dimension_cutoff_of_strict_width_and_atomwise_unique
          matrix z f alternative alternativeCode hspark hKpos hK_le_M
            hwidth
            (sourceAtomCodesUniqueAtWidth_of_uniquelySparseDecodableOn_range_of_rays
              matrix z f alternative hraysRealized hfactors hdecodable)
            hrich hfactors halternativeSparse halternativeFactors
  · exact Or.inr hdecodable

/-- If nonzero points on all pure source-atom rays are observed, the
spark-adaptive dichotomy places the identification failure on the actual output
range. -/
theorem spark_cutoff_le_effective_sparsity_or_not_uniquelySparseDecodableOn_range
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hraysRealized : SourceAtomRaysRealized z)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' ∨
      ¬ UniquelySparseDecodableOn alternative
        (Set.range f) (min K' M') := by
  by_cases hdecodable : UniquelySparseDecodableOn alternative
      (Set.range f) (min K' M')
  · left
    exact effective_sparsity_ge_spark_cutoff_of_strict_width_and_atomwise_unique
      matrix z f alternative alternativeCode hKpos hK_le_M hwidth
        (sourceAtomCodesUniqueAtWidth_of_uniquelySparseDecodableOn_range_of_rays
          matrix z f alternative hraysRealized hfactors hdecodable)
        hrich hfactors halternativeSparse halternativeFactors
  · exact Or.inr hdecodable

/-- Atom-local numerical version of the support-core Hall repair. Each source
atom may use its own actual support size `r_i`; only
`min (r_i + min K' M') M' < spark alternative` is required.  This is weaker
than global injectivity on all `min K' M'`-sparse codes. -/
theorem effective_sparsity_ge_dimension_cutoff_of_atomwise_spark
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (atomCode : Fin M → FeatureVector M')
    (hspark : spark matrix = d + 1)
    (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hatomSparse : ∀ i,
      (nonzeroSupport (atomCode i)).card ≤ min K' M')
    (hatomFactors : ∀ i,
      matrix.col i = alternative.mulVec (atomCode i))
    (hatomCutoff : ∀ i,
      min ((nonzeroSupport (atomCode i)).card + min K' M') M' <
        spark alternative)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) d ≤ min K' M' := by
  apply effective_sparsity_ge_dimension_cutoff_of_strict_width_and_support_cores
    matrix z f alternative alternativeCode hspark hK_le_M hwidth
  · intro i
    exact hasLeastSupportAtWidth_of_code_of_sum_spark alternative
      (matrix.col i) (atomCode i) (hatomSparse i) (hatomFactors i)
        (hatomCutoff i)
  · exact hrich
  · exact hfactors
  · exact halternativeSparse
  · exact halternativeFactors

/-- Alternative sparse-code injectivity turns the two independently selected
support systems supplied by richness into one compatible system. This is the
source-to-model bridge missing from the archived Hall proof. -/
theorem exists_compatible_supports_of_kRich_and_injective_alternative
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (halternativeInjective : KSparseInjective alternative (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ supports : Fin M → Finset (Fin M'),
      ∃ coordinateSupports : Finset (Fin M) → Finset (Fin M'),
      (∀ i, (supports i).card ≤ min K' M') ∧
      (∀ i, matrix.col i ∈ columnSpan alternative (supports i)) ∧
      (∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
        (coordinateSupports coordinateSet).card ≤ min K' M') ∧
      ∀ coordinateSet : Finset (Fin M), coordinateSet.card = K →
        ∀ i ∈ coordinateSet,
          supports i ⊆ coordinateSupports coordinateSet := by
  classical
  obtain ⟨code, hcode_card, hcode⟩ :=
    exists_sparse_source_atom_factorization_of_kRich_and_factorizations
      matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
        halternativeSparse halternativeFactors
  let supports : Fin M → Finset (Fin M') :=
    fun i => nonzeroSupport (code i)
  have hcoordinate_exists : ∀ coordinateSet : Finset (Fin M),
      coordinateSet.card = K →
      ∃ target : Finset (Fin M'),
        target.card ≤ min K' M' ∧
          Submodule.map matrix.mulVecLin (coordinateSpan coordinateSet) ≤
            columnSpan alternative target := by
    intro coordinateSet hcoordinateSet
    obtain ⟨target, htarget⟩ :=
      AppendixHall.exists_sparse_alternative_subspace_containing_coordinate_image
        matrix z f alternative alternativeCode hrich hfactors
        (kSparse_min_columnCount alternativeCode halternativeSparse)
        halternativeFactors coordinateSet hcoordinateSet
    exact ⟨target.1, target.2, htarget⟩
  let coordinateSupports : Finset (Fin M) → Finset (Fin M') :=
    fun coordinateSet =>
      if h : coordinateSet.card = K then
        Classical.choose (hcoordinate_exists coordinateSet h)
      else ∅
  have hcoordinate_card : ∀ coordinateSet : Finset (Fin M),
      coordinateSet.card = K →
        (coordinateSupports coordinateSet).card ≤ min K' M' := by
    intro coordinateSet hcoordinateSet
    simp only [coordinateSupports, dif_pos hcoordinateSet]
    exact (Classical.choose_spec
      (hcoordinate_exists coordinateSet hcoordinateSet)).1
  have hcoordinate_span : ∀ coordinateSet : Finset (Fin M),
      coordinateSet.card = K →
      Submodule.map matrix.mulVecLin (coordinateSpan coordinateSet) ≤
        columnSpan alternative (coordinateSupports coordinateSet) := by
    intro coordinateSet hcoordinateSet
    simp only [coordinateSupports, dif_pos hcoordinateSet]
    exact (Classical.choose_spec
      (hcoordinate_exists coordinateSet hcoordinateSet)).2
  have hatom : ∀ i : Fin M,
      matrix.col i ∈ columnSpan alternative (supports i) := by
    intro i
    rw [hcode i]
    exact mulVec_mem_columnSpan_nonzeroSupport alternative (code i)
  have hcompatible : ∀ coordinateSet : Finset (Fin M),
      coordinateSet.card = K → ∀ i ∈ coordinateSet,
        supports i ⊆ coordinateSupports coordinateSet := by
    intro coordinateSet hcoordinateSet i hi
    have hsource_mem : matrix.col i ∈
        Submodule.map matrix.mulVecLin (coordinateSpan coordinateSet) := by
      rw [map_mulVecLin_coordinateSpan_eq_columnSpan]
      apply Submodule.subset_span
      exact ⟨⟨i, hi⟩, rfl⟩
    have htarget_mem : matrix.col i ∈
        columnSpan alternative (coordinateSupports coordinateSet) :=
      hcoordinate_span coordinateSet hcoordinateSet hsource_mem
    rw [← map_mulVecLin_coordinateSpan_eq_columnSpan] at htarget_mem
    obtain ⟨targetCode, htargetCode_mem, htargetCode_eq⟩ := htarget_mem
    have htargetCode_support : nonzeroSupport targetCode ⊆
        coordinateSupports coordinateSet :=
      nonzeroSupport_subset_of_mem_coordinateSpan htargetCode_mem
    have htargetCode_card :
        (nonzeroSupport targetCode).card ≤ min K' M' :=
      (Finset.card_le_card htargetCode_support).trans
        (hcoordinate_card coordinateSet hcoordinateSet)
    have hcodes_equal : code i = targetCode := by
      apply halternativeInjective (code i) targetCode
        (hcode_card i) htargetCode_card
      calc
        alternative.mulVec (code i) = matrix.col i := (hcode i).symm
        _ = alternative.mulVec targetCode := by
          simpa using htargetCode_eq.symm
    change nonzeroSupport (code i) ⊆ coordinateSupports coordinateSet
    rwa [hcodes_equal]
  refine ⟨supports, coordinateSupports, ?_, hatom, hcoordinate_card,
    hcompatible⟩
  intro i
  exact hcode_card i

/-- In the equal-width, equal-sparsity endpoint, alternative sparse-code
injectivity supplies compatibility and the cutoff `K + 1 < spark(A)` is enough
for the Hall argument to identify all columns.  This is a useful conditional
route, although global alternative injectivity is stronger than the atom-local
compatibility needed by Hall. -/
theorem equal_size_columnsEquivalent_of_injective_alternative
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hKpos : 0 < K) (hK_lt_M : K < M)
    (hcutoff : K + 1 < spark matrix)
    (halternativeInjective : KSparseInjective alternative K)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ColumnsEquivalentUpToPermutationAndScaling matrix alternative := by
  classical
  have hK_le_M : K ≤ M := hK_lt_M.le
  have hmin : min K M = K := Nat.min_eq_left hK_le_M
  obtain ⟨supports, coordinateSupports, _hsupport_card, hatom,
      hcoordinate_card, hcompatible⟩ :=
    exists_compatible_supports_of_kRich_and_injective_alternative
      matrix z f alternative alternativeCode hKpos hK_le_M
        (by simpa [hmin] using halternativeInjective) hrich hfactors
        halternativeSparse halternativeFactors
  have hupper : ∀ vertices : Finset (Fin M), vertices.card ≤ K →
      (neighborhood supports vertices).card ≤ K := by
    apply neighborhood_card_le_of_coordinate_support_compatibility
      supports coordinateSupports hK_le_M hcompatible
    intro coordinateSet hcoordinateSet
    simpa [hmin] using hcoordinate_card coordinateSet hcoordinateSet
  have hglobal : GlobalHall supports := by
    apply local_hall_implies_global_up_to supports K K (K + 1)
    · omega
    · omega
    · exact local_hall_lower_up_to_of_spark_and_atom_supports_general
        matrix alternative supports hcutoff hatom
    · exact hupper
  obtain ⟨matching, hmatching, hsingleton⟩ :=
    supports_singleton_of_equal_width supports hKpos hK_lt_M hglobal hupper
  let matchingEquiv : Equiv.Perm (Fin M) :=
    Equiv.ofBijective matching hmatching
  let permutation : Equiv.Perm (Fin M) := matchingEquiv.symm
  have hscale_exists : ∀ j : Fin M, ∃ scale : ℝ,
      scale ≠ 0 ∧
        alternative.col j = scale • matrix.col (permutation j) := by
    intro j
    have hmatching_inverse : matching (permutation j) = j := by
      change matchingEquiv (matchingEquiv.symm j) = j
      exact matchingEquiv.apply_symm_apply j
    have hsource_mem : matrix.col (permutation j) ∈
        ℝ ∙ alternative.col j := by
      rw [← familySpan_singleton (R := ℝ) alternative.col j,
        familySpan_matrix_columns_eq_columnSpan]
      simpa [hsingleton (permutation j), hmatching_inverse] using
        hatom (permutation j)
    obtain ⟨coefficient, hcoefficient⟩ :=
      Submodule.mem_span_singleton.mp hsource_mem
    have hsource_ne : matrix.col (permutation j) ≠ 0 := by
      have hli := linearIndependent_of_card_lt_spark matrix
        ({permutation j} : Finset (Fin M)) (by simp; omega)
      have hne := hli.ne_zero
        (⟨permutation j, Finset.mem_singleton_self _⟩ :
          {i // i ∈ ({permutation j} : Finset (Fin M))})
      simpa [selectedColumns] using hne
    have hcoefficient_ne : coefficient ≠ 0 := by
      intro hzero
      apply hsource_ne
      rw [← hcoefficient, hzero]
      simp
    refine ⟨coefficient⁻¹, inv_ne_zero hcoefficient_ne, ?_⟩
    calc
      alternative.col j =
          (coefficient⁻¹ * coefficient) • alternative.col j := by
        simp [hcoefficient_ne]
      _ = coefficient⁻¹ • (coefficient • alternative.col j) := by
        rw [smul_smul]
      _ = coefficient⁻¹ • matrix.col (permutation j) := by
        rw [hcoefficient]
  choose scale hscale_ne hcolumns using hscale_exists
  exact ⟨permutation, scale, hscale_ne, hcolumns⟩

/-- With source sparsity added, the same conditional route recovers every code
through injectivity of the alternative matrix.  The returned permutation and
scaling act simultaneously on columns and codes. -/
theorem equal_size_dictionary_and_code_identifiability_of_injective_alternative
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hKpos : 0 < K) (hK_lt_M : K < M)
    (hcutoff : K + 1 < spark matrix)
    (halternativeInjective : KSparseInjective alternative K)
    (hrich : KRich (K := K) z)
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ permutation : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      (∀ i, alternative.col i = scale i • matrix.col (permutation i)) ∧
      ∀ x, z x = alignAlternativeCode permutation scale (alternativeCode x) := by
  obtain ⟨permutation, scale, hscale, hcolumns⟩ :=
    equal_size_columnsEquivalent_of_injective_alternative
      matrix z f alternative alternativeCode hKpos hK_lt_M hcutoff
      halternativeInjective hrich hfactors halternativeSparse
      halternativeFactors
  refine ⟨permutation, scale, hscale, hcolumns, ?_⟩
  have hunalignedSparse : KSparse (K := K)
      (fun x => unalignSourceCode permutation scale (z x)) :=
    kSparse_unalignSourceCode permutation scale hscale z hsourceSparse
  intro x
  have hcodes : alternativeCode x =
      unalignSourceCode permutation scale (z x) := by
    apply halternativeInjective _ _ (halternativeSparse x)
      (hunalignedSparse x)
    calc
      alternative.mulVec (alternativeCode x) = f x :=
        (halternativeFactors x).symm
      _ = matrix.mulVec (z x) := hfactors x
      _ = alternative.mulVec
          (unalignSourceCode permutation scale (z x)) :=
        (mulVec_unalignSourceCode matrix alternative permutation scale
          hscale hcolumns (z x)).symm
  calc
    z x = alignAlternativeCode permutation scale
        (unalignSourceCode permutation scale (z x)) :=
      (alignAlternativeCode_unalignSourceCode permutation scale hscale
        (z x)).symm
    _ = alignAlternativeCode permutation scale (alternativeCode x) := by
      rw [← hcodes]

/-- If effective alternative sparsity lies strictly below the source's
spark-adaptive Hall cutoff, sparse-code injectivity prevents any width
reduction. -/
theorem atom_count_le_of_kRich_and_injective_alternative
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hcutoff : min K' M' + 1 ≤ min (2 * K) (spark matrix - 1))
    (halternativeInjective : KSparseInjective alternative (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    M ≤ M' := by
  obtain ⟨supports, coordinateSupports, _hsupport_card, hatom,
      hcoordinate_card, hcompatible⟩ :=
    exists_compatible_supports_of_kRich_and_injective_alternative
      matrix z f alternative alternativeCode hKpos hK_le_M
        halternativeInjective hrich hfactors halternativeSparse
        halternativeFactors
  exact AppendixHall.atom_count_le_alternative_count_of_spark_compatibility
    matrix alternative supports coordinateSupports hcutoff hK_le_M hatom
      hcompatible hcoordinate_card

/-- Contrapositive strict-width form of the conditional Hall theorem. The
conclusion is stated for effective sparsity and is therefore stronger than a
bound on the declared sparsity alone. -/
theorem effective_sparsity_ge_spark_cutoff_of_strict_width
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (halternativeInjective : KSparseInjective alternative (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' := by
  by_contra hnot
  have hcutoff :
      min K' M' + 1 ≤ min (2 * K) (spark matrix - 1) := by
    omega
  have hcount := atom_count_le_of_kRich_and_injective_alternative
    matrix z f alternative alternativeCode hKpos hK_le_M hcutoff
      halternativeInjective hrich hfactors halternativeSparse
      halternativeFactors
  omega

/-- Under source full spark, strict width reduction with an injective
alternative factorization costs effective sparsity at least `min (2*K) d`.
This remains sharp when the ambient dimension is below `2*K`. -/
theorem effective_sparsity_ge_dimension_cutoff_of_strict_width
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (halternativeInjective : KSparseInjective alternative (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) d ≤ min K' M' := by
  have hbound := effective_sparsity_ge_spark_cutoff_of_strict_width
    matrix z f alternative alternativeCode hKpos hK_le_M hwidth
      halternativeInjective hrich hfactors halternativeSparse
      halternativeFactors
  simpa [hspark] using hbound

/-- Pure spark specialization of alternative sparse-code injectivity. -/
theorem effective_sparsity_ge_dimension_cutoff_of_alternative_spark
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hsourceSpark : spark matrix = d + 1)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (halternativeSpark :
      min (2 * min K' M') M' < spark alternative)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) d ≤ min K' M' := by
  apply effective_sparsity_ge_dimension_cutoff_of_strict_width
    matrix z f alternative alternativeCode hsourceSpark hKpos hK_le_M
      hwidth
  · exact (kSparseInjective_iff_min_lt_spark alternative).2
      halternativeSpark
  · exact hrich
  · exact hfactors
  · exact halternativeSparse
  · exact halternativeFactors

/-- Fully numerical universal dichotomy.  A narrower alternative either
reaches the source's spark-adaptive sparsity cutoff or its own spark is too low
for injectivity on all effectively sparse codes. -/
theorem spark_cutoff_le_effective_sparsity_or_alternative_spark_le
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    min (2 * K) (spark matrix - 1) ≤ min K' M' ∨
      spark alternative ≤ min (2 * min K' M') M' := by
  by_cases halternativeSpark :
      min (2 * min K' M') M' < spark alternative
  · left
    apply effective_sparsity_ge_spark_cutoff_of_strict_width
      matrix z f alternative alternativeCode hKpos hK_le_M hwidth
    · exact (kSparseInjective_iff_min_lt_spark alternative).2
        halternativeSpark
    · exact hrich
    · exact hfactors
    · exact halternativeSparse
    · exact halternativeFactors
  · right
    omega

/-- Under source full spark and `2*K ≤ d`, the numerical dichotomy has the
paper's advertised `2*K` branch. -/
theorem twoK_le_effective_sparsity_or_alternative_spark_le
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1) (h2K_le_d : 2 * K ≤ d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 * K ≤ min K' M' ∨
      spark alternative ≤ min (2 * min K' M') M' := by
  rcases spark_cutoff_le_effective_sparsity_or_alternative_spark_le
      matrix z f alternative alternativeCode hKpos hK_le_M hwidth hrich
        hfactors halternativeSparse halternativeFactors with hsource | halt
  · left
    simpa [hspark, Nat.min_eq_left h2K_le_d] using hsource
  · exact Or.inr halt

/-- In the paper's intended range `2*K ≤ d`, the effective lower bound
implies the advertised declared-sparsity conclusion and more. -/
theorem twoK_le_alternative_sparsity_of_strict_width_and_injective_alternative
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hspark : spark matrix = d + 1) (h2K_le_d : 2 * K ≤ d)
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (halternativeInjective : KSparseInjective alternative (min K' M'))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 * K ≤ K' := by
  calc
    2 * K = min (2 * K) d := (Nat.min_eq_left h2K_le_d).symm
    _ ≤ min K' M' :=
      effective_sparsity_ge_dimension_cutoff_of_strict_width
        matrix z f alternative alternativeCode hspark hKpos hK_le_M
          hwidth halternativeInjective hrich hfactors halternativeSparse
          halternativeFactors
    _ ≤ K' := Nat.min_le_left K' M'

end PKG26AtomicFeatures
