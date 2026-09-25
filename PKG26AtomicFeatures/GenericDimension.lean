import PKG26AtomicFeatures.ConcentrationProfile
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Generic projective-dimension obstructions for sparse factorizations

This module proves projective incidence bounds for source atom families under
ambient Lebesgue measure. `SphericalGenericDimension.lean` treats unit-column
families using their intrinsic surface measure.

The basic incidence chart gives each alternative atom `n = d - 1` projective
degrees of freedom and charges one scalar parameter for every coefficient slot.
The resulting null-set theorem holds simultaneously over all finite support
patterns.  Its weighted form charges actual support sizes, its rank-capped
form removes coefficient redundancy inside dependent supports, and its
hereditary form applies the same obstruction to every source subfamily.
Consequently an exact common factorization satisfies both the global parameter
count and the stronger subsetwise neighborhood expansion.  No spark or
general-position assumption on the alternative dictionary is needed, and any
joint source law absolutely continuous with respect to Lebesgue measure
suffices; independence
and identical distribution are not required.
-/

open scoped BigOperators
open MeasureTheory Set

namespace PKG26AtomicFeatures

abbrev GenericAtomParameters (n M' : ℕ) := Fin M' → Fin n → ℝ
abbrev GenericCoefficientParameters (M s : ℕ) := Fin M → Fin s → ℝ
abbrev GenericIncidenceParameters (n M M' s : ℕ) :=
  GenericAtomParameters n M' × GenericCoefficientParameters M s

def chartAtom {n M' : ℕ} (pivot : Fin M' → Fin (n + 1))
    (atoms : GenericAtomParameters n M') (j : Fin M') : Fin (n + 1) → ℝ :=
  fun r => if h : r = pivot j then 1 else
    atoms j ((finSuccAboveEquiv (pivot j)).symm ⟨r, h⟩)

def incidenceParamMap {n M M' s : ℕ}
    (pivot : Fin M' → Fin (n + 1))
    (indices : Fin M → Fin s → Fin M') :
    GenericIncidenceParameters n M M' s →
      (Fin M × Fin (n + 1)) → ℝ :=
  fun parameters ir =>
    ∑ k : Fin s, parameters.2 ir.1 k *
      chartAtom pivot parameters.1 (indices ir.1 k) ir.2

theorem incidenceParamMap_contDiff {n M M' s : ℕ}
    (pivot : Fin M' → Fin (n + 1))
    (indices : Fin M → Fin s → Fin M') :
    ContDiff ℝ 1 (incidenceParamMap pivot indices) := by
  apply contDiff_pi.mpr
  rintro ⟨i, r⟩
  simp only [incidenceParamMap]
  apply ContDiff.sum
  intro k _hk
  by_cases h : r = pivot (indices i k)
  · simp [chartAtom, h]
    fun_prop
  · simp [chartAtom, h]
    fun_prop

theorem finrank_genericIncidenceParameters (n M M' s : ℕ) :
    Module.finrank ℝ (GenericIncidenceParameters n M M' s) =
      M' * n + M * s := by
  simp [GenericIncidenceParameters, GenericAtomParameters,
    GenericCoefficientParameters, Module.finrank_pi_fintype]

theorem finrank_sourceAtomFamily (n M : ℕ) :
    Module.finrank ℝ ((Fin M × Fin (n + 1)) → ℝ) = M * (n + 1) := by
  simp

theorem incidenceParamMap_range_hausdorffMeasure_eq_zero
    {n M M' s : ℕ} (pivot : Fin M' → Fin (n + 1))
    (indices : Fin M → Fin s → Fin M')
    (hdim : M' * n + M * s < M * (n + 1)) :
    μH[Fintype.card (Fin M × Fin (n + 1))]
      (Set.range (incidenceParamMap pivot indices)) = 0 := by
  have hfinrank : Module.finrank ℝ (GenericIncidenceParameters n M M' s) <
      Fintype.card (Fin M × Fin (n + 1)) := by
    rw [finrank_genericIncidenceParameters]
    simpa using hdim
  have hfinrank' :
      (Module.finrank ℝ (GenericIncidenceParameters n M M' s) : ENNReal) <
        (Fintype.card (Fin M × Fin (n + 1)) : ENNReal) := by
    exact_mod_cast hfinrank
  have hdimH : dimH (Set.range (incidenceParamMap pivot indices)) <
      (Fintype.card (Fin M × Fin (n + 1)) : ENNReal) :=
    (incidenceParamMap_contDiff pivot indices).dimH_range_le.trans_lt hfinrank'
  exact hausdorffMeasure_of_dimH_lt
    (d := (Fintype.card (Fin M × Fin (n + 1)) : NNReal)) hdimH

def genericIncidenceBadSet (n M M' s : ℕ) :
    Set ((Fin M × Fin (n + 1)) → ℝ) :=
  ⋃ pivot : Fin M' → Fin (n + 1),
    ⋃ indices : Fin M → Fin s → Fin M',
      Set.range (incidenceParamMap pivot indices)

/-- The flattened family of source atoms obtained from an arbitrary alternative
dictionary and `s` coefficient slots per source atom. -/
def atomFamilyFromTerms {n M M' s : ℕ}
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (indices : Fin M → Fin s → Fin M')
    (coefficients : Fin M → Fin s → ℝ) :
    (Fin M × Fin (n + 1)) → ℝ :=
  fun ir => ∑ k : Fin s,
    coefficients ir.1 k * alternative ir.2 (indices ir.1 k)

theorem atomFamilyFromTerms_mem_genericIncidenceBadSet
    {n M M' s : ℕ}
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (indices : Fin M → Fin s → Fin M')
    (coefficients : Fin M → Fin s → ℝ) :
    atomFamilyFromTerms alternative indices coefficients ∈
      genericIncidenceBadSet n M M' s := by
  classical
  have hpivot_exists : ∀ j : Fin M', ∃ r : Fin (n + 1),
      alternative.col j = 0 ∨ alternative r j ≠ 0 := by
    intro j
    by_cases hzero : alternative.col j = 0
    · exact ⟨0, Or.inl hzero⟩
    · have hexists : ∃ r, alternative r j ≠ 0 := by
        by_contra hnot
        push Not at hnot
        apply hzero
        funext r
        exact hnot r
      obtain ⟨r, hr⟩ := hexists
      exact ⟨r, Or.inr hr⟩
  choose pivot hpivot using hpivot_exists
  let atoms : GenericAtomParameters n M' := fun j t =>
    if alternative.col j = 0 then 0 else
      alternative ((finSuccAboveEquiv (pivot j)) t).1 j /
        alternative (pivot j) j
  let scaledCoefficients : GenericCoefficientParameters M s := fun i k =>
    if alternative.col (indices i k) = 0 then 0 else
      coefficients i k * alternative (pivot (indices i k)) (indices i k)
  rw [genericIncidenceBadSet]
  apply Set.mem_iUnion.mpr
  refine ⟨pivot, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨indices, ?_⟩
  refine ⟨(atoms, scaledCoefficients), ?_⟩
  funext ir
  simp only [atomFamilyFromTerms, incidenceParamMap]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hzero : alternative.col (indices ir.1 k) = 0
  · have hentry : alternative ir.2 (indices ir.1 k) = 0 := by
      exact congrFun hzero ir.2
    simp [scaledCoefficients, hzero, hentry]
  · have hpivot_ne : alternative (pivot (indices ir.1 k))
        (indices ir.1 k) ≠ 0 := (hpivot (indices ir.1 k)).resolve_left hzero
    by_cases hr : ir.2 = pivot (indices ir.1 k)
    · simp [scaledCoefficients, chartAtom, hzero, hr]
    · simp [scaledCoefficients, chartAtom, atoms, hzero, hr]
      field_simp

theorem genericIncidenceBadSet_hausdorffMeasure_eq_zero
    {n M M' s : ℕ} (hdim : M' * n + M * s < M * (n + 1)) :
    μH[Fintype.card (Fin M × Fin (n + 1))]
      (genericIncidenceBadSet n M M' s) = 0 := by
  rw [genericIncidenceBadSet]
  apply measure_iUnion_null
  intro pivot
  apply measure_iUnion_null
  intro indices
  exact incidenceParamMap_range_hausdorffMeasure_eq_zero pivot indices hdim

/-- A source atom family admits an `s`-term representation by `M'` alternative
atoms when one common alternative matrix and `s` (possibly repeated or
zero-weighted) slots represent every source atom. -/
def STermRepresentable {n M : ℕ} (M' s : ℕ)
    (source : (Fin M × Fin (n + 1)) → ℝ) : Prop :=
  ∃ alternative : Matrix (Fin (n + 1)) (Fin M') ℝ,
    ∃ indices : Fin M → Fin s → Fin M',
      ∃ coefficients : Fin M → Fin s → ℝ,
        source = atomFamilyFromTerms alternative indices coefficients

/-- A source family is projective-dimension generic when every finite
term representation obeys the corresponding parameter-count inequality. -/
def ProjectiveDimensionGeneric {n M : ℕ}
    (source : (Fin M × Fin (n + 1)) → ℝ) : Prop :=
  ∀ M' s, STermRepresentable M' s source →
    M * (n + 1) ≤ M' * n + M * s

/-- The columns of a matrix, flattened as a finite family of ambient vectors.
This is only a coordinate reindexing; it carries no mathematical assumption. -/
def matrixAtomFamily {n : ℕ} {atom : Type*}
    (matrix : Matrix (Fin (n + 1)) atom ℝ) :
    (atom × Fin (n + 1)) → ℝ :=
  fun ir => matrix ir.2 ir.1

theorem sTermRepresentable_subset_genericIncidenceBadSet
    {n M M' s : ℕ} :
    {source | STermRepresentable M' s source} ⊆
      genericIncidenceBadSet n M M' s := by
  rintro source ⟨alternative, indices, coefficients, rfl⟩
  exact atomFamilyFromTerms_mem_genericIncidenceBadSet
    alternative indices coefficients

/-- If the projective dictionary parameters plus coefficients have dimension
strictly below the source-family dimension, all `s`-term-representable source
families form a Hausdorff-null set. -/
theorem sTermRepresentable_hausdorffMeasure_eq_zero
    {n M M' s : ℕ} (hdim : M' * n + M * s < M * (n + 1)) :
    (μH[Fintype.card (Fin M × Fin (n + 1))] :
      Measure ((Fin M × Fin (n + 1)) → ℝ))
      {source | STermRepresentable M' s source} = 0 := by
  exact measure_mono_null sTermRepresentable_subset_genericIncidenceBadSet
    (genericIncidenceBadSet_hausdorffMeasure_eq_zero hdim)

/-- Lebesgue-almost every source atom family satisfies the exact integral
parameter-count obstruction simultaneously for every alternative width and
every number of coefficient slots. -/
theorem ae_forall_sTermRepresentable_dimension_bound (n M : ℕ) :
    ∀ᵐ source : (Fin M × Fin (n + 1)) → ℝ ∂volume,
      ProjectiveDimensionGeneric source := by
  simp only [ProjectiveDimensionGeneric]
  rw [ae_all_iff]
  intro M'
  rw [ae_all_iff]
  intro s
  by_cases hdim : M' * n + M * s < M * (n + 1)
  · rw [← hausdorffMeasure_pi_real]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (sTermRepresentable_hausdorffMeasure_eq_zero hdim)] with source hsource
    intro hrepresentable
    exact False.elim (hsource hrepresentable)
  · exact Filter.Eventually.of_forall fun _source _hrepresentable =>
      Nat.le_of_not_gt hdim

/-- The same full-measure statement holds for every joint source law that is
absolutely continuous with respect to Lebesgue measure; no independence or
identical-distribution premise is needed. -/
theorem ae_projectiveDimensionGeneric_of_absolutelyContinuous
    {n M : ℕ}
    (distribution : Measure ((Fin M × Fin (n + 1)) → ℝ))
    (hdistribution : distribution ≪ volume) :
    ∀ᵐ source ∂distribution, ProjectiveDimensionGeneric source := by
  exact hdistribution.ae_le
    (ae_forall_sTermRepresentable_dimension_bound n M)

/-- The dimension obstruction in its sharp projective-codimension form.  The
right side counts `n = d-1` free parameters per projective alternative atom;
the left side is the source dimension remaining after `s` coefficients per
source atom have been paid for. -/
theorem projective_codimension_bound_of_sTermRepresentable
    {n M M' s : ℕ} (hs : s ≤ n + 1)
    {source : (Fin M × Fin (n + 1)) → ℝ}
    (hgeneric : ProjectiveDimensionGeneric source)
    (hrepresentable : STermRepresentable M' s source) :
    M * (n + 1 - s) ≤ M' * n := by
  have hdim := hgeneric M' s hrepresentable
  have hsplit : n + 1 = (n + 1 - s) + s :=
    (Nat.sub_add_cancel hs).symm
  rw [hsplit, Nat.mul_add] at hdim
  omega

/-- Integer-sharp version of the source paper's displayed fractional bound.
It rounds up automatically, so it is at least as strong as the real-valued
inequality `M' ≥ M (d-s)/(d-1)`. -/
theorem ceil_projective_codimension_bound_of_sTermRepresentable
    {n M M' s : ℕ} (hn : 0 < n) (hs : s ≤ n + 1)
    {source : (Fin M × Fin (n + 1)) → ℝ}
    (hgeneric : ProjectiveDimensionGeneric source)
    (hrepresentable : STermRepresentable M' s source) :
    (M * (n + 1 - s)) ⌈/⌉ n ≤ M' := by
  rw [ceilDiv_le_iff_le_mul hn]
  rw [Nat.mul_comm n M']
  exact projective_codimension_bound_of_sTermRepresentable hs hgeneric
    hrepresentable

/-- Exact integer lower bound on uniform representation sparsity when an
alternative dictionary is no wider than the source dictionary.  In paper
notation the numerator is `M + (M - M') * (d - 1)`, so this is precisely
`s ≥ ⌈1 + (1 - M' / M) * (d - 1)⌉`. -/
theorem ceil_sparsity_lower_bound_of_sTermRepresentable
    {n M M' s : ℕ} (hM : 0 < M) (hwidth : M' ≤ M)
    {source : (Fin M × Fin (n + 1)) → ℝ}
    (hgeneric : ProjectiveDimensionGeneric source)
    (hrepresentable : STermRepresentable M' s source) :
    (M + (M - M') * n) ⌈/⌉ M ≤ s := by
  rw [ceilDiv_le_iff_le_mul hM]
  have hdim := hgeneric M' s hrepresentable
  have hsplit : M * n = M' * n + (M - M') * n := by
    conv_lhs => rw [show M = M' + (M - M') by omega]
    exact Nat.add_mul M' (M - M') n
  rw [Nat.mul_add, hsplit] at hdim
  omega

/-- In ambient dimension at least two, a strict generic width reduction
requires at least two terms per source atom. -/
theorem two_le_of_strict_width_and_sTermRepresentable
    {n M M' s : ℕ} (hn : 0 < n) (hwidth : M' < M)
    {source : (Fin M × Fin (n + 1)) → ℝ}
    (hgeneric : ProjectiveDimensionGeneric source)
    (hrepresentable : STermRepresentable M' s source) :
    2 ≤ s := by
  have hdim := hgeneric M' s hrepresentable
  by_contra hs
  have hs' : s ≤ 1 := by omega
  have hmul : M' * n < M * n :=
    Nat.mul_lt_mul_of_pos_right hwidth hn
  have hcoeff : M * s ≤ M := by
    simpa using Nat.mul_le_mul_left M hs'
  rw [Nat.mul_add] at hdim
  omega

/-- A strict width reduction bounds the ambient projective dimension in terms
of the coefficient budget per source atom and the number of removed atoms. In
paper notation, `(M - M') * (d - 1) ≤ M * (s - 1)`. -/
theorem projective_ambient_dimension_bound_of_sTermRepresentable
    {n M M' s : ℕ} (hwidth : M' < M)
    {source : (Fin M × Fin (n + 1)) → ℝ}
    (hgeneric : ProjectiveDimensionGeneric source)
    (hrepresentable : STermRepresentable M' s source) :
    n ≤ (M * (s - 1)) / (M - M') := by
  have hden : 0 < M - M' := Nat.sub_pos_of_lt hwidth
  rw [Nat.le_div_iff_mul_le hden]
  have hdim := hgeneric M' s hrepresentable
  have hsource_split : M * (n + 1) = M * n + M := by
    simp [Nat.mul_add]
  have hwidth_split : M * n = M' * n + (M - M') * n := by
    calc
      M * n = (M' + (M - M')) * n := by
        exact congrArg (fun width => width * n)
          (Nat.add_sub_of_le hwidth.le).symm
      _ = M' * n + (M - M') * n := Nat.add_mul M' (M - M') n
  have hsource_rearranged : M * (n + 1) =
      M' * n + ((M - M') * n + M) := by
    rw [hsource_split, hwidth_split]
    omega
  rw [hsource_rearranged] at hdim
  have hremainder : (M - M') * n + M ≤ M * s :=
    Nat.le_of_add_le_add_left hdim
  have hspos : 0 < s := by
    by_contra hs
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    simp only [Nat.mul_zero] at hremainder
    omega
  have hcoefficient_split : M * s = M + M * (s - 1) := by
    calc
      M * s = M * (1 + (s - 1)) := by
        rw [Nat.add_sub_of_le hspos]
      _ = M + M * (s - 1) := by simp [Nat.mul_add]
  rw [hcoefficient_split] at hremainder
  have hproduct : (M - M') * n ≤ M * (s - 1) := by
    have hadd : M + (M - M') * n ≤ M + M * (s - 1) := by
      simpa [Nat.add_comm] using hremainder
    exact Nat.le_of_add_le_add_left hadd
  simpa [Nat.mul_comm] using hproduct

/-- A coefficient vector with support of size at most `s` can be written with
exactly `s` ordered slots, padding by zero coefficients after enlarging its
support. -/
theorem exists_term_enumeration_of_support_card_le
    {d M' s : ℕ} (alternative : Matrix (Fin d) (Fin M') ℝ)
    (code : FeatureVector M')
    (hcard : (nonzeroSupport code).card ≤ s) (hs : s ≤ M') :
    ∃ indices : Fin s → Fin M', ∃ coefficients : Fin s → ℝ,
      ∀ r, alternative.mulVec code r =
        ∑ k, coefficients k * alternative r (indices k) := by
  classical
  obtain ⟨support, hsupport, _hsupport_univ, hsupport_card⟩ :=
    Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (nonzeroSupport code)) hcard (by simpa using hs)
  let enumeration : Fin s ≃ {j // j ∈ support} :=
    (Finset.equivFinOfCardEq hsupport_card).symm
  refine ⟨fun k => (enumeration k).1, fun k => code (enumeration k).1, ?_⟩
  intro r
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ j : Fin M', alternative r j * code j) =
        ∑ j ∈ support, alternative r j * code j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ support)
      intro j _hj_univ hj_support
      have hj_nonzeroSupport : j ∉ nonzeroSupport code := fun hj =>
        hj_support (hsupport hj)
      have hj_zero : code j = 0 := by
        simpa [mem_nonzeroSupport_iff] using hj_nonzeroSupport
      simp [hj_zero]
    _ = ∑ j : {j // j ∈ support}, alternative r j.1 * code j.1 := by
      exact Finset.sum_subtype support (fun _ => Iff.rfl)
        (fun j => alternative r j * code j)
    _ = ∑ k : Fin s,
        code (enumeration k).1 * alternative r (enumeration k).1 := by
      symm
      apply Fintype.sum_equiv enumeration
      intro k
      exact mul_comm _ _

/-- A representation can be compressed to a basis of the span generated by
its nonzero support.  The number of slots is the exact rank of that span, and
every retained alternative atom comes from the original support. -/
theorem exists_rank_term_representation
    {d M' : ℕ} (alternative : Matrix (Fin d) (Fin M') ℝ)
    (code : FeatureVector M') :
    ∃ indices : Fin (Module.finrank ℝ
        (columnSpan alternative (nonzeroSupport code))) → Fin M',
      ∃ coefficients : Fin (Module.finrank ℝ
        (columnSpan alternative (nonzeroSupport code))) → ℝ,
        (∀ k, indices k ∈ nonzeroSupport code) ∧
        ∀ r, alternative.mulVec code r =
          ∑ k, coefficients k * alternative r (indices k) := by
  classical
  let supportVectors : Set (RepresentationVector d) :=
    Set.range (selectedColumns alternative (nonzeroSupport code))
  obtain ⟨basisVectors, hbasis_mem, hbasis_span,
      _hbasis_independent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ supportVectors
  have hmulVec_mem : alternative.mulVec code ∈
      Submodule.span ℝ (Set.range basisVectors) := by
    rw [hbasis_span]
    exact mulVec_mem_columnSpan_nonzeroSupport alternative code
  rw [Submodule.mem_span_range_iff_exists_fun] at hmulVec_mem
  obtain ⟨coefficients, hcoefficients⟩ := hmulVec_mem
  have hindex_exists : ∀ k, ∃ j : Fin M',
      j ∈ nonzeroSupport code ∧ basisVectors k = alternative.col j := by
    intro k
    obtain ⟨j, hj⟩ := hbasis_mem k
    refine ⟨j.1, j.2, ?_⟩
    simpa [selectedColumns] using hj.symm
  choose indices hindices_mem hbasis_eq using hindex_exists
  refine ⟨indices, coefficients, hindices_mem, ?_⟩
  intro r
  have hcoefficients_r := congrFun hcoefficients r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoefficients_r
  rw [← hcoefficients_r]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hbasis_eq k]
  rfl

/-- A common matrix factorization whose per-atom coefficient vectors have
support at most `s` induces an `s`-term representation. -/
theorem sTermRepresentable_of_sparse_atom_factorization
    {n M M' s : ℕ} (hs : s ≤ M')
    (sourceMatrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : Fin M → FeatureVector M')
    (hsparse : ∀ i, (nonzeroSupport (code i)).card ≤ s)
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i)) :
    STermRepresentable M' s (matrixAtomFamily sourceMatrix) := by
  classical
  have hterms : ∀ i : Fin M,
      ∃ indices : Fin s → Fin M', ∃ coefficients : Fin s → ℝ,
        ∀ r, alternative.mulVec (code i) r =
          ∑ k, coefficients k * alternative r (indices k) := by
    intro i
    exact exists_term_enumeration_of_support_card_le alternative (code i)
      (hsparse i) hs
  choose indices coefficients hrepresentation using hterms
  refine ⟨alternative, indices, coefficients, ?_⟩
  funext ir
  rw [atomFamilyFromTerms]
  exact congrFun (hfactors ir.1) ir.2 |>.trans (hrepresentation ir.1 ir.2)

/-- The minimal linear-algebraic input for the generic count: if every source
atom has a coefficient vector supported on at most `s` common alternative
atoms, genericity alone forces the exact parameter-dimension inequality. -/
theorem generic_dimension_bound_of_sparse_atom_factorization
    {n M M' s : ℕ} (hs : s ≤ M')
    (sourceMatrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : Fin M → FeatureVector M')
    (hgeneric : ProjectiveDimensionGeneric (matrixAtomFamily sourceMatrix))
    (hsparse : ∀ i, (nonzeroSupport (code i)).card ≤ s)
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i)) :
    M * (n + 1) ≤ M' * n + M * s := by
  apply hgeneric M' s
  exact sTermRepresentable_of_sparse_atom_factorization hs sourceMatrix
    alternative code hsparse hfactors

/-- Membership in a selected column span is witnessed by a coefficient vector
whose nonzero support is contained in that selection. -/
theorem exists_sparse_code_of_mem_columnSpan
    {d M' : ℕ} (alternative : Matrix (Fin d) (Fin M') ℝ)
    (support : Finset (Fin M')) (vector : RepresentationVector d)
    (hmem : vector ∈ columnSpan alternative support) :
    ∃ code : FeatureVector M',
      (nonzeroSupport code).card ≤ support.card ∧
        alternative.mulVec code = vector := by
  classical
  rw [columnSpan, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  let code : FeatureVector M' := fun j =>
    if h : j ∈ support then c ⟨j, h⟩ else 0
  refine ⟨code, ?_, ?_⟩
  · apply Finset.card_le_card
    intro j hj
    rw [mem_nonzeroSupport_iff] at hj
    by_contra hnot
    exact hj (by simp [code, hnot])
  · funext r
    have hc_r := congrFun hc r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      selectedColumns] at hc_r
    rw [Matrix.mulVec, dotProduct]
    calc
      (∑ j : Fin M', alternative r j * code j) =
          ∑ j ∈ support, alternative r j * code j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ support)
        intro j _hj_univ hj_support
        simp [code, hj_support]
      _ = ∑ j : {j // j ∈ support}, alternative r j.1 * c j := by
        rw [Finset.sum_subtype support (fun _ => Iff.rfl)
          (fun j => alternative r j * code j)]
        apply Finset.sum_congr rfl
        intro j _hj
        simp [code, j.2]
      _ = vector r := by
        rw [← hc_r]
        apply Finset.sum_congr rfl
        intro j _hj
        exact mul_comm _ _

/-- Positive source richness and the two factorizations imply the exact
atomwise linear-algebraic premise needed by the dimension theorem: every
source column itself has a common alternative-dictionary code of effective
sparsity `min K' M'`. No spark or genericity premise is used in this bridge. -/
theorem exists_sparse_source_atom_factorization_of_kRich_and_factorizations
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ code : Fin M → FeatureVector M',
      (∀ i, (nonzeroSupport (code i)).card ≤ min K' M') ∧
        ∀ i, matrix.col i = alternative.mulVec (code i) := by
  classical
  have hsupport_exists : ∀ i : Fin M,
      ∃ support : Finset (Fin M'),
        support.card ≤ min K' M' ∧
          matrix.col i ∈ columnSpan alternative support := by
    intro i
    have hsingleton_card : ({i} : Finset (Fin M)).card ≤ K := by
      simp
      omega
    obtain ⟨sourceSupport, hsingleton_subset, _hsource_univ,
        hsource_card⟩ :=
      Finset.exists_subsuperset_card_eq
        (Finset.subset_univ ({i} : Finset (Fin M)))
        hsingleton_card (by simpa using hK_le_M)
    obtain ⟨alternativeSupport, hspan⟩ :=
      AppendixHall.exists_sparse_alternative_subspace_containing_coordinate_image
        matrix z f alternative alternativeCode hrich hfactors
        (kSparse_min_columnCount alternativeCode halternativeSparse)
        halternativeFactors sourceSupport hsource_card
    have hcolumnSpan : columnSpan matrix sourceSupport ≤
        columnSpan alternative alternativeSupport.1 := by
      rw [← map_mulVecLin_coordinateSpan_eq_columnSpan]
      exact hspan
    refine ⟨alternativeSupport.1, alternativeSupport.2, hcolumnSpan ?_⟩
    apply Submodule.subset_span
    exact ⟨⟨i, hsingleton_subset (Finset.mem_singleton_self i)⟩, rfl⟩
  choose supports hsupports_card hatom using hsupport_exists
  have hcode_exists : ∀ i : Fin M,
      ∃ code : FeatureVector M',
        (nonzeroSupport code).card ≤ min K' M' ∧
          alternative.mulVec code = matrix.col i := by
    intro i
    obtain ⟨code, hcode_card, hcode⟩ :=
      exists_sparse_code_of_mem_columnSpan alternative (supports i)
        (matrix.col i) (hatom i)
    exact ⟨code, hcode_card.trans (hsupports_card i), hcode⟩
  choose code hcode_card hcode using hcode_exists
  exact ⟨code, hcode_card, fun i => (hcode i).symm⟩

/-- Positive source richness and the two source-model factorizations make the
finite family of source atoms term-representable at the effective alternative
sparsity `min K' M'`. No spark or general-position premise is used here. -/
theorem sTermRepresentable_of_kRich_and_factorizations
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    STermRepresentable M' (min K' M')
      (matrixAtomFamily matrix) := by
  obtain ⟨code, hcode_card, hcode⟩ :=
    exists_sparse_source_atom_factorization_of_kRich_and_factorizations
      matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
        halternativeSparse halternativeFactors
  apply sTermRepresentable_of_sparse_atom_factorization
    (Nat.min_le_right K' M') matrix alternative code hcode_card
  exact hcode

/-- Generic source atoms plus the paper's richness/factorization premises imply
the exact integral dimension count. This is the global generic theorem; it
needs neither full spark nor any condition on the alternative dictionary. -/
theorem generic_dimension_bound_of_kRich_and_factorizations
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : ProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    M * (n + 1) ≤ M' * n + M * min K' M' := by
  apply hgeneric M' (min K' M')
  exact sTermRepresentable_of_kRich_and_factorizations
    matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
      halternativeSparse halternativeFactors

/-- Exact integer sparsity lower bound under the source model.  It is stated
for effective sparsity, so it remains informative even when the declared
`K'` exceeds the number of alternative atoms. -/
theorem ceil_generic_effective_sparsity_lower_bound_of_kRich_and_factorizations
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : ProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' ≤ M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    (M + (M - M') * n) ⌈/⌉ M ≤ min K' M' := by
  apply ceil_sparsity_lower_bound_of_sTermRepresentable
    (hKpos.trans_le hK_le_M) hwidth hgeneric
  exact sTermRepresentable_of_kRich_and_factorizations
    matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
      halternativeSparse halternativeFactors

/-- A strict width reduction of a generic source dictionary in dimension at
least two forces declared alternative sparsity at least two. -/
theorem two_le_generic_sparsity_of_kRich_and_factorizations
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : ProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hn : 0 < n) (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    2 ≤ K' := by
  have heffective : 2 ≤ min K' M' := by
    apply two_le_of_strict_width_and_sTermRepresentable hn hwidth hgeneric
    exact sTermRepresentable_of_kRich_and_factorizations
      matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
        halternativeSparse halternativeFactors
  exact heffective.trans (Nat.min_le_left K' M')

/-- Source-model form of the exact ambient-dimension ceiling. A fixed strict
width reduction and effective alternative sparsity can represent a generic
source only below this dimension. -/
theorem generic_ambient_dimension_bound_of_kRich_and_factorizations
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : ProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hKpos : 0 < K) (hK_le_M : K ≤ M) (hwidth : M' < M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    n ≤ (M * (min K' M' - 1)) / (M - M') := by
  apply projective_ambient_dimension_bound_of_sTermRepresentable
    hwidth hgeneric
  exact sTermRepresentable_of_kRich_and_factorizations
    matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
      halternativeSparse halternativeFactors

/-- Under the natural effective-sparsity ceiling, the generic dimension count
is equivalently a projective-codimension lower bound on alternative width. -/
theorem generic_projective_codimension_bound_of_kRich_and_factorizations
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : ProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (heffective : min K' M' ≤ n + 1)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    M * (n + 1 - min K' M') ≤ M' * n := by
  apply projective_codimension_bound_of_sTermRepresentable heffective hgeneric
  exact sTermRepresentable_of_kRich_and_factorizations
    matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
      halternativeSparse halternativeFactors

/-- Paper-notation specialization when the declared alternative sparsity is no
larger than both its column count and the ambient dimension. -/
theorem generic_projective_codimension_bound_of_kRich_and_factorizations_of_le
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : ProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hK'_le_M' : K' ≤ M') (hK'_le_d : K' ≤ n + 1)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    M * (n + 1 - K') ≤ M' * n := by
  simpa [Nat.min_eq_left hK'_le_M'] using
    generic_projective_codimension_bound_of_kRich_and_factorizations
      matrix z f alternative alternativeCode hgeneric hKpos hK_le_M
        (by simpa [Nat.min_eq_left hK'_le_M'] using hK'_le_d)
        hrich hfactors halternativeSparse halternativeFactors

/-- Integer-sharp form of the generic width lower bound in the paper's
notation. -/
theorem ceil_generic_width_bound_of_kRich_and_factorizations
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : ProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hn : 0 < n) (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hK'_le_M' : K' ≤ M') (hK'_le_d : K' ≤ n + 1)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    (M * (n + 1 - K')) ⌈/⌉ n ≤ M' := by
  rw [ceilDiv_le_iff_le_mul hn, Nat.mul_comm n M']
  exact
    generic_projective_codimension_bound_of_kRich_and_factorizations_of_le
      matrix z f alternative alternativeCode hgeneric hKpos hK_le_M
        hK'_le_M' hK'_le_d hrich hfactors halternativeSparse
        halternativeFactors

/-! ## Weighted incidence dimension -/

/-- Coefficient parameters when source atom `i` is assigned its own number of
ordered representation slots. -/
abbrev GenericVariableCoefficientParameters {atom : Type*}
    (slotCount : atom → ℕ) :=
  (Σ i, Fin (slotCount i)) → ℝ

abbrev GenericVariableIncidenceParameters (n M' : ℕ) {atom : Type*}
    (slotCount : atom → ℕ) :=
  GenericAtomParameters n M' ×
    GenericVariableCoefficientParameters slotCount

def variableIncidenceParamMap {n M' : ℕ} {atom : Type*} [Fintype atom]
    {slotCount : atom → ℕ}
    (pivot : Fin M' → Fin (n + 1))
    (indices : ∀ i, Fin (slotCount i) → Fin M') :
    GenericVariableIncidenceParameters n M' slotCount →
      (atom × Fin (n + 1)) → ℝ :=
  fun parameters ir =>
    ∑ k : Fin (slotCount ir.1), parameters.2 ⟨ir.1, k⟩ *
      chartAtom pivot parameters.1 (indices ir.1 k) ir.2

theorem variableIncidenceParamMap_contDiff
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    {slotCount : atom → ℕ}
    (pivot : Fin M' → Fin (n + 1))
    (indices : ∀ i, Fin (slotCount i) → Fin M') :
    ContDiff ℝ 1 (variableIncidenceParamMap pivot indices) := by
  apply contDiff_pi.mpr
  rintro ⟨i, r⟩
  simp only [variableIncidenceParamMap]
  apply ContDiff.sum
  intro k _hk
  by_cases h : r = pivot (indices i k)
  · simp [chartAtom, h]
    fun_prop
  · simp [chartAtom, h]
    fun_prop

theorem finrank_genericVariableIncidenceParameters
    (n M' : ℕ) {atom : Type*} [Fintype atom]
    (slotCount : atom → ℕ) :
    Module.finrank ℝ
      (GenericVariableIncidenceParameters n M' slotCount) =
        M' * n + ∑ i, slotCount i := by
  simp [GenericVariableIncidenceParameters, GenericAtomParameters,
    GenericVariableCoefficientParameters, Module.finrank_pi_fintype]

theorem variableIncidenceParamMap_range_hausdorffMeasure_eq_zero
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    {slotCount : atom → ℕ}
    (pivot : Fin M' → Fin (n + 1))
    (indices : ∀ i, Fin (slotCount i) → Fin M')
    (hdim : M' * n + ∑ i, slotCount i <
      Fintype.card atom * (n + 1)) :
    μH[Fintype.card (atom × Fin (n + 1))]
      (Set.range (variableIncidenceParamMap pivot indices)) = 0 := by
  have hfinrank :
      Module.finrank ℝ
          (GenericVariableIncidenceParameters n M' slotCount) <
        Fintype.card (atom × Fin (n + 1)) := by
    rw [finrank_genericVariableIncidenceParameters]
    simpa using hdim
  have hfinrank' :
      (Module.finrank ℝ
        (GenericVariableIncidenceParameters n M' slotCount) : ENNReal) <
        (Fintype.card (atom × Fin (n + 1)) : ENNReal) := by
    exact_mod_cast hfinrank
  have hdimH : dimH (Set.range (variableIncidenceParamMap pivot indices)) <
      (Fintype.card (atom × Fin (n + 1)) : ENNReal) :=
    (variableIncidenceParamMap_contDiff pivot indices).dimH_range_le.trans_lt
      hfinrank'
  exact hausdorffMeasure_of_dimH_lt
    (d := (Fintype.card (atom × Fin (n + 1)) : NNReal)) hdimH

def genericVariableIncidenceBadSet
    (n M' : ℕ) {atom : Type*} [Fintype atom]
    (slotCount : atom → ℕ) :
    Set ((atom × Fin (n + 1)) → ℝ) :=
  ⋃ pivot : Fin M' → Fin (n + 1),
    ⋃ indices : ∀ i, Fin (slotCount i) → Fin M',
      Set.range (variableIncidenceParamMap pivot indices)

def atomFamilyFromVariableTerms
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    {slotCount : atom → ℕ}
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (indices : ∀ i, Fin (slotCount i) → Fin M')
    (coefficients : GenericVariableCoefficientParameters slotCount) :
    (atom × Fin (n + 1)) → ℝ :=
  fun ir => ∑ k : Fin (slotCount ir.1),
    coefficients ⟨ir.1, k⟩ * alternative ir.2 (indices ir.1 k)

theorem atomFamilyFromVariableTerms_mem_genericVariableIncidenceBadSet
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    {slotCount : atom → ℕ}
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (indices : ∀ i, Fin (slotCount i) → Fin M')
    (coefficients : GenericVariableCoefficientParameters slotCount) :
    atomFamilyFromVariableTerms alternative indices coefficients ∈
      genericVariableIncidenceBadSet n M' slotCount := by
  classical
  have hpivot_exists : ∀ j : Fin M', ∃ r : Fin (n + 1),
      alternative.col j = 0 ∨ alternative r j ≠ 0 := by
    intro j
    by_cases hzero : alternative.col j = 0
    · exact ⟨0, Or.inl hzero⟩
    · have hexists : ∃ r, alternative r j ≠ 0 := by
        by_contra hnot
        push Not at hnot
        apply hzero
        funext r
        exact hnot r
      obtain ⟨r, hr⟩ := hexists
      exact ⟨r, Or.inr hr⟩
  choose pivot hpivot using hpivot_exists
  let atoms : GenericAtomParameters n M' := fun j t =>
    if alternative.col j = 0 then 0 else
      alternative ((finSuccAboveEquiv (pivot j)) t).1 j /
        alternative (pivot j) j
  let scaledCoefficients : GenericVariableCoefficientParameters slotCount :=
    fun ik =>
      if alternative.col (indices ik.1 ik.2) = 0 then 0 else
        coefficients ik *
          alternative (pivot (indices ik.1 ik.2)) (indices ik.1 ik.2)
  rw [genericVariableIncidenceBadSet]
  apply Set.mem_iUnion.mpr
  refine ⟨pivot, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨indices, ?_⟩
  refine ⟨(atoms, scaledCoefficients), ?_⟩
  funext ir
  simp only [atomFamilyFromVariableTerms, variableIncidenceParamMap]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hzero : alternative.col (indices ir.1 k) = 0
  · have hentry : alternative ir.2 (indices ir.1 k) = 0 := by
      exact congrFun hzero ir.2
    simp [scaledCoefficients, hzero, hentry]
  · have hpivot_ne : alternative (pivot (indices ir.1 k))
        (indices ir.1 k) ≠ 0 := (hpivot (indices ir.1 k)).resolve_left hzero
    by_cases hr : ir.2 = pivot (indices ir.1 k)
    · simp [scaledCoefficients, chartAtom, hzero, hr]
    · simp [scaledCoefficients, chartAtom, atoms, hzero, hr]
      field_simp

theorem genericVariableIncidenceBadSet_hausdorffMeasure_eq_zero
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    {slotCount : atom → ℕ}
    (hdim : M' * n + ∑ i, slotCount i <
      Fintype.card atom * (n + 1)) :
    μH[Fintype.card (atom × Fin (n + 1))]
      (genericVariableIncidenceBadSet n M' slotCount) = 0 := by
  rw [genericVariableIncidenceBadSet]
  apply measure_iUnion_null
  intro pivot
  apply measure_iUnion_null
  intro indices
  exact variableIncidenceParamMap_range_hausdorffMeasure_eq_zero
    pivot indices hdim

/-- A term representation with a source-specific number of coefficient slots.
The total coefficient dimension is exactly `∑ i, slotCount i`. -/
def VariableTermRepresentable {n : ℕ} {atom : Type*} [Fintype atom]
    (M' : ℕ) (slotCount : atom → ℕ)
    (source : (atom × Fin (n + 1)) → ℝ) : Prop :=
  ∃ alternative : Matrix (Fin (n + 1)) (Fin M') ℝ,
    ∃ indices : ∀ i, Fin (slotCount i) → Fin M',
      ∃ coefficients : GenericVariableCoefficientParameters slotCount,
        source = atomFamilyFromVariableTerms alternative indices coefficients

/-- Weighted projective-dimension genericity charges each source atom only for
the coefficient slots it actually uses. -/
def WeightedProjectiveDimensionGeneric
    {n : ℕ} {atom : Type*} [Fintype atom]
    (source : (atom × Fin (n + 1)) → ℝ) : Prop :=
  ∀ M' slotCount, VariableTermRepresentable M' slotCount source →
    Fintype.card atom * (n + 1) ≤ M' * n + ∑ i, slotCount i

theorem variableTermRepresentable_subset_genericVariableIncidenceBadSet
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    {slotCount : atom → ℕ} :
    {source | VariableTermRepresentable M' slotCount source} ⊆
      genericVariableIncidenceBadSet n M' slotCount := by
  rintro source ⟨alternative, indices, coefficients, rfl⟩
  exact atomFamilyFromVariableTerms_mem_genericVariableIncidenceBadSet
    alternative indices coefficients

theorem variableTermRepresentable_hausdorffMeasure_eq_zero
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    {slotCount : atom → ℕ}
    (hdim : M' * n + ∑ i, slotCount i <
      Fintype.card atom * (n + 1)) :
    (μH[Fintype.card (atom × Fin (n + 1))] :
      Measure ((atom × Fin (n + 1)) → ℝ))
      {source | VariableTermRepresentable M' slotCount source} = 0 := by
  exact measure_mono_null
    variableTermRepresentable_subset_genericVariableIncidenceBadSet
    (genericVariableIncidenceBadSet_hausdorffMeasure_eq_zero hdim)

/-- Weighted projective-dimension genericity is a full-Lebesgue-measure
property, simultaneously over every width and every finite slot profile. -/
theorem ae_weightedProjectiveDimensionGeneric
    (n : ℕ) (atom : Type*) [Fintype atom] :
    ∀ᵐ source : (atom × Fin (n + 1)) → ℝ ∂volume,
      WeightedProjectiveDimensionGeneric source := by
  simp only [WeightedProjectiveDimensionGeneric]
  rw [ae_all_iff]
  intro M'
  rw [ae_all_iff]
  intro slotCount
  by_cases hdim : M' * n + ∑ i, slotCount i <
      Fintype.card atom * (n + 1)
  · rw [← hausdorffMeasure_pi_real]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (variableTermRepresentable_hausdorffMeasure_eq_zero hdim)] with
        source hsource
    intro hrepresentable
    exact False.elim (hsource hrepresentable)
  · exact Filter.Eventually.of_forall fun _source _hrepresentable =>
      Nat.le_of_not_gt hdim

/-- Joint absolute continuity is a sufficient probabilistic condition for the
weighted full-measure theorem; iid sampling is not needed. -/
theorem ae_weightedProjectiveDimensionGeneric_of_absolutelyContinuous
    {n : ℕ} {atom : Type*} [Fintype atom]
    (distribution : Measure ((atom × Fin (n + 1)) → ℝ))
    (hdistribution : distribution ≪ volume) :
    ∀ᵐ source ∂distribution, WeightedProjectiveDimensionGeneric source := by
  exact hdistribution.ae_le (ae_weightedProjectiveDimensionGeneric n atom)

/-- The weighted notion implies the uniform-slot notion by taking the constant
slot profile. -/
theorem WeightedProjectiveDimensionGeneric.toProjectiveDimensionGeneric
    {n M : ℕ} {source : (Fin M × Fin (n + 1)) → ℝ}
    (hgeneric : WeightedProjectiveDimensionGeneric source) :
    ProjectiveDimensionGeneric source := by
  intro M' s hrepresentable
  obtain ⟨alternative, indices, coefficients, hsource⟩ := hrepresentable
  let slotCount : Fin M → ℕ := fun _ => s
  have hvariable : VariableTermRepresentable M' slotCount source := by
    refine ⟨alternative, indices, fun ik => coefficients ik.1 ik.2, ?_⟩
    rw [hsource]
    rfl
  have hdim := hgeneric M' slotCount hvariable
  simpa [slotCount] using hdim

/-- Every coefficient vector has an exact slot representation indexed by its
nonzero support, so there is no padding loss in the weighted theorem. -/
theorem variableTermRepresentable_of_atom_factorization
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i)) :
    VariableTermRepresentable M'
      (fun i => (nonzeroSupport (code i)).card)
      (matrixAtomFamily sourceMatrix) := by
  classical
  have hterms : ∀ i : atom,
      ∃ indices : Fin ((nonzeroSupport (code i)).card) → Fin M',
        ∃ coefficients : Fin ((nonzeroSupport (code i)).card) → ℝ,
          ∀ r, alternative.mulVec (code i) r =
            ∑ k, coefficients k * alternative r (indices k) := by
    intro i
    apply exists_term_enumeration_of_support_card_le alternative (code i)
      (le_refl _)
    simpa using Finset.card_le_univ (nonzeroSupport (code i))
  choose indices coefficients hrepresentation using hterms
  refine ⟨alternative, indices, fun ik => coefficients ik.1 ik.2, ?_⟩
  funext ir
  rw [matrixAtomFamily, atomFamilyFromVariableTerms]
  exact congrFun (hfactors ir.1) ir.2 |>.trans
    (hrepresentation ir.1 ir.2)

/-- Exact weighted dimension theorem for an arbitrary common linear
factorization. There is no sparsity, richness, spark, independence, or
general-position assumption on the alternative matrix. -/
theorem generic_weighted_dimension_bound_of_atom_factorization
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : WeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i)) :
    Fintype.card atom * (n + 1) ≤ M' * n +
      ∑ i, (nonzeroSupport (code i)).card := by
  apply hgeneric M' (fun i => (nonzeroSupport (code i)).card)
  exact variableTermRepresentable_of_atom_factorization
    sourceMatrix alternative code hfactors

/-! ## Hereditary genericity and subset expansion -/

def selectedCoordinate {atom : Type*} [DecidableEq atom]
    (vertices : Finset atom) {n : ℕ} (ir : atom × Fin (n + 1)) : Prop :=
  ir.1 ∈ vertices

def selectedCoordinateEquiv {atom : Type*} [DecidableEq atom]
    (vertices : Finset atom) (n : ℕ) :
    ({i // i ∈ vertices} × Fin (n + 1)) ≃
      {ir : atom × Fin (n + 1) // selectedCoordinate vertices ir} where
  toFun ir := ⟨(ir.1.1, ir.2), ir.1.2⟩
  invFun ir := (⟨ir.1.1, ir.2⟩, ir.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def restrictAtomFamily {atom : Type*} [DecidableEq atom]
    (vertices : Finset atom) {n : ℕ}
    (source : (atom × Fin (n + 1)) → ℝ) :
    ({i // i ∈ vertices} × Fin (n + 1)) → ℝ :=
  fun ir => source (ir.1.1, ir.2)

theorem restrictAtomFamily_quasiMeasurePreserving
    {atom : Type*} [Fintype atom] [DecidableEq atom]
    (vertices : Finset atom) (n : ℕ) :
    Measure.QuasiMeasurePreserving
      (restrictAtomFamily (n := n) vertices) volume volume := by
  classical
  let splitEquiv := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : atom × Fin (n + 1) => ℝ) (selectedCoordinate vertices)
  have hsplit := volume_preserving_piEquivPiSubtypeProd
    (fun _ : atom × Fin (n + 1) => ℝ) (selectedCoordinate vertices)
  have hfirst : Measure.QuasiMeasurePreserving
      (fun source => (splitEquiv source).1) volume volume :=
    Measure.quasiMeasurePreserving_fst.comp hsplit.quasiMeasurePreserving
  let coordinateEquiv := selectedCoordinateEquiv vertices n
  have hreindex := volume_measurePreserving_piCongrLeft
    (fun _ : {i // i ∈ vertices} × Fin (n + 1) => ℝ)
    coordinateEquiv.symm
  have hcomposition := hreindex.quasiMeasurePreserving.comp hfirst
  exact hcomposition

/-- Hereditary weighted genericity requires the weighted parameter count on
every source subfamily, not only on the full atom set. -/
def HereditarilyWeightedProjectiveDimensionGeneric
    {n : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (source : (atom × Fin (n + 1)) → ℝ) : Prop :=
  ∀ vertices : Finset atom,
    WeightedProjectiveDimensionGeneric (restrictAtomFamily vertices source)

/-- Hereditary weighted genericity is itself full measure. This is stronger
than applying a dimension count only to the full source dictionary. -/
theorem ae_hereditarilyWeightedProjectiveDimensionGeneric
    (n : ℕ) (atom : Type*) [Fintype atom] [DecidableEq atom] :
    ∀ᵐ source : (atom × Fin (n + 1)) → ℝ ∂volume,
      HereditarilyWeightedProjectiveDimensionGeneric source := by
  simp only [HereditarilyWeightedProjectiveDimensionGeneric]
  rw [ae_all_iff]
  intro vertices
  exact (restrictAtomFamily_quasiMeasurePreserving vertices n).ae
    (ae_weightedProjectiveDimensionGeneric n {i // i ∈ vertices})

/-- Absolute continuity also suffices for the simultaneous all-subfamilies
statement. -/
theorem ae_hereditarilyWeightedProjectiveDimensionGeneric_of_absolutelyContinuous
    {n : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (distribution : Measure ((atom × Fin (n + 1)) → ℝ))
    (hdistribution : distribution ≪ volume) :
    ∀ᵐ source ∂distribution,
      HereditarilyWeightedProjectiveDimensionGeneric source := by
  exact hdistribution.ae_le
    (ae_hereditarilyWeightedProjectiveDimensionGeneric n atom)

/-- The alternative atoms touched by the slots of a selected source
subfamily. Repeated slots and overlaps are counted only once. -/
def variableTermNeighborhood
    {atom : Type*} [DecidableEq atom] {M' : ℕ}
    {slotCount : atom → ℕ}
    (indices : ∀ i, Fin (slotCount i) → Fin M')
    (vertices : Finset atom) : Finset (Fin M') :=
  vertices.biUnion fun i => Finset.univ.image (indices i)

theorem variableTerm_index_mem_neighborhood
    {atom : Type*} [DecidableEq atom] {M' : ℕ}
    {slotCount : atom → ℕ}
    (indices : ∀ i, Fin (slotCount i) → Fin M')
    (vertices : Finset atom) {i : atom} (hi : i ∈ vertices)
    (k : Fin (slotCount i)) :
    indices i k ∈ variableTermNeighborhood indices vertices := by
  rw [variableTermNeighborhood, Finset.mem_biUnion]
  exact ⟨i, hi, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩

/-- Restricting a term representation to selected source atoms and deleting
all unused alternative atoms preserves the representation exactly. -/
theorem variableTermRepresentable_restrict_and_compress
    {n M' : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    {slotCount : atom → ℕ}
    {source : (atom × Fin (n + 1)) → ℝ}
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (indices : ∀ i, Fin (slotCount i) → Fin M')
    (coefficients : GenericVariableCoefficientParameters slotCount)
    (hsource : source =
      atomFamilyFromVariableTerms alternative indices coefficients)
    (vertices : Finset atom) :
    VariableTermRepresentable
      (variableTermNeighborhood indices vertices).card
      (fun i : {i // i ∈ vertices} => slotCount i.1)
      (restrictAtomFamily vertices source) := by
  classical
  let neighbors := variableTermNeighborhood indices vertices
  let compressedAlternative :
      Matrix (Fin (n + 1)) (Fin neighbors.card) ℝ :=
    fun r k => alternative r ((Finset.equivFin neighbors).symm k).1
  let compressedIndices :
      ∀ i : {i // i ∈ vertices},
        Fin (slotCount i.1) → Fin neighbors.card :=
    fun i k => Finset.equivFin neighbors
      ⟨indices i.1 k,
        variableTerm_index_mem_neighborhood indices vertices i.2 k⟩
  let restrictedCoefficients : GenericVariableCoefficientParameters
      (fun i : {i // i ∈ vertices} => slotCount i.1) :=
    fun ik => coefficients ⟨ik.1.1, ik.2⟩
  refine ⟨compressedAlternative, compressedIndices,
    restrictedCoefficients, ?_⟩
  rw [hsource]
  funext ir
  simp only [restrictAtomFamily, atomFamilyFromVariableTerms]
  apply Finset.sum_congr rfl
  intro k _hk
  simp [compressedAlternative, compressedIndices, restrictedCoefficients,
    neighbors]

/-- Hereditary weighted genericity yields a projective expansion inequality
for every subset of source atoms and the exact neighborhood of every concrete
term representation. -/
theorem variableTermNeighborhood_projective_expansion
    {n M' : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    {slotCount : atom → ℕ}
    {source : (atom × Fin (n + 1)) → ℝ}
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric source)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (indices : ∀ i, Fin (slotCount i) → Fin M')
    (coefficients : GenericVariableCoefficientParameters slotCount)
    (hsource : source =
      atomFamilyFromVariableTerms alternative indices coefficients)
    (vertices : Finset atom) :
    vertices.card * (n + 1) ≤
      (variableTermNeighborhood indices vertices).card * n +
        ∑ i : {i // i ∈ vertices}, slotCount i.1 := by
  have hrestricted := variableTermRepresentable_restrict_and_compress
    alternative indices coefficients hsource vertices
  have hbound := hgeneric vertices
    (variableTermNeighborhood indices vertices).card
    (fun i : {i // i ∈ vertices} => slotCount i.1) hrestricted
  simpa using hbound

/-- Canonical enumeration of the nonzero coordinates of one coefficient
vector. -/
noncomputable def nonzeroSupportSlotIndex {M' : ℕ}
    (code : FeatureVector M') :
    Fin (nonzeroSupport code).card → Fin M' :=
  fun k => ((Finset.equivFin (nonzeroSupport code)).symm k).1

noncomputable def nonzeroSupportSlotCoefficient {M' : ℕ}
    (code : FeatureVector M') :
    Fin (nonzeroSupport code).card → ℝ :=
  fun k => code (nonzeroSupportSlotIndex code k)

theorem image_nonzeroSupportSlotIndex {M' : ℕ}
    (code : FeatureVector M') :
    Finset.univ.image (nonzeroSupportSlotIndex code) =
      nonzeroSupport code := by
  classical
  ext j
  constructor
  · rintro hj
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hj
    exact ((Finset.equivFin (nonzeroSupport code)).symm k).2
  · intro hj
    let j' : {j // j ∈ nonzeroSupport code} := ⟨j, hj⟩
    apply Finset.mem_image.mpr
    refine ⟨Finset.equivFin (nonzeroSupport code) j', Finset.mem_univ _, ?_⟩
    simp [nonzeroSupportSlotIndex, j']

/-- The canonical support-slot enumeration reproduces an atomwise matrix
factorization exactly. -/
theorem matrixAtomFamily_eq_atomFamilyFrom_nonzeroSupportSlots
    {n M' : ℕ} {atom : Type*} [Fintype atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i)) :
    matrixAtomFamily sourceMatrix =
      atomFamilyFromVariableTerms alternative
        (fun i => nonzeroSupportSlotIndex (code i))
        (fun ik => nonzeroSupportSlotCoefficient (code ik.1) ik.2) := by
  classical
  funext ir
  rw [matrixAtomFamily]
  change sourceMatrix.col ir.1 ir.2 = _
  rw [congrFun (hfactors ir.1) ir.2]
  simp only [Matrix.mulVec, dotProduct, atomFamilyFromVariableTerms]
  let support := nonzeroSupport (code ir.1)
  let enumeration : Fin support.card ≃ {j // j ∈ support} :=
    (Finset.equivFin support).symm
  calc
    (∑ j : Fin M', alternative ir.2 j * code ir.1 j) =
        ∑ j ∈ support, alternative ir.2 j * code ir.1 j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ support)
      intro j _hj_univ hj_support
      have hj_zero : code ir.1 j = 0 := by
        have : j ∉ nonzeroSupport (code ir.1) := by simpa [support]
          using hj_support
        simpa [mem_nonzeroSupport_iff] using this
      simp [hj_zero]
    _ = ∑ j : {j // j ∈ support},
        alternative ir.2 j.1 * code ir.1 j.1 := by
      exact Finset.sum_subtype support (fun _ => Iff.rfl)
        (fun j => alternative ir.2 j * code ir.1 j)
    _ = ∑ k : Fin support.card,
        code ir.1 (enumeration k).1 * alternative ir.2 (enumeration k).1 := by
      symm
      apply Fintype.sum_equiv enumeration
      intro k
      exact mul_comm _ _
    _ = ∑ k : Fin (nonzeroSupport (code ir.1)).card,
        nonzeroSupportSlotCoefficient (code ir.1) k *
          alternative ir.2 (nonzeroSupportSlotIndex (code ir.1) k) := by
      rfl

theorem variableTermNeighborhood_nonzeroSupportSlots
    {M' : ℕ} {atom : Type*} [DecidableEq atom]
    (code : atom → FeatureVector M') (vertices : Finset atom) :
    variableTermNeighborhood
      (fun i => nonzeroSupportSlotIndex (code i)) vertices =
        vertices.biUnion fun i => nonzeroSupport (code i) := by
  classical
  rw [variableTermNeighborhood]
  apply Finset.biUnion_congr rfl
  intro i _hi
  exact image_nonzeroSupportSlotIndex (code i)

/-- Exact subsetwise projective expansion for every atomwise factorization of
a hereditarily generic source family. It counts both distinct alternative
neighbors and the actual support load on the selected source atoms. -/
theorem nonzeroSupport_neighborhood_projective_expansion
    {n M' : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (vertices : Finset atom) :
    vertices.card * (n + 1) ≤
      (vertices.biUnion fun i => nonzeroSupport (code i)).card * n +
        ∑ i : {i // i ∈ vertices}, (nonzeroSupport (code i.1)).card := by
  have hexpansion := variableTermNeighborhood_projective_expansion hgeneric
    alternative (fun i => nonzeroSupportSlotIndex (code i))
    (fun ik => nonzeroSupportSlotCoefficient (code ik.1) ik.2)
    (matrixAtomFamily_eq_atomFamilyFrom_nonzeroSupportSlots
      sourceMatrix alternative code hfactors) vertices
  rwa [variableTermNeighborhood_nonzeroSupportSlots] at hexpansion

/-- Rank-capped subsetwise expansion: redundant coefficients inside a
dependent per-atom support cost only the rank of that support span. -/
theorem supportRank_neighborhood_projective_expansion
    {n M' : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (vertices : Finset atom) :
    vertices.card * (n + 1) ≤
      (vertices.biUnion fun i => nonzeroSupport (code i)).card * n +
        ∑ i : {i // i ∈ vertices}, Module.finrank ℝ
          (columnSpan alternative (nonzeroSupport (code i.1))) := by
  classical
  let slotCount : atom → ℕ := fun i => Module.finrank ℝ
    (columnSpan alternative (nonzeroSupport (code i)))
  have hterms : ∀ i : atom,
      ∃ indices : Fin (slotCount i) → Fin M',
        ∃ coefficients : Fin (slotCount i) → ℝ,
          (∀ k, indices k ∈ nonzeroSupport (code i)) ∧
          ∀ r, alternative.mulVec (code i) r =
            ∑ k, coefficients k * alternative r (indices k) := by
    intro i
    exact exists_rank_term_representation alternative (code i)
  choose indices coefficients hindices_mem hrepresentation using hterms
  let packedCoefficients : GenericVariableCoefficientParameters slotCount :=
    fun ik => coefficients ik.1 ik.2
  have hsource : matrixAtomFamily sourceMatrix =
      atomFamilyFromVariableTerms alternative indices packedCoefficients := by
    funext ir
    rw [matrixAtomFamily, atomFamilyFromVariableTerms]
    exact congrFun (hfactors ir.1) ir.2 |>.trans
      (hrepresentation ir.1 ir.2)
  have hexpansion := variableTermNeighborhood_projective_expansion hgeneric
    alternative indices packedCoefficients hsource vertices
  have hneighborhood_subset : variableTermNeighborhood indices vertices ⊆
      vertices.biUnion fun i => nonzeroSupport (code i) := by
    intro j hj
    rw [variableTermNeighborhood, Finset.mem_biUnion] at hj
    obtain ⟨i, hi, hj⟩ := hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, _hk, rfl⟩ := hj
    rw [Finset.mem_biUnion]
    exact ⟨i, hi, hindices_mem i k⟩
  have hcard := Finset.card_le_card hneighborhood_subset
  exact hexpansion.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right n hcard) _)

/-- Exact integer neighborhood lower bound after charging each source atom
only the rank of the alternative span used to represent it. -/
theorem ceil_supportRank_neighborhood_expansion
    {n M' : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (hn : 0 < n) (vertices : Finset atom) :
    (vertices.card * (n + 1) -
      ∑ i : {i // i ∈ vertices}, Module.finrank ℝ
        (columnSpan alternative (nonzeroSupport (code i.1)))) ⌈/⌉ n ≤
      (vertices.biUnion fun i => nonzeroSupport (code i)).card := by
  rw [ceilDiv_le_iff_le_mul hn]
  rw [Nat.mul_comm n]
  have hdimension := supportRank_neighborhood_projective_expansion
    sourceMatrix alternative code hgeneric hfactors vertices
  omega

/-- Applying the rank-adjusted subset law to all source atoms gives a global
lower bound on total alternative width. -/
theorem ceil_supportRank_global_width_bound
    {n M' : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (hn : 0 < n) :
    (Fintype.card atom * (n + 1) -
      ∑ i, Module.finrank ℝ
        (columnSpan alternative (nonzeroSupport (code i)))) ⌈/⌉ n ≤ M' := by
  have hsubset := ceil_supportRank_neighborhood_expansion
    sourceMatrix alternative code hgeneric hfactors hn
      (Finset.univ : Finset atom)
  have hneighborhood :
      ((Finset.univ : Finset atom).biUnion fun i =>
        nonzeroSupport (code i)).card ≤ M' := by
    simpa using Finset.card_le_univ
      ((Finset.univ : Finset atom).biUnion fun i => nonzeroSupport (code i))
  simpa using hsubset.trans hneighborhood

/-- Uniform-sparsity corollary of exact weighted expansion. -/
theorem sparse_nonzeroSupport_neighborhood_dimension_bound
    {n M' s : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hsparse : ∀ i, (nonzeroSupport (code i)).card ≤ s)
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (vertices : Finset atom) :
    vertices.card * (n + 1) ≤
      (vertices.biUnion fun i => nonzeroSupport (code i)).card * n +
        vertices.card * s := by
  have hexact := nonzeroSupport_neighborhood_projective_expansion
    sourceMatrix alternative code hgeneric hfactors vertices
  have hsum :
      (∑ i : {i // i ∈ vertices}, (nonzeroSupport (code i.1)).card) ≤
        ∑ _i : {i // i ∈ vertices}, s := by
    apply Finset.sum_le_sum
    intro i _hi
    exact hsparse i.1
  exact hexact.trans (Nat.add_le_add_left (by simpa using hsum) _)

/-- The alternative coordinates actually used by a family of atomwise
representations.  This deletes globally unused dictionary columns before any
dimension count, so its cardinality is the intrinsic alternative width. -/
noncomputable def globallyUsedCoordinates {M' : ℕ} {atom : Type*}
    [Fintype atom] [DecidableEq atom]
    (code : atom → FeatureVector M') : Finset (Fin M') :=
  (Finset.univ : Finset atom).biUnion fun i => nonzeroSupport (code i)

/-- Exact generic incidence bound in globally used width.  It strengthens the
declared-width inequality by charging only alternative columns that occur in
at least one source-atom representation:

`M*d ≤ U*(d-1) + M*s`, with `d = n+1` and
`U = card (globallyUsedCoordinates code)`. -/
theorem sparse_global_used_width_dimension_bound
    {n M' s : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hsparse : ∀ i, (nonzeroSupport (code i)).card ≤ s)
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i)) :
    Fintype.card atom * (n + 1) ≤
      (globallyUsedCoordinates code).card * n + Fintype.card atom * s := by
  simpa [globallyUsedCoordinates] using
    sparse_nonzeroSupport_neighborhood_dimension_bound
      sourceMatrix alternative code hgeneric hsparse hfactors
        (Finset.univ : Finset atom)

/-- The globally used width is at most the number of declared alternative
columns. -/
theorem globallyUsedCoordinates_card_le {M' : ℕ} {atom : Type*}
    [Fintype atom] [DecidableEq atom]
    (code : atom → FeatureVector M') :
    (globallyUsedCoordinates code).card ≤ M' := by
  simpa [globallyUsedCoordinates] using
    Finset.card_le_univ (globallyUsedCoordinates code)

/-- Subsetwise projective-codimension expansion: a selected family of source
atoms must touch enough distinct alternative atoms after paying for at most
`s` coefficient parameters per source atom. -/
theorem sparse_nonzeroSupport_neighborhood_projective_expansion
    {n M' s : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hsparse : ∀ i, (nonzeroSupport (code i)).card ≤ s)
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (hs : s ≤ n + 1) (vertices : Finset atom) :
    vertices.card * (n + 1 - s) ≤
      (vertices.biUnion fun i => nonzeroSupport (code i)).card * n := by
  have hdim := sparse_nonzeroSupport_neighborhood_dimension_bound
    sourceMatrix alternative code hgeneric hsparse hfactors vertices
  have hsplit : n + 1 = (n + 1 - s) + s :=
    (Nat.sub_add_cancel hs).symm
  rw [hsplit, Nat.mul_add] at hdim
  omega

/-- Integer-sharp neighborhood expansion, with the necessary ceiling. -/
theorem ceil_sparse_nonzeroSupport_neighborhood_expansion
    {n M' s : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hsparse : ∀ i, (nonzeroSupport (code i)).card ≤ s)
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (hn : 0 < n) (hs : s ≤ n + 1) (vertices : Finset atom) :
    (vertices.card * (n + 1 - s)) ⌈/⌉ n ≤
      (vertices.biUnion fun i => nonzeroSupport (code i)).card := by
  rw [ceilDiv_le_iff_le_mul hn]
  rw [Nat.mul_comm n]
  exact sparse_nonzeroSupport_neighborhood_projective_expansion
    sourceMatrix alternative code hgeneric hsparse hfactors hs vertices

/-- At sparsity one, projective expansion becomes the exact ordinary Hall
condition. Thus a matching of source atoms to distinct used alternative atoms
is forced without assuming full spark of either matrix. -/
theorem oneSparse_nonzeroSupports_globalHall
    {n M' : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hsparse : ∀ i, (nonzeroSupport (code i)).card ≤ 1)
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (hn : 0 < n) :
    AppendixHall.GlobalHall (fun i => nonzeroSupport (code i)) := by
  intro vertices
  have hexpansion := sparse_nonzeroSupport_neighborhood_projective_expansion
    sourceMatrix alternative code hgeneric hsparse hfactors (by omega)
      vertices
  simp only [Nat.add_sub_cancel] at hexpansion
  exact le_of_mul_le_mul_right hexpansion hn

theorem oneSparse_alternative_width_ge_source_card
    {n M' : ℕ} {atom : Type*} [Fintype atom] [DecidableEq atom]
    (sourceMatrix : Matrix (Fin (n + 1)) atom ℝ)
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (code : atom → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily sourceMatrix))
    (hsparse : ∀ i, (nonzeroSupport (code i)).card ≤ 1)
    (hfactors : ∀ i, sourceMatrix.col i = alternative.mulVec (code i))
    (hn : 0 < n) :
    Fintype.card atom ≤ M' := by
  obtain ⟨representative, hinjective, _hmem⟩ :=
    AppendixHall.exists_injective_representative_of_globalHall
      (fun i => nonzeroSupport (code i))
      (oneSparse_nonzeroSupports_globalHall sourceMatrix alternative code
        hgeneric hsparse hfactors hn)
  simpa using Fintype.card_le_of_injective representative hinjective

/-- Source-model version of subsetwise projective expansion. Positive richness
is used only to synthesize sparse codes for the source atoms; hereditary
genericity then forces every selected support neighborhood to expand. -/
theorem exists_sparse_source_atom_factorization_with_projective_expansion
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (heffective : min K' M' ≤ n + 1)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ code : Fin M → FeatureVector M',
      (∀ i, (nonzeroSupport (code i)).card ≤ min K' M') ∧
      (∀ i, matrix.col i = alternative.mulVec (code i)) ∧
      ∀ vertices : Finset (Fin M),
        vertices.card * (n + 1 - min K' M') ≤
          (vertices.biUnion fun i => nonzeroSupport (code i)).card * n := by
  obtain ⟨code, hcode_card, hcode⟩ :=
    exists_sparse_source_atom_factorization_of_kRich_and_factorizations
      matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
        halternativeSparse halternativeFactors
  refine ⟨code, hcode_card, hcode, ?_⟩
  intro vertices
  exact sparse_nonzeroSupport_neighborhood_projective_expansion
    matrix alternative code hgeneric hcode_card hcode heffective vertices

/-- Source-model wrapper for the exact globally used-width count. Positive
richness supplies one effective-sparse representation of every source atom;
hereditary genericity then charges only the union of coordinates actually used
by those representations. -/
theorem exists_sparse_source_atom_factorization_with_used_width_bound
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ code : Fin M → FeatureVector M',
      (∀ i, (nonzeroSupport (code i)).card ≤ min K' M') ∧
      (∀ i, matrix.col i = alternative.mulVec (code i)) ∧
      M * (n + 1) ≤
        (globallyUsedCoordinates code).card * n + M * min K' M' := by
  obtain ⟨code, hcode_card, hcode⟩ :=
    exists_sparse_source_atom_factorization_of_kRich_and_factorizations
      matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
        halternativeSparse halternativeFactors
  refine ⟨code, hcode_card, hcode, ?_⟩
  simpa using sparse_global_used_width_dimension_bound
    matrix alternative code hgeneric hcode_card hcode

/-- The source-model bridge also produces one sparse atomwise factorization
obeying the exact rank-capped expansion law on every source subset. This form
needs no a priori ceiling on the effective sparsity. -/
theorem exists_sparse_source_atom_factorization_with_rank_expansion
    {X : Type*} {n M M' K K' : ℕ}
    (matrix : Matrix (Fin (n + 1)) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hgeneric : HereditarilyWeightedProjectiveDimensionGeneric
      (matrixAtomFamily matrix))
    (hKpos : 0 < K) (hK_le_M : K ≤ M)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ code : Fin M → FeatureVector M',
      (∀ i, (nonzeroSupport (code i)).card ≤ min K' M') ∧
      (∀ i, matrix.col i = alternative.mulVec (code i)) ∧
      ∀ vertices : Finset (Fin M),
        vertices.card * (n + 1) ≤
          (vertices.biUnion fun i => nonzeroSupport (code i)).card * n +
            ∑ i : {i // i ∈ vertices}, Module.finrank ℝ
              (columnSpan alternative (nonzeroSupport (code i.1))) := by
  obtain ⟨code, hcode_card, hcode⟩ :=
    exists_sparse_source_atom_factorization_of_kRich_and_factorizations
      matrix z f alternative alternativeCode hKpos hK_le_M hrich hfactors
        halternativeSparse halternativeFactors
  refine ⟨code, hcode_card, hcode, ?_⟩
  intro vertices
  exact supportRank_neighborhood_projective_expansion
    matrix alternative code hgeneric hcode vertices

end PKG26AtomicFeatures
