import PKG26AtomicFeatures.Featurization
import PKG26AtomicFeatures.SphericalGenericDimension

/-!
# Generic rigidity for identifiable featurizations

Relatively open richness supplies sparse representations of every source
column in one fixed alternative dictionary. The projective incidence bound
on the product of unit spheres then yields both numerical conclusions of
the generic-rigidity theorem.
-/

open MeasureTheory

namespace PKG26AtomicFeatures

/-- Every source dimension `d ≥ 2` has the sphere-coordinate form `n + 1`
with `n ≥ 1`, and conversely. -/
theorem ambient_dimension_parameter_translation (d : ℕ) :
    2 ≤ d ↔ ∃ n : ℕ, 1 ≤ n ∧ d = n + 1 := by
  constructor
  · intro hd
    exact ⟨d - 1, by omega, by omega⟩
  · rintro ⟨n, hn, rfl⟩
    omega

/-- Every finite matrix has spark at most one more than its ambient dimension,
including the convention for linearly independent columns. -/
theorem spark_le_ambient_dimension_succ {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) : spark matrix ≤ d + 1 := by
  classical
  by_cases hM : M ≤ d
  · exact (spark_le_column_count_succ matrix).trans (by omega)
  obtain ⟨coordinates, _, hcard⟩ :=
    Finset.exists_subset_card_eq (show d + 1 ≤ (Finset.univ : Finset (Fin M)).card by
      simpa using Nat.succ_le_of_lt (Nat.lt_of_not_ge hM))
  have hdependent : ¬ LinearIndependent ℝ (selectedColumns matrix coordinates) := by
    intro hli
    have hbound := hli.fintype_card_le_finrank
    have : coordinates.card ≤ d := by simpa using hbound
    omega
  simpa [hcard] using spark_le_card_of_dependent matrix coordinates hdependent

/-- Open-subset richness suffices for the sparse source-atom factorization
used by the projective dimension count. -/
theorem exists_sparse_source_atom_factorization_of_openKRich
    {X : Type*} {d M M' K K' : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (code : X → FeatureVector M)
    (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hK : K ≤ M) (hrich : OpenKRich (K := K) code)
    (hfactors : ∀ x, f x = matrix.mulVec (code x))
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ atomCode : Fin M → FeatureVector M',
      (∀ i, (nonzeroSupport (atomCode i)).card ≤ min K' M') ∧
        ∀ i, matrix.col i = alternative.mulVec (atomCode i) := by
  obtain ⟨extended, hsparse, hfactor⟩ :=
    exists_alternative_code_on_universal_sparse_domain matrix code f alternative
      alternativeCode hK hrich hfactors halternativeSparse halternativeFactors
  exact exists_sparse_source_atom_factorization_of_kRich_and_factorizations matrix
    universalSparseCode (universalSparseRepresentation matrix) alternative extended
    hKpos hK universalSparseCode_rich (fun _ => rfl) hsparse hfactor

/-- The source's real sparsity bound at every spherical family satisfying the
almost-everywhere incidence bound.  The effective alternative sparsity budget
is `min K' M'`, so this dimension count does not require a spark condition. -/
theorem generic_featurization_sparsity_bound
    {X : Type*} {n M M' K K' : ℕ} (source : ProductUnitSphere n M)
    (code : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hn : 0 < n) (hM : 0 < M) (hK : 0 < K) (hK_le_M : K ≤ M)
    (hgeneric : SphericalProjectiveDimensionGeneric source)
    (hfactors : ∀ x, f x = (ProductUnitSphere.matrix source).mulVec (code x))
    (hrich : OpenKRich (K := K) code)
    (halternativeSparse : KSparse (K := K') alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    1 + (n : ℝ) * ((M : ℝ) - M') / M ≤ K' := by
  obtain ⟨atomCode, hsparse, hfactor⟩ :=
    exists_sparse_source_atom_factorization_of_openKRich (ProductUnitSphere.matrix source) code f
      alternative alternativeCode hK hK_le_M hrich hfactors
      halternativeSparse halternativeFactors
  have hterms : STermRepresentable M' (min K' M')
      (ProductUnitSphere.atomFamily source) := by
    exact sTermRepresentable_of_sparse_atom_factorization (Nat.min_le_right K' M')
      (ProductUnitSphere.matrix source) alternative atomCode hsparse hfactor
  have heffective_pos : 1 ≤ min K' M' := by
    by_contra h
    have hzero : min K' M' = 0 := by omega
    rw [hzero] at hterms
    exact ProductUnitSphere.not_sTermRepresentable_zero source hM hterms
  have hdim := hgeneric M' (min K' M') hterms
  have hdimR : (M : ℝ) * n ≤ (M' : ℝ) * n +
      M * (((min K' M' : ℕ) : ℝ) - 1) := by
    exact_mod_cast hdim
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hquotient : (n : ℝ) * ((M : ℝ) - M') / M ≤
      ((min K' M' : ℕ) : ℝ) - 1 := by
    apply (div_le_iff₀ hMR).mpr
    nlinarith
  have heffective_le : ((min K' M' : ℕ) : ℝ) ≤ K' := by
    exact_mod_cast Nat.min_le_left K' M'
  linarith

/-- The source's real sparsity bound and strict half-width consequence at
every spherical family satisfying the almost-everywhere incidence bound. -/
theorem generic_featurization_bounds
    {X : Type*} {n M M' K K' : ℕ} (source : ProductUnitSphere n M)
    (code : X → FeatureVector M) (f : X → RepresentationVector (n + 1))
    (alternative : Matrix (Fin (n + 1)) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hn : 0 < n) (hM : 0 < M) (hK : 0 < K) (hK_le_M : K ≤ M)
    (hgeneric : SphericalProjectiveDimensionGeneric source)
    (hfactors : ∀ x, f x = (ProductUnitSphere.matrix source).mulVec (code x))
    (hrich : OpenKRich (K := K) code)
    (halt : IsFeaturization K' alternative alternativeCode f) :
    1 + (n : ℝ) * ((M : ℝ) - M') / M ≤ K' ∧ (M : ℝ) / 2 < M' := by
  have hsparsity := generic_featurization_sparsity_bound source code f alternative
    alternativeCode hn hM hK hK_le_M hgeneric hfactors hrich halt.1 halt.2.1
  refine ⟨hsparsity, ?_⟩
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hquotient : (n : ℝ) * ((M : ℝ) - M') / M ≤ (K' : ℝ) - 1 := by
    linarith
  have hdimR : (M : ℝ) * n ≤ (M' : ℝ) * n + M * ((K' : ℝ) - 1) := by
    have hcross := (div_le_iff₀ hMR).mp hquotient
    nlinarith
  have hspark := spark_le_ambient_dimension_succ alternative
  have hK'dim : 2 * K' ≤ n + 1 := by have := halt.2.2; omega
  have hK'dimR : 2 * (K' : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hK'dim
  by_contra hnot
  have hwidthR : 2 * (M' : ℝ) ≤ M := by linarith
  nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hwidthR),
    mul_nonneg hMR.le (sub_nonneg.mpr hK'dimR)]

end PKG26AtomicFeatures
