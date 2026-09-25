import PKG26AtomicFeatures.SparseStability
import PKG26AtomicFeatures.AdjacentSupportRigidity

/-!
# Rigidity from sparse stability and open richness

Quantitative sparse stability implies the sparse injectivity used by the
algebraic rigidity proof. Relatively open richness suffices throughout the
range `1 ≤ K < M`, including `M < 2*K`.
-/

namespace PKG26AtomicFeatures

/-- Pair equivalence with possibly different width indices. The equivalence
itself proves equal widths; columns and codes use the same nonzero scales. -/
def AtomicPairsEquivalent {X : Type*} {d M M' : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (B : Matrix (Fin d) (Fin M') ℝ) (u : X → FeatureVector M') : Prop :=
  ∃ permutation : Fin M' ≃ Fin M, ∃ scale : Fin M' → ℝ,
    (∀ j, scale j ≠ 0) ∧
    (∀ j, B.col j = scale j • A.col (permutation j)) ∧
    ∀ x j, z x (permutation j) = scale j * u x j

/-- Unit-normalized nonnegative dictionary/code pairs are compared by a
single permutation, with no remaining scaling or sign freedom. -/
def AtomicPairsPermutationEquivalent {X : Type*} {d M M' : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (B : Matrix (Fin d) (Fin M') ℝ) (u : X → FeatureVector M') : Prop :=
  ∃ permutation : Fin M' ≃ Fin M,
    (∀ j, B.col j = A.col (permutation j)) ∧
    ∀ x j, z x (permutation j) = u x j

/-- Normalization removes the magnitude of each scale; a positive source
activation together with nonnegative learned codes removes its sign. -/
theorem AtomicPairsEquivalent.permutation_of_unit_nonnegative
    {X : Type*} {d M M' : ℕ}
    {A : Matrix (Fin d) (Fin M) ℝ} {z : X → FeatureVector M}
    {B : Matrix (Fin d) (Fin M') ℝ} {u : X → FeatureVector M'}
    (h : AtomicPairsEquivalent A z B u)
    (hA : HasUnitEuclideanColumns A) (hB : HasUnitEuclideanColumns B)
    (hz : ∀ i, ∃ x, 0 < z x i) (hu : ∀ x j, 0 ≤ u x j) :
    AtomicPairsPermutationEquivalent A z B u := by
  obtain ⟨permutation, scale, _hnonzero, hcolumns, hcodes⟩ := h
  have hscale (j : Fin M') : scale j = 1 := by
    have habs : |scale j| = 1 := by
      have hn := hB j
      rw [hcolumns j, map_smul, norm_smul, hA (permutation j), mul_one,
        Real.norm_eq_abs] at hn
      exact hn
    obtain ⟨x, hx⟩ := hz (permutation j)
    have hp : 0 < scale j := by
      by_contra hn
      have hprod : scale j * u x j ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (hu x j)
      rw [← hcodes x j] at hprod
      exact (not_lt_of_ge hprod) hx
    rwa [abs_of_pos hp] at habs
  refine ⟨permutation, ?_, ?_⟩
  · intro j
    simpa only [hscale j, one_smul] using hcolumns j
  · intro x j
    simpa only [hscale j, one_mul] using hcodes x j

/-- Complete rigidity under sharp sparse injectivity and open richness.
The three conclusions are the unfolded content of the draft's disjunction:
sparsity cannot decrease, equal dimensions identify the pair, and reducing
width at least doubles sparsity. No quantitative margin is needed here. -/
theorem atomic_rigidity_of_openRich
    {X : Type*} {d M M' K K' : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (B : Matrix (Fin d) (Fin M') ℝ) (u : X → FeatureVector M')
    (f : X → RepresentationVector d)
    (hK : 0 < K) (hKM : K < M)
    (hA : KSparseInjective A K) (hB : KSparseInjective B K')
    (hz : KSparse (K := K) z) (hrich : OpenKRich (K := K) z)
    (hf : ∀ x, f x = A.mulVec (z x))
    (hu : KSparse (K := K') u) (hBu : ∀ x, f x = B.mulVec (u x)) :
    K ≤ K' ∧
      (M' = M → K' = K → AtomicPairsEquivalent A z B u) ∧
      (M' < M → 2 * K ≤ K') := by
  have hAspark := (kSparseInjective_iff_min_lt_spark A).mp hA
  obtain ⟨extended, hextSparse, hextFactors⟩ :=
    exists_alternative_code_on_universal_sparse_domain A z f B u
      hKM.le hrich hf hu hBu
  have hKspark : K < spark A := by omega
  refine ⟨?_, ?_, ?_⟩
  · exact AppendixHall.source_sparsity_le_alternative_sparsity_of_lt_spark
      A universalSparseCode (universalSparseRepresentation A) B extended
      hKspark universalSparseCode_rich (fun _ => rfl) hextSparse hextFactors
  · intro hwidth hsparsity
    subst M'
    subst K'
    obtain ⟨permutation, scale, hscale, hcolumns, _⟩ :=
      equal_size_dictionary_and_code_identifiability_of_min_lt_spark
        A universalSparseCode (universalSparseRepresentation A) B extended
        hK hKM hAspark universalSparseCode_rich universalSparseCode_sparse
        (fun _ => rfl) hextSparse hextFactors
    refine ⟨permutation, scale, hscale, hcolumns, ?_⟩
    have haligned := kSparse_alignAlternativeCode permutation scale hscale u hu
    intro x j
    have heq : z x = alignAlternativeCode permutation scale (u x) := by
      apply hA _ _ (hz x) (haligned x)
      exact (hf x).symm.trans ((hBu x).trans
        (mulVec_alignAlternativeCode A B permutation scale hcolumns (u x)))
    simpa [alignAlternativeCode] using congrFun heq (permutation j)
  · intro hwidth
    have hBmin : KSparseInjective B (min K' M') := by
      intro left right hl hr heq
      exact hB left right (hl.trans (Nat.min_le_left _ _))
        (hr.trans (Nat.min_le_left _ _)) heq
    have hcutoff := effective_sparsity_ge_spark_cutoff_of_strict_width
      A universalSparseCode (universalSparseRepresentation A) B extended
      hK hKM.le hwidth hBmin universalSparseCode_rich (fun _ => rfl)
      hextSparse hextFactors
    omega

/-- The draft's rigidity alternative, with componentwise strict domination
spelled out instead of leaving the order on `(width, sparsity)` implicit.
Source and learned margins may differ. -/
theorem atomic_rigidity_of_sparse_unit_cube
    {X : Type*} {d M M' K K' : ℕ} {α γ : ℝ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (B : Matrix (Fin d) (Fin M') ℝ) (u : X → FeatureVector M')
    (f : X → RepresentationVector d)
    (hK : 0 < K) (hKM : K < M) (hα : 0 < α) (hγ : 0 < γ)
    (hA : SparseLowerStable A α (2 * K))
    (hB : SparseLowerStable B γ (2 * K'))
    (hz : KSparse (K := K) z)
    (hcube : ∀ v : FeatureVector M, (nonzeroSupport v).card ≤ K →
      (∀ i, 0 ≤ v i ∧ v i ≤ 1) → v ∈ Set.range z)
    (hf : ∀ x, f x = A.mulVec (z x))
    (hu : KSparse (K := K') u) (hBu : ∀ x, f x = B.mulVec (u x)) :
    AtomicPairsEquivalent A z B u ∨
      (M ≤ M' ∧ K ≤ K' ∧ (M < M' ∨ K < K')) ∨ 2 * K ≤ K' := by
  obtain ⟨hsparse, hequal, hnarrow⟩ := atomic_rigidity_of_openRich
    A z B u f hK hKM (hA.sparseInjective hα) (hB.sparseInjective hγ)
    hz (openKRich_of_sparse_unit_cube_range z hcube) hf hu hBu
  by_cases hwidth : M' < M
  · exact Or.inr (Or.inr (hnarrow hwidth))
  · by_cases heqM : M' = M
    · by_cases heqK : K' = K
      · exact Or.inl (hequal heqM heqK)
      · exact Or.inr (Or.inl ⟨by omega, hsparse, Or.inr (by omega)⟩)
    · exact Or.inr (Or.inl ⟨by omega, hsparse, Or.inl (by omega)⟩)

end PKG26AtomicFeatures
