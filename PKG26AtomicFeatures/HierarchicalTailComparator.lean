import PKG26AtomicFeatures.HierarchicalSupportLaw
import PKG26AtomicFeatures.RankedFeatureTail
import PKG26AtomicFeatures.AETailComparator

/-!
# Whole-family comparators for hierarchical populations

A width-m comparator retains all three atoms of each of the first floor(m/3)
parent families and fills any remaining slots with source atoms. The omitted
atomic prevalence is at most twice the omitted parent prevalence, since a
parent of prevalence q has two children of prevalence q/2 each.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped BigOperators ENNReal

/-- All three atoms of every selected parent family. -/
def wholeFamilyAtoms {N : ℕ} (P : Finset (Fin N)) : Finset (Fin (N * 3)) :=
  (P ×ˢ Finset.univ).image finProdFinEquiv

@[simp] theorem mem_wholeFamilyAtoms {N : ℕ} (P : Finset (Fin N))
    (i : Fin N) (k : Fin 3) : finProdFinEquiv (i, k) ∈ wholeFamilyAtoms P ↔ i ∈ P := by
  simp [wholeFamilyAtoms]

theorem wholeFamilyAtoms_card {N : ℕ} (P : Finset (Fin N)) :
    (wholeFamilyAtoms P).card = 3 * P.card := by
  rw [wholeFamilyAtoms, Finset.card_image_of_injective _ finProdFinEquiv.injective,
    Finset.card_product]
  simp [Nat.mul_comm]

theorem wholeFamilyAtoms_complement {N : ℕ} (P : Finset (Fin N)) :
    Finset.univ \ wholeFamilyAtoms P = wholeFamilyAtoms (Finset.univ \ P) := by
  ext a
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective a
  simp

/-- The total prevalence of a complete family is twice its parent prevalence. -/
theorem sum_wholeFamilyAtoms {N : ℕ} (p : Fin (N * 3) → ℝ) (q : Fin N → ℝ)
    (hparent : ∀ i, p (hierarchicalParent i) = q i)
    (hchild : ∀ i k, p (hierarchicalChild i k) = q i / 2)
    (P : Finset (Fin N)) :
    ∑ a ∈ wholeFamilyAtoms P, p a = 2 * ∑ i ∈ P, q i := by
  rw [wholeFamilyAtoms, Finset.sum_image]
  · rw [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change p (hierarchicalParent i) +
      (p (hierarchicalChild i 0) + p (hierarchicalChild i 1)) = 2 * q i
    rw [hparent, hchild, hchild]
    ring
  · exact fun _ _ _ _ h => finProdFinEquiv.injective h

/-- Filling the remaining width slots can only improve the complete-family
comparator. No sorting assumption or distributional independence is needed
for this finite marginal calculation. -/
theorem exists_whole_family_comparator_embedding {N m : ℕ}
    (p : Fin (N * 3) → ℝ) (q : Fin N → ℝ)
    (hp : ∀ a, 0 ≤ p a)
    (hparent : ∀ i, p (hierarchicalParent i) = q i)
    (hchild : ∀ i k, p (hierarchicalChild i k) = q i / 2)
    (σ : Equiv.Perm (Fin N)) (hm : m ≤ N * 3) :
    ∃ e : Fin m ↪ Fin (N * 3),
      (∑ a ∈ Finset.univ \ Finset.univ.image e, p a) ≤
        2 * rankedFeatureTail q σ (m / 3) := by
  classical
  have hn : m / 3 ≤ N := by omega
  let P : Finset (Fin N) := Finset.univ.image (rankedPrefixEmbedding σ hn)
  have hP : P.card = m / 3 := by
    simp only [P, Finset.card_image_of_injective _ (rankedPrefixEmbedding σ hn).injective,
      Finset.card_univ, Fintype.card_fin]
  have hR : (wholeFamilyAtoms P).card ≤ m := by
    rw [wholeFamilyAtoms_card, hP]
    omega
  obtain ⟨Q, hRQ, _, hQ⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (wholeFamilyAtoms P)) hR
      (show m ≤ (Finset.univ : Finset (Fin (N * 3))).card by simpa using hm)
  let S : ExactSourceSupport (N * 3) m := ⟨Q, hQ⟩
  refine ⟨sourceSupportEnumeration S, ?_⟩
  rw [sourceSupportEnumeration_image]
  change (∑ a ∈ Finset.univ \ Q, p a) ≤ _
  calc
    _ ≤ ∑ a ∈ Finset.univ \ wholeFamilyAtoms P, p a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ a,
          fun haR => (Finset.mem_sdiff.mp ha).2 (hRQ haR)⟩
      · exact fun a _ _ => hp a
    _ = 2 * ∑ i ∈ Finset.univ \ P, q i := by
      rw [wholeFamilyAtoms_complement, sum_wholeFamilyAtoms p q hparent hchild]
    _ = _ := by rw [sum_outside_rankedPrefix_eq_rankedFeatureTail q σ hn]

/-- Actual approximate optimization is bounded by the whole-family tail
at floor(m/3), including widths not divisible by three. -/
theorem IsApproximatelyOptimalRecoveryPair.loss_le_hierarchical_parent_tail
    {Ω : Type*} [MeasurableSpace Ω] {d N m K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin d) (Fin (N * 3)) ℝ) (z : Ω → FeatureVector (N * 3))
    (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m)
    (q : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (γ C₀ : ℝ)
    (hopt : IsApproximatelyOptimalRecoveryPair μ A z B code γ C₀ K)
    (hA : HasUnitEuclideanColumns A) (hstable : SparseLowerStable A γ (2 * K))
    (hz : Measurable z) (hsparse : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card ≤ K)
    (hbounded : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i ∧ z x i ≤ 1)
    (hparent : ∀ i, featurePrevalence μ z (hierarchicalParent i) = q i)
    (hchild : ∀ i k, featurePrevalence μ z (hierarchicalChild i k) = q i / 2)
    (hC₀ : 0 ≤ C₀) (hm : m ≤ N * 3) :
    actualPopulationSquaredLoss μ A z B code ≤
      ENNReal.ofReal (2 * C₀ * K * rankedFeatureTail q σ (m / 3)) := by
  obtain ⟨e, he⟩ := exists_whole_family_comparator_embedding
    (featurePrevalence μ z) q (fun _ => measureReal_nonneg) hparent hchild σ hm
  have h := hopt.loss_le_omitted_prevalence_ae μ A z B code e γ C₀
    hA hstable hz hsparse hbounded hC₀
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  change C₀ * K * (∑ a ∈ Finset.univ \ Finset.univ.image e, featurePrevalence μ z a) ≤ _
  calc
    _ ≤ C₀ * K * (2 * rankedFeatureTail q σ (m / 3)) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hC₀ (Nat.cast_nonneg K))
    _ = _ := by ring

end PKG26AtomicFeatures
