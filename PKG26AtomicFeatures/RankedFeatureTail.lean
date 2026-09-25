import PKG26AtomicFeatures.SourceTruncationBounds
import Mathlib.Data.Fin.Embedding

/-!
# Ranked prevalence tails and nested recovery sets

A permutation fixes one ordering of the source features. The first `m`
positions determine an actual source subdictionary, and its omitted marginal
mass is exactly the suffix sum. This identity and width monotonicity do not
need sortedness. Sortedness is only used to identify the recovery set as an
initial segment of the chosen ordering.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped BigOperators ENNReal

/-- The concrete embedding of the first `m` entries in a permutation. -/
def rankedPrefixEmbedding {M m : ℕ} (σ : Equiv.Perm (Fin M)) (hm : m ≤ M) :
    Fin m ↪ Fin M :=
  (Fin.castLEEmb hm).trans σ.toEmbedding

@[simp] theorem rankedPrefixEmbedding_apply {M m : ℕ}
    (σ : Equiv.Perm (Fin M)) (hm : m ≤ M) (j : Fin m) :
    rankedPrefixEmbedding σ hm j = σ (Fin.castLE hm j) := rfl

/-- Prefix membership is exactly the rank test after applying the inverse
permutation. This includes the empty and full prefixes. -/
theorem mem_rankedPrefixEmbedding_image {M m : ℕ}
    (σ : Equiv.Perm (Fin M)) (hm : m ≤ M) (i : Fin M) :
    i ∈ Finset.univ.image (rankedPrefixEmbedding σ hm) ↔ (σ.symm i).val < m := by
  classical
  constructor
  · rintro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    simpa only [rankedPrefixEmbedding_apply, σ.symm_apply_apply, Fin.val_castLE] using j.isLt
  · intro hi
    let j : Fin m := ⟨(σ.symm i).val, hi⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    have hcast : Fin.castLE hm j = σ.symm i := Fin.ext rfl
    rw [rankedPrefixEmbedding_apply, hcast, σ.apply_symm_apply]

/-- The suffix weight after retaining the first `m` ranked coordinates.
Widths at least `M` have empty suffix. -/
noncomputable def rankedFeatureTail {M : ℕ} (p : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin M => m ≤ j.val), p (σ j)

/-- Omitting the concrete ranked prefix gives exactly the suffix sum,
for arbitrary weights and arbitrary permutation. -/
theorem sum_outside_rankedPrefix_eq_rankedFeatureTail {M m : ℕ}
    (p : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) (hm : m ≤ M) :
    (∑ i ∈ Finset.univ \ Finset.univ.image (rankedPrefixEmbedding σ hm), p i) =
      rankedFeatureTail p σ m := by
  classical
  have hset : Finset.univ \ Finset.univ.image (rankedPrefixEmbedding σ hm) =
      (Finset.univ.filter fun j : Fin M => m ≤ j.val).image σ := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    rw [mem_rankedPrefixEmbedding_image]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact ⟨σ.symm i, Nat.le_of_not_gt hi, σ.apply_symm_apply i⟩
    · rintro ⟨j, hj, rfl⟩
      simpa only [σ.symm_apply_apply, not_lt] using hj
  rw [hset, Finset.sum_image]
  · rfl
  · intro i _ j _ hij
    exact σ.injective hij

/-- The actual omitted feature prevalence of the ranked source comparator
is the ranked tail of the actual population prevalences. -/
theorem omittedFeaturePrevalence_rankedPrefix_eq
    {Ω : Type*} [MeasurableSpace Ω] {M m : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M)
    (σ : Equiv.Perm (Fin M)) (hm : m ≤ M) :
    omittedFeaturePrevalence μ z (Finset.univ.image (rankedPrefixEmbedding σ hm)) =
      rankedFeatureTail (featurePrevalence μ z) σ m :=
  sum_outside_rankedPrefix_eq_rankedFeatureTail (featurePrevalence μ z) σ hm

theorem rankedFeatureTail_nonneg {M : ℕ} (p : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (σ : Equiv.Perm (Fin M)) (m : ℕ) :
    0 ≤ rankedFeatureTail p σ m :=
  Finset.sum_nonneg fun j _ => hp (σ j)

/-- Increasing retained width can only decrease a nonnegative-weight tail. -/
theorem rankedFeatureTail_le_of_width_le {M m m' : ℕ}
    (p : Fin M → ℝ) (hp : ∀ i, 0 ≤ p i) (σ : Equiv.Perm (Fin M))
    (hwidth : m ≤ m') : rankedFeatureTail p σ m' ≤ rankedFeatureTail p σ m := by
  unfold rankedFeatureTail
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwidth.trans (Finset.mem_filter.mp hj).2⟩
  · intro j _ _
    exact hp (σ j)

theorem rankedFeatureTail_antitone {M : ℕ} (p : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (σ : Equiv.Perm (Fin M)) :
    Antitone (rankedFeatureTail p σ) :=
  fun _ _ h => rankedFeatureTail_le_of_width_le p hp σ h

@[simp] theorem rankedFeatureTail_eq_zero_of_width_ge {M m : ℕ}
    (p : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) (hm : M ≤ m) :
    rankedFeatureTail p σ m = 0 := by
  have hempty : (Finset.univ.filter fun j : Fin M => m ≤ j.val) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j _ hj
    have hjM := j.isLt
    omega
  simp only [rankedFeatureTail, hempty, Finset.sum_empty]

/-- Positive-prevalence features meeting the tail-based recovery threshold. -/
noncomputable def tailRecoverableFeatures {M : ℕ} (p : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (C : ℝ) (m : ℕ) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun i => 0 < p i ∧ C * rankedFeatureTail p σ m ≤ p i

@[simp] theorem mem_tailRecoverableFeatures {M : ℕ} (p : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (C : ℝ) (m : ℕ) (i : Fin M) :
    i ∈ tailRecoverableFeatures p σ C m ↔
      0 < p i ∧ C * rankedFeatureTail p σ m ≤ p i := by
  classical
  simp [tailRecoverableFeatures]

/-- The same ordering and nonnegative threshold constant give nested
recoverable feature sets as retained width increases. -/
theorem tailRecoverableFeatures_subset_of_width_le {M m m' : ℕ}
    (p : Fin M → ℝ) (hp : ∀ i, 0 ≤ p i) (σ : Equiv.Perm (Fin M))
    (C : ℝ) (hC : 0 ≤ C) (hwidth : m ≤ m') :
    tailRecoverableFeatures p σ C m ⊆ tailRecoverableFeatures p σ C m' := by
  intro i hi
  obtain ⟨hpos, hbound⟩ := (mem_tailRecoverableFeatures p σ C m i).mp hi
  exact (mem_tailRecoverableFeatures p σ C m' i).mpr ⟨hpos,
    (mul_le_mul_of_nonneg_left (rankedFeatureTail_le_of_width_le p hp σ hwidth) hC).trans hbound⟩

theorem tailRecoverableFeatures_monotone {M : ℕ} (p : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (σ : Equiv.Perm (Fin M)) (C : ℝ) (hC : 0 ≤ C) :
    Monotone (tailRecoverableFeatures p σ C) :=
  fun _ _ h => tailRecoverableFeatures_subset_of_width_le p hp σ C hC h

/-- The last recoverable one-based rank, with maximum of the empty set
defined as zero. Under a decreasing ordering it is the initial-segment size. -/
noncomputable def tailRecoverableRank {M : ℕ} (p : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (C : ℝ) (m : ℕ) : ℕ :=
  (tailRecoverableFeatures p σ C m).sup fun i => (σ.symm i).val + 1

theorem tailRecoverableRank_le {M : ℕ} (p : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (C : ℝ) (m : ℕ) :
    tailRecoverableRank p σ C m ≤ M := by
  apply Finset.sup_le
  intro i _
  exact Nat.succ_le_of_lt (σ.symm i).isLt

theorem tailRecoverableRank_eq_zero_of_empty {M : ℕ} (p : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (C : ℝ) (m : ℕ)
    (hempty : tailRecoverableFeatures p σ C m = ∅) :
    tailRecoverableRank p σ C m = 0 := by
  simp only [tailRecoverableRank, hempty, Finset.sup_empty, bot_eq_zero]

/-- With weights in decreasing rank order, the tail-threshold recovery set
is exactly the first `r` coordinates, where `r` is the empty-safe maximum. -/
theorem mem_tailRecoverableFeatures_iff_rank_lt
    {M : ℕ} (p : Fin M → ℝ) (σ : Equiv.Perm (Fin M))
    (horder : Antitone (fun j : Fin M => p (σ j))) (C : ℝ) (m : ℕ) (j : Fin M) :
    σ j ∈ tailRecoverableFeatures p σ C m ↔ j.val < tailRecoverableRank p σ C m := by
  constructor
  · intro hj
    have hsup := Finset.le_sup (f := fun i : Fin M => (σ.symm i).val + 1) hj
    simp only [σ.symm_apply_apply] at hsup
    exact Nat.lt_of_succ_le hsup
  · intro hj
    have hle : j.val + 1 ≤ tailRecoverableRank p σ C m := Nat.succ_le_of_lt hj
    obtain ⟨i, hi, hji⟩ := (Finset.le_sup_iff (show (0 : ℕ) < j.val + 1 by omega)).mp hle
    have hrank : j ≤ σ.symm i := by
      change j.val ≤ (σ.symm i).val
      omega
    have hp : p i ≤ p (σ j) := by simpa only [σ.apply_symm_apply] using horder hrank
    obtain ⟨hipos, hibound⟩ := (mem_tailRecoverableFeatures p σ C m i).mp hi
    exact (mem_tailRecoverableFeatures p σ C m (σ j)).mpr
      ⟨hipos.trans_le hp, hibound.trans hp⟩

/-- The empty-safe recovery rank is nondecreasing with model width. This
rank monotonicity holds even before imposing sortedness. -/
theorem tailRecoverableRank_monotone {M : ℕ} (p : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (σ : Equiv.Perm (Fin M)) (C : ℝ) (hC : 0 ≤ C) :
    Monotone (tailRecoverableRank p σ C) := by
  intro m m' hwidth
  exact Finset.sup_mono (tailRecoverableFeatures_subset_of_width_le p hp σ C hC hwidth)

/-- The concrete ranked source subdictionary has the exact prevalence-tail
comparison bound used in recovery. -/
theorem actualPopulationSquaredLoss_ranked_source_truncation_le
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (σ : Equiv.Perm (Fin M)) (hm : m ≤ M)
    (hA : HasUnitEuclideanColumns A) (hz : Measurable z)
    (hsparse : KSparse (K := K) z) (hnonneg : ∀ x j, 0 ≤ z x j)
    (hbounded : ∀ x j, z x j ≤ 1) :
    actualPopulationSquaredLoss μ A z (A.submatrix id (rankedPrefixEmbedding σ hm))
      (fun x j => z x (rankedPrefixEmbedding σ hm j)) ≤
        ENNReal.ofReal ((K : ℝ) * rankedFeatureTail (featurePrevalence μ z) σ m) := by
  simpa only [omittedFeaturePrevalence_rankedPrefix_eq] using
    actualPopulationSquaredLoss_source_truncation_le μ A z (rankedPrefixEmbedding σ hm)
      hA hz hsparse hnonneg hbounded

/-- An approximately optimal learned pair inherits the actual ranked-tail
loss bound from the feasible ranked source truncation. -/
theorem IsApproximatelyOptimalRecoveryPair.loss_le_rankedFeatureTail
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m)
    (σ : Equiv.Perm (Fin M)) (hm : m ≤ M) (γ C : ℝ)
    (hopt : IsApproximatelyOptimalRecoveryPair μ A z B u γ C K)
    (hA : HasUnitEuclideanColumns A) (hstable : SparseLowerStable A γ (2 * K))
    (hz : Measurable z) (hsparse : KSparse (K := K) z)
    (hnonneg : ∀ x j, 0 ≤ z x j) (hbounded : ∀ x j, z x j ≤ 1) (hC : 0 ≤ C) :
    actualPopulationSquaredLoss μ A z B u ≤
      ENNReal.ofReal (C * K * rankedFeatureTail (featurePrevalence μ z) σ m) := by
  simpa only [omittedFeaturePrevalence_rankedPrefix_eq] using
    hopt.loss_le_omitted_prevalence μ A z B u (rankedPrefixEmbedding σ hm) γ C
      hA hstable hz hsparse hnonneg hbounded hC

end PKG26AtomicFeatures
