import PKG26AtomicFeatures.StableSupportIntersections

/-!
# Selecting good supports from finite weighted loss

The weights need only be nonnegative; no probability normalization is needed.
All marginal, separation, and loss quantities below are actual finite sums.
A support is good when its weight is positive and its conditional loss is at
most the positive threshold. Strict total-loss bounds supply good supports,
including when total loss is zero and the relevant marginal is positive.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- Total loss of a finite weighted family of conditional losses. -/
noncomputable def weightedConditionalLoss {ι : Type*} [Fintype ι]
    (w loss : ι → ℝ) : ℝ := ∑ s, w s * loss s

/-- The total weight of a selected finite family. -/
noncomputable def supportFamilyWeight {ι : Type*}
    (w : ι → ℝ) (family : Finset ι) : ℝ := ∑ s ∈ family, w s

/-- Positive-weight supports whose conditional loss is below the threshold. -/
noncomputable def goodSupportIndices {ι : Type*} [Fintype ι]
    (w loss : ι → ℝ) (τ : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun s => 0 < w s ∧ loss s ≤ τ

@[simp] theorem mem_goodSupportIndices {ι : Type*} [Fintype ι]
    (w loss : ι → ℝ) (τ : ℝ) (s : ι) :
    s ∈ goodSupportIndices w loss τ ↔ 0 < w s ∧ loss s ≤ τ := by
  classical
  simp [goodSupportIndices]

/-- Total weight outside the good family. Zero-weight indices contribute
zero whether or not their conditional loss exceeds the threshold. -/
noncomputable def badSupportWeight {ι : Type*} [Fintype ι]
    (w loss : ι → ℝ) (τ : ℝ) : ℝ := by
  classical
  exact supportFamilyWeight w (Finset.univ \ goodSupportIndices w loss τ)

/-- Marginal weight of supports containing an atom. -/
noncomputable def supportMarginalWeight {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (i : Fin M) : ℝ := by
  classical
  exact supportFamilyWeight w (Finset.univ.filter fun s => i ∈ S s)

/-- Weight of supports containing `i` and excluding `j`. -/
noncomputable def supportSeparationWeight {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (i j : Fin M) : ℝ := by
  classical
  exact supportFamilyWeight w (Finset.univ.filter fun s => i ∈ S s ∧ j ∉ S s)

/-- All good supports containing the selected source atom. -/
noncomputable def goodContainingSupportIndices {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ : ℝ) (i : Fin M) : Finset ι := by
  classical
  exact (goodSupportIndices w loss τ).filter fun s => i ∈ S s

@[simp] theorem mem_goodContainingSupportIndices {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ : ℝ) (i : Fin M) (s : ι) :
    s ∈ goodContainingSupportIndices S w loss τ i ↔
      (0 < w s ∧ loss s ≤ τ) ∧ i ∈ S s := by
  classical
  simp [goodContainingSupportIndices]

theorem supportFamilyWeight_nonneg {ι : Type*} (w : ι → ℝ)
    (hw : ∀ s, 0 ≤ w s) (family : Finset ι) :
    0 ≤ supportFamilyWeight w family :=
  Finset.sum_nonneg fun s _ => hw s

theorem weightedConditionalLoss_nonneg {ι : Type*} [Fintype ι]
    (w loss : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s) :
    0 ≤ weightedConditionalLoss w loss :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hw s) (hloss s)

/-- If a selected family contains no good support, its weight times the
threshold is bounded by the actual total weighted loss. -/
theorem threshold_mul_familyWeight_le_loss_of_no_good
    {ι : Type*} [Fintype ι] (w loss : ι → ℝ) (τ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (family : Finset ι)
    (hno : ∀ s ∈ family, ¬ (0 < w s ∧ loss s ≤ τ)) :
    τ * supportFamilyWeight w family ≤ weightedConditionalLoss w loss := by
  classical
  unfold supportFamilyWeight weightedConditionalLoss
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ s ∈ family, w s * loss s := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hzero : w s = 0
      · simp [hzero]
      · have hpos : 0 < w s := lt_of_le_of_ne (hw s) (Ne.symm hzero)
        have hbad : τ < loss s := lt_of_not_ge fun h => hno s hs ⟨hpos, h⟩
        nlinarith
    _ ≤ ∑ s, w s * loss s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro s _ _
      exact mul_nonneg (hw s) (hloss s)

/-- Finite weighted Markov bound for supports outside the good family. -/
theorem threshold_mul_badSupportWeight_le_loss
    {ι : Type*} [Fintype ι] (w loss : ι → ℝ) (τ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s) :
    τ * badSupportWeight w loss τ ≤ weightedConditionalLoss w loss := by
  classical
  apply threshold_mul_familyWeight_le_loss_of_no_good w loss τ hw hloss
  intro s hs hgood
  exact (Finset.mem_sdiff.mp hs).2 ((mem_goodSupportIndices w loss τ s).mpr hgood)

theorem badSupportWeight_le_loss_div_threshold
    {ι : Type*} [Fintype ι] (w loss : ι → ℝ) (τ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s) (hτ : 0 < τ) :
    badSupportWeight w loss τ ≤ weightedConditionalLoss w loss / τ := by
  apply (le_div_iff₀ hτ).mpr
  simpa only [mul_comm] using threshold_mul_badSupportWeight_le_loss w loss τ hw hloss

/-- A family whose weight exceeds the loss budget divided by the threshold
must contain an actual positive-weight good support. -/
theorem exists_good_support_of_loss_lt_threshold_mul_weight
    {ι : Type*} [Fintype ι] (w loss : ι → ℝ) (τ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (family : Finset ι)
    (hsmall : weightedConditionalLoss w loss < τ * supportFamilyWeight w family) :
    ∃ s ∈ family, 0 < w s ∧ loss s ≤ τ := by
  by_contra hn
  have hno : ∀ s ∈ family, ¬ (0 < w s ∧ loss s ≤ τ) := by
    intro s hs hgood
    exact hn ⟨s, hs, hgood⟩
  exact (not_lt_of_ge
    (threshold_mul_familyWeight_le_loss_of_no_good w loss τ hw hloss family hno)) hsmall

/-- A marginal above the loss budget guarantees a good support containing
that coordinate. No positive lower bound on total loss is required. -/
theorem goodContainingSupportIndices_nonempty_of_marginal
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s) (hτ : 0 < τ)
    (i : Fin M)
    (hmargin : weightedConditionalLoss w loss / τ < supportMarginalWeight S w i) :
    (goodContainingSupportIndices S w loss τ i).Nonempty := by
  classical
  have hsmall : weightedConditionalLoss w loss < τ * supportMarginalWeight S w i := by
    have h := (div_lt_iff₀ hτ).mp hmargin
    simpa only [mul_comm] using h
  obtain ⟨s, hs, hgood⟩ := exists_good_support_of_loss_lt_threshold_mul_weight
    w loss τ hw hloss (Finset.univ.filter fun s => i ∈ S s) hsmall
  exact ⟨s, (mem_goodContainingSupportIndices S w loss τ i s).mpr
    ⟨hgood, (Finset.mem_filter.mp hs).2⟩⟩

/-- Sufficient separation mass supplies a good support containing `i` and
excluding `j`, with the exact strict total-loss boundary. -/
theorem exists_good_support_separating_of_loss_lt
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s) (hτ : 0 < τ)
    (i j : Fin M)
    (hsep : ρ * supportMarginalWeight S w i ≤ supportSeparationWeight S w i j)
    (hsmall : weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i) :
    ∃ s ∈ goodContainingSupportIndices S w loss τ i, j ∉ S s := by
  classical
  have hsmall' : weightedConditionalLoss w loss < τ * supportSeparationWeight S w i j := by
    have hmul := mul_le_mul_of_nonneg_left hsep hτ.le
    nlinarith
  obtain ⟨s, hs, hgood⟩ := exists_good_support_of_loss_lt_threshold_mul_weight
    w loss τ hw hloss (Finset.univ.filter fun s => i ∈ S s ∧ j ∉ S s) hsmall'
  have hmembers := (Finset.mem_filter.mp hs).2
  exact ⟨s, (mem_goodContainingSupportIndices S w loss τ i s).mpr
    ⟨hgood, hmembers.1⟩, hmembers.2⟩

/-- A separation-scale loss bound also makes the containing good family
nonempty when the separation fraction is at most one. -/
theorem goodContainingSupportIndices_nonempty_of_separation_scale
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s) (hτ : 0 < τ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (i : Fin M)
    (hsmall : weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i) :
    (goodContainingSupportIndices S w loss τ i).Nonempty := by
  apply goodContainingSupportIndices_nonempty_of_marginal S w loss τ hw hloss hτ i
  apply (div_lt_iff₀ hτ).mpr
  have hproduct : 0 < (ρ * τ) * supportMarginalWeight S w i :=
    lt_of_le_of_lt (weightedConditionalLoss_nonneg w loss hw hloss) hsmall
  have hp : 0 < supportMarginalWeight S w i :=
    (mul_pos_iff_of_pos_left (mul_pos hρ hτ)).mp hproduct
  have hmul := mul_le_mul_of_nonneg_right hρone (mul_nonneg hτ.le hp.le)
  nlinarith

/-- If every other atom can be separated from `i` with weight at least
`ρ pᵢ`, then loss strictly below `ρ τ pᵢ` leaves enough good supports to
isolate `i`. The conclusion includes nonemptiness, including the case where
there are no other source atoms to quantify over. -/
theorem good_support_intersection_eq_singleton_of_separation
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hτ : 0 < τ) (hρ : 0 < ρ) (hρone : ρ ≤ 1) (i : Fin M)
    (hsep : ∀ j, j ≠ i →
      ρ * supportMarginalWeight S w i ≤ supportSeparationWeight S w i j)
    (hsmall : weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i) :
    (goodContainingSupportIndices S w loss τ i).Nonempty ∧
      supportFamilyIntersection S (goodContainingSupportIndices S w loss τ i) = {i} := by
  classical
  refine ⟨goodContainingSupportIndices_nonempty_of_separation_scale
    S w loss τ ρ hw hloss hτ hρ hρone i hsmall, ?_⟩
  ext j
  constructor
  · intro hj
    apply Finset.mem_singleton.mpr
    by_contra hji
    obtain ⟨s, hs, hjs⟩ := exists_good_support_separating_of_loss_lt
      S w loss τ ρ hw hloss hτ i j (hsep j hji) hsmall
    exact hjs ((mem_supportFamilyIntersection S _ j).mp hj s hs)
  · intro hj
    rw [Finset.mem_singleton] at hj
    subst j
    apply (mem_supportFamilyIntersection S _ i).mpr
    intro s hs
    exact ((mem_goodContainingSupportIndices S w loss τ i s).mp hs).2

/-- Atoms that accompany `i` on every positive-weight support, expressed
through zero separation mass rather than an auxiliary support certificate. -/
noncomputable def forcedCompanionSet {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (i : Fin M) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun j => supportSeparationWeight S w i j = 0

@[simp] theorem mem_forcedCompanionSet {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (i j : Fin M) :
    j ∈ forcedCompanionSet S w i ↔ supportSeparationWeight S w i j = 0 := by
  classical
  simp [forcedCompanionSet]

/-- Zero separation mass forces co-occurrence on each positive-weight
support because every term in the separation sum is nonnegative. -/
theorem forcedCompanion_mem_of_positive_weight
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s)
    (i j : Fin M) (hj : j ∈ forcedCompanionSet S w i)
    (s : ι) (hs : 0 < w s) (hi : i ∈ S s) : j ∈ S s := by
  classical
  by_contra hjs
  have hzero := (mem_forcedCompanionSet S w i j).mp hj
  have hbound : w s ≤ supportSeparationWeight S w i j := by
    apply Finset.single_le_sum (fun t _ => hw t)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hi, hjs⟩
  linarith

/-- The zero-separation-mass definition agrees with co-occurrence on all
positive-weight supports; zero-weight supports impose no restriction. -/
theorem mem_forcedCompanionSet_iff_positive_weight_occurrence
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s)
    (i j : Fin M) :
    j ∈ forcedCompanionSet S w i ↔
      ∀ s, 0 < w s → i ∈ S s → j ∈ S s := by
  classical
  constructor
  · intro hj s hs hi
    exact forcedCompanion_mem_of_positive_weight S w hw i j hj s hs hi
  · intro hoccurs
    apply (mem_forcedCompanionSet S w i j).mpr
    unfold supportSeparationWeight supportFamilyWeight
    apply Finset.sum_eq_zero
    intro s hs
    have hmembers := (Finset.mem_filter.mp hs).2
    apply le_antisymm _ (hw s)
    exact le_of_not_gt fun hpos => hmembers.2 (hoccurs s hpos hmembers.1)

/-- Every source atom is its own forced companion. -/
theorem self_mem_forcedCompanionSet
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (i : Fin M) :
    i ∈ forcedCompanionSet S w i :=
  (mem_forcedCompanionSet_iff_positive_weight_occurrence S w hw i i).mpr
    (fun _ _ hi => hi)

/-- With separation mass bounded below for every non-companion, the
intersection of all good supports containing `i` is exactly its true forced
companion set. This retains non-singleton hierarchical structure. -/
theorem good_support_intersection_eq_forcedCompanionSet
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hτ : 0 < τ) (hρ : 0 < ρ) (hρone : ρ ≤ 1) (i : Fin M)
    (hsep : ∀ j, j ∉ forcedCompanionSet S w i →
      ρ * supportMarginalWeight S w i ≤ supportSeparationWeight S w i j)
    (hsmall : weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i) :
    (goodContainingSupportIndices S w loss τ i).Nonempty ∧
      supportFamilyIntersection S (goodContainingSupportIndices S w loss τ i) =
        forcedCompanionSet S w i := by
  classical
  refine ⟨goodContainingSupportIndices_nonempty_of_separation_scale
    S w loss τ ρ hw hloss hτ hρ hρone i hsmall, ?_⟩
  ext j
  constructor
  · intro hj
    by_contra hnot
    obtain ⟨s, hs, hjs⟩ := exists_good_support_separating_of_loss_lt
      S w loss τ ρ hw hloss hτ i j (hsep j hnot) hsmall
    exact hjs ((mem_supportFamilyIntersection S _ j).mp hj s hs)
  · intro hj
    apply (mem_supportFamilyIntersection S _ j).mpr
    intro s hs
    have hgood := (mem_goodContainingSupportIndices S w loss τ i s).mp hs
    exact forcedCompanion_mem_of_positive_weight S w hw i j hj s hgood.1.1 hgood.2

end PKG26AtomicFeatures
