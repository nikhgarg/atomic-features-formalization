import PKG26AtomicFeatures.WeightedGoodSupports

/-!
# Exceptional companions in a selected support family

An exceptional companion of `i` occurs in the selected family, differs from
`i`, and never occurs there without `i`. Reverse separation bounds the sum
of these companions' marginal weights by the weight outside the selected
family, multiplied by the sparsity bound. Discarding supports that contain
an exceptional companion therefore incurs a dimension-independent weight
bound. No normalization of the nonnegative weights is needed.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- Other atoms occurring in the selected family only together with `i`. -/
noncomputable def exceptionalCompanionSet {ι : Type*} {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun j => j ≠ i ∧ (∃ s ∈ G, j ∈ S s) ∧
    ∀ s ∈ G, j ∈ S s → i ∈ S s

@[simp] theorem mem_exceptionalCompanionSet {ι : Type*} {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i j : Fin M) :
    j ∈ exceptionalCompanionSet S G i ↔
      j ≠ i ∧ (∃ s ∈ G, j ∈ S s) ∧ ∀ s ∈ G, j ∈ S s → i ∈ S s := by
  classical
  simp [exceptionalCompanionSet]

/-- Selected supports containing `i` and no exceptional companion of `i`. -/
noncomputable def eligibleSupportIndices {ι : Type*} {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M) : Finset ι := by
  classical
  exact G.filter fun s => i ∈ S s ∧ Disjoint (S s) (exceptionalCompanionSet S G i)

@[simp] theorem mem_eligibleSupportIndices {ι : Type*} {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M) (s : ι) :
    s ∈ eligibleSupportIndices S G i ↔
      s ∈ G ∧ i ∈ S s ∧ Disjoint (S s) (exceptionalCompanionSet S G i) := by
  classical
  simp [eligibleSupportIndices]

/-- Total weight outside a selected family. -/
noncomputable def excludedSupportWeight {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (G : Finset ι) : ℝ := by
  classical
  exact supportFamilyWeight w (Finset.univ \ G)

/-- Supports outside the selected family, or containing an exceptional
companion. This family also bounds the false-positive exceptional cases. -/
noncomputable def exceptionalSupportIndices {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M) : Finset ι := by
  classical
  exact Finset.univ.filter fun s =>
    s ∉ G ∨ ¬ Disjoint (S s) (exceptionalCompanionSet S G i)

/-- Supports containing `i` on which eligibility fails. -/
noncomputable def ineligibleContainingSupportIndices {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M) : Finset ι := by
  classical
  exact Finset.univ.filter fun s => i ∈ S s ∧ s ∉ eligibleSupportIndices S G i

@[simp] theorem mem_exceptionalSupportIndices {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M) (s : ι) :
    s ∈ exceptionalSupportIndices S G i ↔
      s ∉ G ∨ ¬ Disjoint (S s) (exceptionalCompanionSet S G i) := by
  classical
  simp [exceptionalSupportIndices]

@[simp] theorem mem_ineligibleContainingSupportIndices
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M) (s : ι) :
    s ∈ ineligibleContainingSupportIndices S G i ↔
      i ∈ S s ∧ s ∉ eligibleSupportIndices S G i := by
  classical
  simp [ineligibleContainingSupportIndices]

/-- An atom outside the exceptional set that occurs on a selected support
has a selected occurrence without `i`. -/
theorem exists_selected_support_excluding_of_not_exceptional
    {ι : Type*} {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i j : Fin M)
    (hji : j ≠ i) (hoccurs : ∃ s ∈ G, j ∈ S s)
    (hj : j ∉ exceptionalCompanionSet S G i) :
    ∃ s ∈ G, j ∈ S s ∧ i ∉ S s := by
  classical
  by_contra! hno
  apply hj
  exact (mem_exceptionalCompanionSet S G i j).mpr ⟨hji, hoccurs, hno⟩

/-- Every other atom on an eligible support has a selected support witness
containing that atom and excluding the target. -/
theorem exists_selected_support_excluding_of_eligible
    {ι : Type*} {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M)
    (s : ι) (hs : s ∈ eligibleSupportIndices S G i)
    (j : Fin M) (hjs : j ∈ S s) (hji : j ≠ i) :
    ∃ t ∈ G, j ∈ S t ∧ i ∉ S t := by
  have hparts := (mem_eligibleSupportIndices S G i s).mp hs
  exact exists_selected_support_excluding_of_not_exceptional S G i j hji
    ⟨s, hparts.1, hjs⟩ (Finset.disjoint_left.mp hparts.2.2 hjs)

/-- Exceptional atoms have positive marginal weight when every selected
support has positive weight. -/
theorem supportMarginalWeight_pos_of_exceptional
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (G : Finset ι) (i j : Fin M)
    (hw : ∀ s, 0 ≤ w s) (hG : ∀ s ∈ G, 0 < w s)
    (hj : j ∈ exceptionalCompanionSet S G i) :
    0 < supportMarginalWeight S w j := by
  classical
  obtain ⟨s, hs, hjs⟩ := ((mem_exceptionalCompanionSet S G i j).mp hj).2.1
  apply (hG s hs).trans_le
  exact Finset.single_le_sum (fun t _ => hw t)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hjs⟩)

/-- Summing reverse-separation weights counts at most `K` atoms on each
excluded support and counts none on any selected support. -/
theorem sum_exceptional_separationWeight_le
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (G : Finset ι) (i : Fin M)
    (hw : ∀ s, 0 ≤ w s) (hcard : ∀ s, (S s).card ≤ K) :
    (∑ j ∈ exceptionalCompanionSet S G i, supportSeparationWeight S w j i) ≤
      (K : ℝ) * excludedSupportWeight w G := by
  classical
  have hpoint (s : ι) :
      (∑ j ∈ exceptionalCompanionSet S G i,
        if j ∈ S s ∧ i ∉ S s then w s else 0) ≤
      if s ∉ G then (K : ℝ) * w s else 0 := by
    by_cases hs : s ∈ G
    · rw [if_neg (not_not.mpr hs)]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro j hj
      have hcontains := ((mem_exceptionalCompanionSet S G i j).mp hj).2.2 s hs
      simp only [show ¬ (j ∈ S s ∧ i ∉ S s) from fun h => h.2 (hcontains h.1), if_false]
    · rw [if_pos hs]
      calc
        _ = ∑ j ∈ (exceptionalCompanionSet S G i).filter
            (fun j => j ∈ S s ∧ i ∉ S s), w s := by rw [Finset.sum_filter]
        _ ≤ ∑ _j ∈ S s, w s := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            exact (Finset.mem_filter.mp hj).2.1
          · intro _ _ _
            exact hw s
        _ = ((S s).card : ℝ) * w s := by simp
        _ ≤ (K : ℝ) * w s :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard s) (hw s)
  calc
    _ = ∑ s, ∑ j ∈ exceptionalCompanionSet S G i,
        if j ∈ S s ∧ i ∉ S s then w s else 0 := by
      simp only [supportSeparationWeight, supportFamilyWeight, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ s, if s ∉ G then (K : ℝ) * w s else 0 := Finset.sum_le_sum fun s _ => hpoint s
    _ = (K : ℝ) * excludedSupportWeight w G := by
      simp only [excludedSupportWeight, supportFamilyWeight, Finset.mul_sum]
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ G)]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      rw [← Finset.sum_sdiff_eq_sub (Finset.subset_univ G)]
      congr 1
      ext s
      simp

/-- Reverse separation bounds the total marginal weight of exceptional
companions by sparsity times the excluded weight. -/
theorem exceptionalCompanion_marginalWeight_bound
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (G : Finset ι) (i : Fin M)
    (ρ : ℝ) (hw : ∀ s, 0 ≤ w s) (hcard : ∀ s, (S s).card ≤ K)
    (hsep : ∀ j ∈ exceptionalCompanionSet S G i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i) :
    ρ * (∑ j ∈ exceptionalCompanionSet S G i, supportMarginalWeight S w j) ≤
      (K : ℝ) * excludedSupportWeight w G := by
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum hsep).trans (sum_exceptional_separationWeight_le S w G i hw hcard)

/-- The weight outside a selected family is its finite indicator sum. -/
private theorem excludedSupportWeight_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (G : Finset ι) :
    excludedSupportWeight w G = ∑ s, if s ∉ G then w s else 0 := by
  classical
  unfold excludedSupportWeight supportFamilyWeight
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext s
    simp
  · intro s _
    rfl

/-- The union bound charges excluded supports once and each exceptional
companion by its full marginal weight. -/
theorem exceptionalSupportWeight_le_excluded_add_marginals
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (G : Finset ι) (i : Fin M)
    (hw : ∀ s, 0 ≤ w s) :
    supportFamilyWeight w (exceptionalSupportIndices S G i) ≤
      excludedSupportWeight w G +
        ∑ j ∈ exceptionalCompanionSet S G i, supportMarginalWeight S w j := by
  classical
  have hpoint (s : ι) :
      (if s ∉ G ∨ ¬ Disjoint (S s) (exceptionalCompanionSet S G i) then w s else 0) ≤
        (if s ∉ G then w s else 0) +
          ∑ j ∈ exceptionalCompanionSet S G i, if j ∈ S s then w s else 0 := by
    have hnonneg : 0 ≤ ∑ j ∈ exceptionalCompanionSet S G i,
        if j ∈ S s then w s else 0 :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> first | exact hw s | exact le_rfl
    by_cases hs : s ∈ G
    · by_cases hd : Disjoint (S s) (exceptionalCompanionSet S G i)
      · simpa only [hs, not_true_eq_false, hd, or_self, if_false, zero_add] using hnonneg
      · obtain ⟨j, hjs, hj⟩ := Finset.not_disjoint_iff.mp hd
        have hsingle := Finset.single_le_sum
          (fun k (_ : k ∈ exceptionalCompanionSet S G i) =>
            show 0 ≤ (if k ∈ S s then w s else 0) by
              split_ifs <;> first | exact hw s | exact le_rfl) hj
        simpa only [hs, not_true_eq_false, hd, not_false_eq_true, or_true,
          if_true, if_false, zero_add, hjs] using hsingle
    · simpa only [hs, not_false_eq_true, true_or, if_true] using
        (le_add_of_nonneg_right hnonneg : w s ≤ w s + _)
  calc
    _ = ∑ s, if s ∉ G ∨ ¬ Disjoint (S s) (exceptionalCompanionSet S G i)
        then w s else 0 := by
      simp only [exceptionalSupportIndices, supportFamilyWeight, Finset.sum_filter]
    _ ≤ ∑ s, ((if s ∉ G then w s else 0) +
        ∑ j ∈ exceptionalCompanionSet S G i, if j ∈ S s then w s else 0) :=
      Finset.sum_le_sum fun s _ => hpoint s
    _ = excludedSupportWeight w G +
        ∑ j ∈ exceptionalCompanionSet S G i, supportMarginalWeight S w j := by
      rw [Finset.sum_add_distrib, ← excludedSupportWeight_eq_sum, Finset.sum_comm]
      simp only [supportMarginalWeight, supportFamilyWeight, Finset.sum_filter]

/-- Reverse separation and sparsity bound the combined excluded and
exceptional-support weight without any dependence on the number of atoms. -/
theorem exceptionalSupportWeight_le
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (G : Finset ι) (i : Fin M)
    (ρ : ℝ) (hw : ∀ s, 0 ≤ w s) (hcard : ∀ s, (S s).card ≤ K) (hρ : 0 < ρ)
    (hsep : ∀ j ∈ exceptionalCompanionSet S G i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i) :
    supportFamilyWeight w (exceptionalSupportIndices S G i) ≤
      (1 + (K : ℝ) / ρ) * excludedSupportWeight w G := by
  have hcomp := exceptionalCompanion_marginalWeight_bound S w G i ρ hw hcard hsep
  have hmarg : (∑ j ∈ exceptionalCompanionSet S G i, supportMarginalWeight S w j) ≤
      (K : ℝ) / ρ * excludedSupportWeight w G := by
    calc
      _ ≤ ((K : ℝ) * excludedSupportWeight w G) / ρ :=
        (le_div_iff₀ hρ).mpr (by simpa only [mul_comm] using hcomp)
      _ = (K : ℝ) / ρ * excludedSupportWeight w G := by ring
  calc
    _ ≤ excludedSupportWeight w G +
        ∑ j ∈ exceptionalCompanionSet S G i, supportMarginalWeight S w j :=
      exceptionalSupportWeight_le_excluded_add_marginals S w G i hw
    _ ≤ excludedSupportWeight w G + (K : ℝ) / ρ * excludedSupportWeight w G :=
      add_le_add le_rfl hmarg
    _ = (1 + (K : ℝ) / ρ) * excludedSupportWeight w G := by ring

/-- Failure of eligibility on a support containing `i` is included in the
combined excluded-or-exceptional family. -/
theorem ineligibleContainingSupportIndices_subset_exceptional
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (G : Finset ι) (i : Fin M) :
    ineligibleContainingSupportIndices S G i ⊆ exceptionalSupportIndices S G i := by
  intro s hs
  have hparts := (mem_ineligibleContainingSupportIndices S G i s).mp hs
  apply (mem_exceptionalSupportIndices S G i s).mpr
  by_cases hG : s ∈ G
  · right
    intro hd
    exact hparts.2 ((mem_eligibleSupportIndices S G i s).mpr ⟨hG, hparts.1, hd⟩)
  · exact Or.inl hG

/-- The total containing weight discarded by eligibility is at most
`(1 + K / ρ)` times the excluded weight. -/
theorem ineligibleContainingSupportWeight_le
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (G : Finset ι) (i : Fin M)
    (ρ : ℝ) (hw : ∀ s, 0 ≤ w s) (hcard : ∀ s, (S s).card ≤ K) (hρ : 0 < ρ)
    (hsep : ∀ j ∈ exceptionalCompanionSet S G i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i) :
    supportFamilyWeight w (ineligibleContainingSupportIndices S G i) ≤
      (1 + (K : ℝ) / ρ) * excludedSupportWeight w G := by
  apply le_trans _ (exceptionalSupportWeight_le S w G i ρ hw hcard hρ hsep)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (ineligibleContainingSupportIndices_subset_exceptional S G i) (fun s _ _ => hw s)

/-- Eligible and ineligible containing supports partition the marginal. -/
theorem supportMarginalWeight_eq_eligible_add_ineligible
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (G : Finset ι) (i : Fin M) :
    supportMarginalWeight S w i = supportFamilyWeight w (eligibleSupportIndices S G i) +
      supportFamilyWeight w (ineligibleContainingSupportIndices S G i) := by
  classical
  have hsubset : eligibleSupportIndices S G i ⊆ Finset.univ.filter (fun s => i ∈ S s) := by
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s,
      ((mem_eligibleSupportIndices S G i s).mp hs).2.1⟩
  have hfamily : ineligibleContainingSupportIndices S G i =
      (Finset.univ.filter fun s => i ∈ S s) \ eligibleSupportIndices S G i := by
    ext s
    simp
  simp only [supportMarginalWeight, supportFamilyWeight, hfamily]
  rw [Finset.sum_sdiff_eq_sub hsubset]
  ring

/-- Eligible supports retain the target marginal up to the controlled
exceptional weight. -/
theorem supportMarginalWeight_sub_excluded_le_eligibleWeight
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w : ι → ℝ) (G : Finset ι) (i : Fin M)
    (ρ : ℝ) (hw : ∀ s, 0 ≤ w s) (hcard : ∀ s, (S s).card ≤ K) (hρ : 0 < ρ)
    (hsep : ∀ j ∈ exceptionalCompanionSet S G i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i) :
    supportMarginalWeight S w i - (1 + (K : ℝ) / ρ) * excludedSupportWeight w G ≤
      supportFamilyWeight w (eligibleSupportIndices S G i) := by
  have hbound := ineligibleContainingSupportWeight_le S w G i ρ hw hcard hρ hsep
  have hpartition := supportMarginalWeight_eq_eligible_add_ineligible S w G i
  linarith

@[simp] theorem excludedSupportWeight_goodSupportIndices
    {ι : Type*} [Fintype ι] (w loss : ι → ℝ) (τ : ℝ) :
    excludedSupportWeight w (goodSupportIndices w loss τ) = badSupportWeight w loss τ := rfl

/-- The exceptional-companion estimate specialized to positive-weight,
low-loss supports and the actual finite weighted loss. -/
theorem exceptionalCompanion_marginalWeight_goodSupport_bound
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ) (i : Fin M)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hcard : ∀ s, (S s).card ≤ K) (hτ : 0 < τ)
    (hsep : ∀ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i) :
    ρ * (∑ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i,
      supportMarginalWeight S w j) ≤ (K : ℝ) * (weightedConditionalLoss w loss / τ) := by
  have hbound := exceptionalCompanion_marginalWeight_bound S w
    (goodSupportIndices w loss τ) i ρ hw hcard hsep
  rw [excludedSupportWeight_goodSupportIndices] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (badSupportWeight_le_loss_div_threshold w loss τ hw hloss hτ) (Nat.cast_nonneg K))

/-- The combined excluded-or-exceptional weight is controlled by actual
weighted loss, with the same constant independent of the support count. -/
theorem exceptionalSupportWeight_goodSupport_le_loss
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ) (i : Fin M)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hcard : ∀ s, (S s).card ≤ K) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hsep : ∀ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i) :
    supportFamilyWeight w (exceptionalSupportIndices S (goodSupportIndices w loss τ) i) ≤
      (1 + (K : ℝ) / ρ) * (weightedConditionalLoss w loss / τ) := by
  have hbound := exceptionalSupportWeight_le S w (goodSupportIndices w loss τ) i
    ρ hw hcard hρ hsep
  rw [excludedSupportWeight_goodSupportIndices] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (badSupportWeight_le_loss_div_threshold w loss τ hw hloss hτ) (by positivity))

/-- Ineligible containing weight is bounded by the actual weighted loss. -/
theorem ineligibleContainingSupportWeight_goodSupport_le_loss
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ) (i : Fin M)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hcard : ∀ s, (S s).card ≤ K) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hsep : ∀ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i) :
    supportFamilyWeight w
        (ineligibleContainingSupportIndices S (goodSupportIndices w loss τ) i) ≤
      (1 + (K : ℝ) / ρ) * (weightedConditionalLoss w loss / τ) := by
  apply le_trans _ (exceptionalSupportWeight_goodSupport_le_loss S w loss τ ρ i
    hw hloss hcard hτ hρ hsep)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (ineligibleContainingSupportIndices_subset_exceptional S (goodSupportIndices w loss τ) i)
    (fun s _ _ => hw s)

/-- Eligibility at the loss threshold retains the marginal minus the
controlled loss budget. -/
theorem supportMarginalWeight_sub_loss_le_eligibleWeight
    {ι : Type*} [Fintype ι] {M K : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ ρ : ℝ) (i : Fin M)
    (hw : ∀ s, 0 ≤ w s) (hloss : ∀ s, 0 ≤ loss s)
    (hcard : ∀ s, (S s).card ≤ K) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hsep : ∀ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i) :
    supportMarginalWeight S w i -
        (1 + (K : ℝ) / ρ) * (weightedConditionalLoss w loss / τ) ≤
      supportFamilyWeight w (eligibleSupportIndices S (goodSupportIndices w loss τ) i) := by
  have hbound := ineligibleContainingSupportWeight_goodSupport_le_loss
    S w loss τ ρ i hw hloss hcard hτ hρ hsep
  have hpartition := supportMarginalWeight_eq_eligible_add_ineligible
    S w (goodSupportIndices w loss τ) i
  linarith

/-- The geometric witness from an eligible low-loss support has positive
weight and conditional loss at most the same threshold. -/
theorem exists_good_support_excluding_of_eligible
    {ι : Type*} [Fintype ι] {M : ℕ}
    (S : ι → Finset (Fin M)) (w loss : ι → ℝ) (τ : ℝ) (i : Fin M)
    (s : ι) (hs : s ∈ eligibleSupportIndices S (goodSupportIndices w loss τ) i)
    (j : Fin M) (hjs : j ∈ S s) (hji : j ≠ i) :
    ∃ t, 0 < w t ∧ loss t ≤ τ ∧ j ∈ S t ∧ i ∉ S t := by
  obtain ⟨t, ht, hjt, hit⟩ := exists_selected_support_excluding_of_eligible
    S (goodSupportIndices w loss τ) i s hs j hjs hji
  have hgood := (mem_goodSupportIndices w loss τ t).mp ht
  exact ⟨t, hgood.1, hgood.2, hjt, hit⟩

end PKG26AtomicFeatures
