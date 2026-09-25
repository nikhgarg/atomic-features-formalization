import PKG26AtomicFeatures.SupportPatternRigidity

/-!
# The inverse-decoder pattern for one parent and two children

A nonnegative invertible 3-by-3 decoder whose two parent-child column sums
are two-sparse has one common coordinate permutation. Its parent column
occupies only the parent coordinate, and each child column occupies only its
own coordinate and possibly the parent coordinate. This pattern preserves
all three feature-presence events on hierarchical nonnegative source codes.
-/

namespace PKG26AtomicFeatures

open Set Topology
open scoped BigOperators Matrix

private theorem parentChild_column_sum_support
    (C : Matrix (Fin 3) (Fin 3) ℝ) (p : Equiv.Perm (Fin 3))
    (hnonneg : ∀ i j, 0 ≤ C i j) (hdiag : ∀ j, 0 < C (p j) j)
    (k : Fin 3) (hk : k ≠ 0)
    (hcard : (nonzeroSupport (C.col 0 + C.col k)).card ≤ 2) :
    nonzeroSupport (C.col 0 + C.col k) = {p 0, p k} := by
  classical
  have hsubset : {p 0, p k} ⊆ nonzeroSupport (C.col 0 + C.col k) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · apply (mem_nonzeroSupport_iff _ _).mpr
      change C (p 0) 0 + C (p 0) k ≠ 0
      exact (add_pos_of_pos_of_nonneg (hdiag 0) (hnonneg _ _)).ne'
    · have hi' := Finset.mem_singleton.mp hi
      subst i
      apply (mem_nonzeroSupport_iff _ _).mpr
      change C (p k) 0 + C (p k) k ≠ 0
      exact (add_pos_of_nonneg_of_pos (hnonneg _ _) (hdiag k)).ne'
  have hne : p 0 ≠ p k := fun h => hk (p.injective h).symm
  exact (Finset.eq_of_subset_of_card_le hsubset (by simpa [hne] using hcard)).symm

private theorem nonnegative_column_support_subset_sum
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hnonneg : ∀ i j, 0 ≤ C i j) (a b : Fin 3) :
    nonzeroSupport (C.col a) ⊆ nonzeroSupport (C.col a + C.col b) := by
  intro i hi
  have hpos : 0 < C i a := lt_of_le_of_ne (hnonneg i a)
    (Ne.symm ((mem_nonzeroSupport_iff (C.col a) i).mp hi))
  exact (mem_nonzeroSupport_iff _ _).mpr
    (add_pos_of_pos_of_nonneg hpos (hnonneg i b)).ne'

/-- The support pattern itself implies preservation of feature presence,
with no restriction on coefficient magnitudes or the sign of unused entries
beyond the stated matrix nonnegativity. -/
theorem hierarchical_inverse_pattern_preserves_presence
    (C : Matrix (Fin 3) (Fin 3) ℝ) (p : Equiv.Perm (Fin 3))
    (hnonneg : ∀ i j, 0 ≤ C i j) (hdiag : ∀ j, 0 < C (p j) j)
    (hparent : nonzeroSupport (C.col 0) = {p 0})
    (hchild1 : nonzeroSupport (C.col 1) ⊆ {p 0, p 1})
    (hchild2 : nonzeroSupport (C.col 2) ⊆ {p 0, p 2})
    (z : FeatureVector 3) (hz : ∀ j, 0 ≤ z j)
    (hhierarchy : z 0 = 0 → z 1 = 0 ∧ z 2 = 0) :
    ∀ j, 0 < C.mulVec z (p j) ↔ 0 < z j := by
  classical
  have hparentzero (j : Fin 3) (hj : j ≠ 0) : C (p j) 0 = 0 := by
    by_contra hnot
    have hmem := (mem_nonzeroSupport_iff (C.col 0) (p j)).mpr hnot
    rw [hparent, Finset.mem_singleton] at hmem
    exact hj (p.injective hmem)
  have h12 : C (p 1) 2 = 0 := by
    by_contra hnot
    have hmem := hchild2 ((mem_nonzeroSupport_iff (C.col 2) (p 1)).mpr hnot)
    simp only [Finset.mem_insert, Finset.mem_singleton, p.injective.eq_iff] at hmem
    rcases hmem with h | h
    · exact (by decide : (1 : Fin 3) ≠ 0) h
    · exact (by decide : (1 : Fin 3) ≠ 2) h
  have h21 : C (p 2) 1 = 0 := by
    by_contra hnot
    have hmem := hchild1 ((mem_nonzeroSupport_iff (C.col 1) (p 2)).mpr hnot)
    simp only [Finset.mem_insert, Finset.mem_singleton, p.injective.eq_iff] at hmem
    rcases hmem with h | h
    · exact (by decide : (2 : Fin 3) ≠ 0) h
    · exact (by decide : (2 : Fin 3) ≠ 1) h
  have hrow1 : C.mulVec z (p 1) = C (p 1) 1 * z 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hparentzero 1 (by decide), h12]
  have hrow2 : C.mulVec z (p 2) = C (p 2) 2 * z 2 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hparentzero 2 (by decide), h21]
  have hlower (j : Fin 3) : C (p j) j * z j ≤ C.mulVec z (p j) := by
    change C (p j) j * z j ≤ ∑ k : Fin 3, C (p j) k * z k
    exact Finset.single_le_sum (fun k _ => mul_nonneg (hnonneg (p j) k) (hz k)) (Finset.mem_univ j)
  intro j
  constructor
  · intro hpos
    fin_cases j
    · change 0 < C.mulVec z (p 0) at hpos
      change 0 < z 0
      by_contra hnot
      have hz0 : z 0 = 0 := le_antisymm (le_of_not_gt hnot) (hz 0)
      obtain ⟨hz1, hz2⟩ := hhierarchy hz0
      have hzero : C.mulVec z (p 0) = 0 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hz0, hz1, hz2]
      simp only [hzero, lt_self_iff_false] at hpos
    · change 0 < C.mulVec z (p 1) at hpos
      change 0 < z 1
      rw [hrow1] at hpos
      exact (mul_pos_iff_of_pos_left (hdiag 1)).mp hpos
    · change 0 < C.mulVec z (p 2) at hpos
      change 0 < z 2
      rw [hrow2] at hpos
      exact (mul_pos_iff_of_pos_left (hdiag 2)).mp hpos
  · intro hzpos
    exact (mul_pos (hdiag j) hzpos).trans_le (hlower j)

/-- Invertibility, nonnegativity, and the two actual two-sparse column sums
force one hierarchy-compatible permutation of all decoder coordinates. -/
theorem exists_hierarchical_inverse_pattern
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hdet : C.det ≠ 0)
    (hnonneg : ∀ i j, 0 ≤ C i j)
    (hpair1 : (nonzeroSupport (C.col 0 + C.col 1)).card ≤ 2)
    (hpair2 : (nonzeroSupport (C.col 0 + C.col 2)).card ≤ 2) :
    ∃ p : Equiv.Perm (Fin 3),
      (∀ j, 0 < C (p j) j) ∧
      nonzeroSupport (C.col 0) = {p 0} ∧
      nonzeroSupport (C.col 1) ⊆ {p 0, p 1} ∧
      nonzeroSupport (C.col 2) ⊆ {p 0, p 2} ∧
      ∀ z : FeatureVector 3, (∀ j, 0 ≤ z j) →
        (z 0 = 0 → z 1 = 0 ∧ z 2 = 0) →
        ∀ j, 0 < C.mulVec z (p j) ↔ 0 < z j := by
  classical
  obtain ⟨p, hp⟩ := exists_permutation_nonzero_entries_of_det_ne_zero C hdet
  have hdiag (j) : 0 < C (p j) j := lt_of_le_of_ne (hnonneg _ _) (Ne.symm (hp j))
  have hsum1 := parentChild_column_sum_support C p hnonneg hdiag 1 (by decide) hpair1
  have hsum2 := parentChild_column_sum_support C p hnonneg hdiag 2 (by decide) hpair2
  have hparent1 := nonnegative_column_support_subset_sum C hnonneg 0 1
  have hparent2 := nonnegative_column_support_subset_sum C hnonneg 0 2
  rw [hsum1] at hparent1
  rw [hsum2] at hparent2
  have hparent : nonzeroSupport (C.col 0) = {p 0} := by
    ext i
    constructor
    · intro hi
      have hi1 := hparent1 hi
      have hi2 := hparent2 hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi1 hi2 ⊢
      rcases hi1 with h0 | h1
      · exact h0
      · rcases hi2 with h0 | h2
        · exact h0
        · have hfalse := p.injective (h1.symm.trans h2)
          exact ((by decide : (1 : Fin 3) ≠ 2) hfalse).elim
    · intro hi
      have heq := Finset.mem_singleton.mp hi
      subst i
      exact (mem_nonzeroSupport_iff _ _).mpr (hdiag 0).ne'
  have hchild1 : nonzeroSupport (C.col 1) ⊆ {p 0, p 1} := by
    have h := nonnegative_column_support_subset_sum C hnonneg 1 0
    rwa [add_comm, hsum1] at h
  have hchild2 : nonzeroSupport (C.col 2) ⊆ {p 0, p 2} := by
    have h := nonnegative_column_support_subset_sum C hnonneg 2 0
    rwa [add_comm, hsum2] at h
  exact ⟨p, hdiag, hparent, hchild1, hchild2,
    hierarchical_inverse_pattern_preserves_presence C p hnonneg hdiag hparent hchild1 hchild2⟩


/-- A source code with the specified parent and child coefficients. -/
noncomputable def hierarchicalParentChildCode (child : Fin 2) (a b : ℝ) : FeatureVector 3 :=
  Pi.single 0 a + Pi.single child.succ b

theorem hierarchicalParentChildCode_synthesis
    (C : Matrix (Fin 3) (Fin 3) ℝ) (child : Fin 2) (a b : ℝ) (i : Fin 3) :
    C.mulVec (hierarchicalParentChildCode child a b) i =
      a * C i 0 + b * C i child.succ := by
  simp [hierarchicalParentChildCode, Matrix.mulVec_add, Matrix.mulVec_single,
    op_smul_eq_smul, Matrix.col]

private theorem nonnegative_coefficients_of_open_square
    (a b : ℝ)
    (h : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ s * a + t * b) :
    0 ≤ a ∧ 0 ≤ b := by
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num⟩
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hclosedA : IsClosed {t : ℝ | 0 ≤ (1 / 2) * a + t * b} :=
    isClosed_le continuous_const (continuous_const.add (continuous_id.mul continuous_const))
  have hclosedB : IsClosed {s : ℝ | 0 ≤ s * a + (1 / 2) * b} :=
    isClosed_le continuous_const ((continuous_id.mul continuous_const).add continuous_const)
  have hA : 0 ≤ (1 / 2 : ℝ) * a + 0 * b :=
    closure_minimal (fun t ht => h (1 / 2) hhalf t ht) hclosedA hzero
  have hB : 0 ≤ (0 : ℝ) * a + (1 / 2) * b :=
    closure_minimal (fun s hs => h s hs (1 / 2) hhalf) hclosedB hzero
  constructor <;> nlinarith

/-- Mapping the two open positive coefficient squares into nonnegative
two-sparse codes already implies entrywise nonnegativity and both exact
column-sum sparsity bounds. The boundary-axis signs follow by continuity;
the sparsity bounds follow from the interior midpoint and homogeneity. -/
theorem hierarchical_inverse_assumptions_of_open_squares
    (C : Matrix (Fin 3) (Fin 3) ℝ)
    (hpatch : ∀ child : Fin 2, ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
      (∀ i, 0 ≤ C.mulVec (hierarchicalParentChildCode child a b) i) ∧
        (nonzeroSupport (C.mulVec (hierarchicalParentChildCode child a b))).card ≤ 2) :
    (∀ i j, 0 ≤ C i j) ∧
      (nonzeroSupport (C.col 0 + C.col 1)).card ≤ 2 ∧
      (nonzeroSupport (C.col 0 + C.col 2)).card ≤ 2 := by
  have hcolumns (child : Fin 2) (i : Fin 3) : 0 ≤ C i 0 ∧ 0 ≤ C i child.succ := by
    apply nonnegative_coefficients_of_open_square
    intro a ha b hb
    simpa only [hierarchicalParentChildCode_synthesis] using (hpatch child a ha b hb).1 i
  have hnonneg (i j : Fin 3) : 0 ≤ C i j := by
    fin_cases j
    · exact (hcolumns 0 i).1
    · exact (hcolumns 0 i).2
    · exact (hcolumns 1 i).2
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hpair (child : Fin 2) : (nonzeroSupport (C.col 0 + C.col child.succ)).card ≤ 2 := by
    have hmid := (hpatch child (1 / 2) hhalf (1 / 2) hhalf).2
    have hsupport : nonzeroSupport (C.mulVec (hierarchicalParentChildCode child (1 / 2) (1 / 2))) =
        nonzeroSupport (C.col 0 + C.col child.succ) := by
      ext i
      rw [mem_nonzeroSupport_iff, mem_nonzeroSupport_iff, hierarchicalParentChildCode_synthesis]
      change (1 / 2 : ℝ) * C i 0 + (1 / 2) * C i child.succ ≠ 0 ↔
        C i 0 + C i child.succ ≠ 0
      constructor
      · intro hn hz
        apply hn
        nlinarith
      · intro hn hz
        apply hn
        nlinarith
    rwa [hsupport] at hmid
  exact ⟨hnonneg, hpair 0, hpair 1⟩

/-- An actual invertible decoder which is nonnegative and two-sparse on
both open source squares has the hierarchy-compatible permutation and
preserves all source feature-presence events. -/
theorem exists_hierarchical_inverse_pattern_of_open_squares
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hdet : C.det ≠ 0)
    (hpatch : ∀ child : Fin 2, ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
      (∀ i, 0 ≤ C.mulVec (hierarchicalParentChildCode child a b) i) ∧
        (nonzeroSupport (C.mulVec (hierarchicalParentChildCode child a b))).card ≤ 2) :
    ∃ p : Equiv.Perm (Fin 3),
      (∀ j, 0 < C (p j) j) ∧
      nonzeroSupport (C.col 0) = {p 0} ∧
      nonzeroSupport (C.col 1) ⊆ {p 0, p 1} ∧
      nonzeroSupport (C.col 2) ⊆ {p 0, p 2} ∧
      ∀ z : FeatureVector 3, (∀ j, 0 ≤ z j) →
        (z 0 = 0 → z 1 = 0 ∧ z 2 = 0) →
        ∀ j, 0 < C.mulVec z (p j) ↔ 0 < z j := by
  obtain ⟨hnonneg, hpair1, hpair2⟩ := hierarchical_inverse_assumptions_of_open_squares C hpatch
  exact exists_hierarchical_inverse_pattern C hdet hnonneg hpair1 hpair2

end PKG26AtomicFeatures
