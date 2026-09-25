import PKG26AtomicFeatures.AtomicRigidity
import PKG26AtomicFeatures.MesoscaleWidthThreeRecovery

/-!
# Perfect hierarchy and failure of richness

Source: the named `Violation of richness` remark in `sections/proofs.tex`.
For nonnegative, pointwise sparse codes, a perfectly hierarchical child and
parent exclude an open patch on a support containing the child but not the
parent. An explicit pair of normalized, stable factorizations shows that
the rigidity conclusion can fail when richness is omitted.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators Matrix

/-- A perfectly hierarchical pair prevents relatively open richness. The
pointwise sparsity assumption is important: a full `K`-coordinate support
containing the child and excluding its parent would require an additional
active coordinate. Taking closure cannot fill the resulting finite union
of coordinate hyperplanes. -/
theorem not_openKRich_of_perfect_hierarchy
    {X : Type*} {M K : ℕ} (z : X → FeatureVector M)
    (hK : 1 ≤ K) (hKM : K < M)
    (hsparse : KSparse (K := K) z) (hnonneg : ∀ x i, 0 ≤ z x i)
    (child parent : Fin M) (hne : child ≠ parent)
    (hhierarchy : ∀ x, 0 < z x child → 0 < z x parent) :
    ¬ OpenKRich (K := K) z := by
  classical
  have hchild : ({child} : Finset (Fin M)) ⊆ Finset.univ.erase parent := by
    simpa using hne
  have hsize : K ≤ (Finset.univ.erase parent : Finset (Fin M)).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ parent), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨S, hchildS, hSparent, hScard⟩ :=
    Finset.exists_subsuperset_card_eq hchild (by simpa using hK) hsize
  have hchildmem : child ∈ S := hchildS (by simp)
  have hparentnot : parent ∉ S := by
    intro hp
    exact (Finset.mem_erase.mp (hSparent hp)).1 rfl
  have hmissing : ∀ x, ∃ i ∈ S, z x i = 0 := by
    intro x
    by_contra! hfull
    have hchildpos : 0 < z x child := by
      rcases lt_or_eq_of_le (hnonneg x child) with h | h
      · exact h
      · exact False.elim ((hfull child hchildmem) h.symm)
    have hparentpos := hhierarchy x hchildpos
    have hsub : insert parent S ⊆ nonzeroSupport (z x) := by
      intro i hi
      rw [mem_nonzeroSupport_iff]
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ne_of_gt hparentpos
      · exact hfull i hi
    have hcard := (Finset.card_le_card hsub).trans (hsparse x)
    rw [Finset.card_insert_of_notMem hparentnot, hScard] at hcard
    omega
  let targets (i : {i // i ∈ S}) : Submodule ℝ (FeatureVector M) :=
    coordinateSpan (Finset.univ.erase i.1)
  have hcover : Set.range z ⊆ ⋃ i, (targets i : Set (FeatureVector M)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi, hzero⟩ := hmissing x
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hi⟩, mem_coordinateSpan_of_nonzeroSupport_subset ?_⟩
    intro j hj
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hji
    subst j
    exact (mem_nonzeroSupport_iff (z x) i).mp hj hzero
  have hclosure := closure_range_subset_iUnion_of_finite_submodules z targets hcover
  intro hrich
  obtain ⟨region, hopen, hnonempty, hregion⟩ := hrich S hScard
  let restricted (i : {i // i ∈ S}) : Submodule ℝ (coordinateSpan S) :=
    Submodule.comap (coordinateSpan S).subtype (targets i)
  have hrestricted : region ⊆ ⋃ i, (restricted i : Set (coordinateSpan S)) := by
    intro v hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hclosure (hregion v hv))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, hi⟩ :=
    exists_submodule_eq_top_of_open_cover restricted region hopen hnonempty hrestricted
  let e : coordinateSpan S :=
    ⟨Pi.single i.1 (1 : ℝ), canonicalVector_mem_coordinateSpan S i.2⟩
  have hemem : e ∈ restricted i := by
    rw [hi]
    exact Submodule.mem_top
  have hezero : (Pi.single i.1 (1 : ℝ) : FeatureVector M) i.1 = 0 :=
    eq_zero_of_mem_coordinateSpan_of_not_mem hemem (by simp)
  simpa using hezero

/-- Equal positive activations of a child and its parent, with one unused
coordinate. The input coefficient lies in the unit interval. -/
def hierarchySourceCode (t : Set.Icc (0 : ℝ) 1) : FeatureVector 3 :=
  ![(t : ℝ), (t : ℝ), 0]

/-- An orthogonal change of the first two normalized dictionary columns. -/
noncomputable def hierarchyAlternativeMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3/5, 4/5, 0; 4/5, -3/5, 0; 0, 0, 1]

/-- The same hierarchical ray has nonnegative two-sparse codes in the
alternative orthogonal dictionary. -/
noncomputable def hierarchyAlternativeCode (t : Set.Icc (0 : ℝ) 1) : FeatureVector 3 :=
  ![(7/5 : ℝ) * t, (1/5 : ℝ) * t, 0]

private theorem hierarchyAlternativeMatrix_mulVec (v : FeatureVector 3) :
    hierarchyAlternativeMatrix.mulVec v =
      ![(3/5 : ℝ) * v 0 + (4/5 : ℝ) * v 1,
        (4/5 : ℝ) * v 0 - (3/5 : ℝ) * v 1, v 2] := by
  ext i
  fin_cases i <;>
    simp [hierarchyAlternativeMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg] <;> ring

private theorem hierarchy_euclidean_norm_sq {n : ℕ} (v : Fin n → ℝ) :
    ‖representationToEuclidean n v‖ ^ 2 = ∑ i, v i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

theorem hierarchyAlternativeMatrix_unit :
    HasUnitEuclideanColumns hierarchyAlternativeMatrix := by
  intro j
  have hsq := hierarchy_euclidean_norm_sq (hierarchyAlternativeMatrix.col j)
  have hn := norm_nonneg (representationToEuclidean 3 (hierarchyAlternativeMatrix.col j))
  have hsum : (∑ i, hierarchyAlternativeMatrix.col j i ^ 2) = 1 := by
    fin_cases j <;>
      norm_num [hierarchyAlternativeMatrix, Matrix.col, Fin.sum_univ_succ]
  rw [hsum] at hsq
  nlinarith

/-- The alternative matrix preserves the Euclidean norm, so its stability
holds for every requested sparsity order at margin one. -/
theorem hierarchyAlternativeMatrix_stable (s : ℕ) :
    SparseLowerStable hierarchyAlternativeMatrix 1 s := by
  intro v _
  have hsq : ‖representationToEuclidean 3 (hierarchyAlternativeMatrix.mulVec v)‖ ^ 2 =
      ‖representationToEuclidean 3 v‖ ^ 2 := by
    rw [hierarchy_euclidean_norm_sq, hierarchy_euclidean_norm_sq,
      hierarchyAlternativeMatrix_mulVec]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change ((3/5 : ℝ) * v 0 + (4/5 : ℝ) * v 1) ^ 2 +
        (((4/5 : ℝ) * v 0 - (3/5 : ℝ) * v 1) ^ 2 + v 2 ^ 2) =
      v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2)
    ring
  simp only [one_mul]
  nlinarith [norm_nonneg (representationToEuclidean 3 v),
    norm_nonneg (representationToEuclidean 3 (hierarchyAlternativeMatrix.mulVec v))]

theorem hierarchySourceCode_sparse : KSparse (K := 2) hierarchySourceCode := by
  classical
  intro t
  have hsub : nonzeroSupport (hierarchySourceCode t) ⊆ ({0, 1} : Finset (Fin 3)) := by
    intro i hi
    fin_cases i <;> simp_all [hierarchySourceCode, nonzeroSupport]
  exact (Finset.card_le_card hsub).trans (by decide)

theorem hierarchyAlternativeCode_sparse : KSparse (K := 2) hierarchyAlternativeCode := by
  classical
  intro t
  have hsub : nonzeroSupport (hierarchyAlternativeCode t) ⊆ ({0, 1} : Finset (Fin 3)) := by
    intro i hi
    fin_cases i <;> simp_all [hierarchyAlternativeCode, nonzeroSupport]
  exact (Finset.card_le_card hsub).trans (by decide)

theorem hierarchySourceCode_nonneg (t : Set.Icc (0 : ℝ) 1) (i : Fin 3) :
    0 ≤ hierarchySourceCode t i := by
  have ht : 0 ≤ (t : ℝ) := t.property.1
  fin_cases i <;> simp [hierarchySourceCode, ht]

theorem hierarchyAlternativeCode_nonneg (t : Set.Icc (0 : ℝ) 1) (i : Fin 3) :
    0 ≤ hierarchyAlternativeCode t i := by
  have ht : 0 ≤ (t : ℝ) := t.property.1
  fin_cases i <;> dsimp [hierarchyAlternativeCode] <;> positivity

/-- Every source coefficient retains the atomic model's unit-cube bound. -/
theorem hierarchySourceCode_le_one (t : Set.Icc (0 : ℝ) 1) (i : Fin 3) :
    hierarchySourceCode t i ≤ 1 := by
  have ht : (t : ℝ) ≤ 1 := t.property.2
  fin_cases i <;> simp [hierarchySourceCode, ht]

theorem hierarchySourceCode_hierarchy (t : Set.Icc (0 : ℝ) 1) :
    0 < hierarchySourceCode t 0 → 0 < hierarchySourceCode t 1 := by
  simp [hierarchySourceCode]

theorem hierarchySourceCode_not_openKRich : ¬ OpenKRich (K := 2) hierarchySourceCode :=
  not_openKRich_of_perfect_hierarchy hierarchySourceCode (by norm_num) (by norm_num)
    hierarchySourceCode_sparse hierarchySourceCode_nonneg 0 1 (by decide)
    hierarchySourceCode_hierarchy

theorem hierarchy_factorizations_equal (t : Set.Icc (0 : ℝ) 1) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ).mulVec (hierarchySourceCode t) =
      hierarchyAlternativeMatrix.mulVec (hierarchyAlternativeCode t) := by
  rw [Matrix.one_mulVec, hierarchyAlternativeMatrix_mulVec]
  ext i
  fin_cases i <;> simp [hierarchySourceCode, hierarchyAlternativeCode] <;> ring

/-- The first alternative column has two nonzero coordinates and therefore
cannot be a column of the identity dictionary. -/
theorem hierarchy_pairs_not_permutation_equivalent :
    ¬ AtomicPairsPermutationEquivalent (1 : Matrix (Fin 3) (Fin 3) ℝ)
      hierarchySourceCode hierarchyAlternativeMatrix hierarchyAlternativeCode := by
  rintro ⟨permutation, hcolumns, _⟩
  have h := congrFun (hcolumns (0 : Fin 3)) (0 : Fin 3)
  change (3 / 5 : ℝ) = (if (0 : Fin 3) = permutation 0 then 1 else 0) at h
  split_ifs at h <;> norm_num at h

/-- The first alternative column cannot even be a nonzero scalar multiple
of an identity column. Thus the counterexample also refutes rigidity up to
permutation and scaling, as used by the current manuscript. -/
theorem hierarchy_pairs_not_scaling_equivalent :
    ¬ AtomicPairsEquivalent (1 : Matrix (Fin 3) (Fin 3) ℝ)
      hierarchySourceCode hierarchyAlternativeMatrix hierarchyAlternativeCode := by
  rintro ⟨permutation, scale, _, hcolumns, _⟩
  have h₀ := congrFun (hcolumns (0 : Fin 3)) (0 : Fin 3)
  have h₁ := congrFun (hcolumns (0 : Fin 3)) (1 : Fin 3)
  change (3 / 5 : ℝ) = scale 0 * (if (0 : Fin 3) = permutation 0 then 1 else 0) at h₀
  change (4 / 5 : ℝ) = scale 0 * (if (1 : Fin 3) = permutation 0 then 1 else 0) at h₁
  by_cases h : (0 : Fin 3) = permutation 0
  · rw [← h] at h₁
    norm_num at h₁
  · simp [h] at h₀

/-- Richness cannot simply be deleted from normalized rigidity. Both
dictionaries below have width three, sparsity two, and full stability margin
one, yet their exact nonnegative factorizations are not equivalent up to
permutation and scaling.
The source coefficients all remain in the unit cube.
This is an existence counterexample, not a universal failure assertion for
every hierarchical model. -/
theorem hierarchy_refutes_rigidity_without_richness :
    HasUnitEuclideanColumns (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
    HasUnitEuclideanColumns hierarchyAlternativeMatrix ∧
    SparseLowerStable (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 4 ∧
    SparseLowerStable hierarchyAlternativeMatrix 1 4 ∧
    KSparse (K := 2) hierarchySourceCode ∧
    KSparse (K := 2) hierarchyAlternativeCode ∧
    (∀ t i, 0 ≤ hierarchySourceCode t i) ∧
    (∀ t i, 0 ≤ hierarchyAlternativeCode t i) ∧
    (∀ t i, hierarchySourceCode t i ≤ 1) ∧
    (∀ t, (1 : Matrix (Fin 3) (Fin 3) ℝ).mulVec (hierarchySourceCode t) =
      hierarchyAlternativeMatrix.mulVec (hierarchyAlternativeCode t)) ∧
    (∀ t, 0 < hierarchySourceCode t 0 → 0 < hierarchySourceCode t 1) ∧
    ¬ OpenKRich (K := 2) hierarchySourceCode ∧
    ¬ AtomicPairsEquivalent (1 : Matrix (Fin 3) (Fin 3) ℝ)
      hierarchySourceCode hierarchyAlternativeMatrix hierarchyAlternativeCode :=
  ⟨identityDictionary_unit 3, hierarchyAlternativeMatrix_unit,
    identityDictionary_stable 3 4 1 le_rfl, hierarchyAlternativeMatrix_stable 4,
    hierarchySourceCode_sparse, hierarchyAlternativeCode_sparse,
    hierarchySourceCode_nonneg, hierarchyAlternativeCode_nonneg,
    hierarchySourceCode_le_one, hierarchy_factorizations_equal, hierarchySourceCode_hierarchy,
    hierarchySourceCode_not_openKRich, hierarchy_pairs_not_scaling_equivalent⟩

end PKG26AtomicFeatures
