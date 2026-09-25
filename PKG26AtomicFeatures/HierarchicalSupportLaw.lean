import PKG26AtomicFeatures.WeightedGoodSupports
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite hierarchical support laws

A parent-support sample is paired with a uniformly chosen full vector of
binary child choices. Choices on inactive parents may duplicate the resulting
support but retain their actual probability weights. Atoms are indexed by
`Fin (N * 3)`, with parent role zero and two child roles one and two.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- The parent atom in a three-atom family. -/
def hierarchicalParent {N : ℕ} (i : Fin N) : Fin (N * 3) :=
  finProdFinEquiv (i, 0)

/-- One of the two child atoms in a three-atom family. -/
def hierarchicalChild {N : ℕ} (i : Fin N) (k : Fin 2) : Fin (N * 3) :=
  finProdFinEquiv (i, k.succ)

/-- Each selected family contributes its parent and the chosen child. -/
def hierarchicalSupport {N : ℕ} (P : Finset (Fin N)) (choice : Fin N → Fin 2) :
    Finset (Fin (N * 3)) :=
  P.image hierarchicalParent ∪ P.image (fun i => hierarchicalChild i (choice i))

@[simp] theorem hierarchicalParent_eq_iff {N : ℕ} (i j : Fin N) :
    hierarchicalParent i = hierarchicalParent j ↔ i = j := by
  simp [hierarchicalParent]

@[simp] theorem hierarchicalChild_eq_iff {N : ℕ} (i j : Fin N) (k l : Fin 2) :
    hierarchicalChild i k = hierarchicalChild j l ↔ i = j ∧ k = l := by
  simp [hierarchicalChild]

@[simp] theorem hierarchicalParent_ne_child {N : ℕ} (i j : Fin N) (k : Fin 2) :
    hierarchicalParent i ≠ hierarchicalChild j k := by
  intro h
  have hpair := finProdFinEquiv.injective h
  have hzero : (0 : Fin 3) = k.succ := congrArg Prod.snd hpair
  have hval := congrArg Fin.val hzero
  simp at hval

@[simp] theorem hierarchicalChild_ne_parent {N : ℕ} (i j : Fin N) (k : Fin 2) :
    hierarchicalChild i k ≠ hierarchicalParent j :=
  Ne.symm (hierarchicalParent_ne_child j i k)

@[simp] theorem mem_hierarchicalSupport_parent {N : ℕ}
    (P : Finset (Fin N)) (choice : Fin N → Fin 2) (i : Fin N) :
    hierarchicalParent i ∈ hierarchicalSupport P choice ↔ i ∈ P := by
  simp [hierarchicalSupport]

@[simp] theorem mem_hierarchicalSupport_child {N : ℕ}
    (P : Finset (Fin N)) (choice : Fin N → Fin 2) (i : Fin N) (k : Fin 2) :
    hierarchicalChild i k ∈ hierarchicalSupport P choice ↔ i ∈ P ∧ choice i = k := by
  simp [hierarchicalSupport]

/-- The two images contain distinct atoms and are mutually disjoint. -/
theorem hierarchicalSupport_card {N : ℕ}
    (P : Finset (Fin N)) (choice : Fin N → Fin 2) :
    (hierarchicalSupport P choice).card = 2 * P.card := by
  have hparent : Function.Injective (@hierarchicalParent N) :=
    fun i j h => (hierarchicalParent_eq_iff i j).mp h
  have hchild : Function.Injective (fun i => hierarchicalChild i (choice i)) :=
    fun i j h => ((hierarchicalChild_eq_iff i j _ _).mp h).1
  have hdisjoint : Disjoint (P.image hierarchicalParent)
      (P.image fun i => hierarchicalChild i (choice i)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    exact hierarchicalChild_ne_parent j i (choice j) hj
  rw [hierarchicalSupport, Finset.card_union_of_disjoint hdisjoint,
    Finset.card_image_of_injective P hparent, Finset.card_image_of_injective P hchild]
  omega

/-- The hierarchy has exactly twice as many atoms as active parents. -/
theorem hierarchicalSupport_card_of_parent_card {N L : ℕ}
    (P : Finset (Fin N)) (choice : Fin N → Fin 2) (hP : P.card = L) :
    (hierarchicalSupport P choice).card = 2 * L := by
  rw [hierarchicalSupport_card, hP]

/-- The actual support family, indexed by the parent sample and all binary choices. -/
def hierarchicalSupportFamily {ι : Type*} {N : ℕ}
    (P : ι → Finset (Fin N)) (sample : ι × (Fin N → Fin 2)) : Finset (Fin (N * 3)) :=
  hierarchicalSupport (P sample.1) sample.2

/-- Independent fair full child choices split each parent sample's mass
uniformly over all binary vectors. -/
noncomputable def hierarchicalSupportWeight {ι : Type*} {N : ℕ}
    (w : ι → ℝ) (sample : ι × (Fin N → Fin 2)) : ℝ :=
  w sample.1 / Fintype.card (Fin N → Fin 2)

theorem hierarchicalSupportWeight_nonneg {ι : Type*} {N : ℕ}
    (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (sample : ι × (Fin N → Fin 2)) :
    0 ≤ hierarchicalSupportWeight w sample :=
  div_nonneg (hw _) (Nat.cast_nonneg _)

private theorem choice_card_pos (N : ℕ) : 0 < (Fintype.card (Fin N → Fin 2) : ℝ) := by
  exact_mod_cast Fintype.card_pos

private theorem sum_choice_weight (N : ℕ) (a : ℝ) :
    (∑ _choice : Fin N → Fin 2, a / Fintype.card (Fin N → Fin 2)) = a := by
  have hcard := (choice_card_pos N).ne'
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- A single coordinate of the uniform full choice vector is exactly fair. -/
theorem sum_choice_weight_eq_half {N : ℕ} (i : Fin N) (k : Fin 2) (a : ℝ) :
    (∑ choice : Fin N → Fin 2,
      if choice i = k then a / Fintype.card (Fin N → Fin 2) else 0) = a / 2 := by
  classical
  let Other := {j : Fin N // j ≠ i} → Fin 2
  let split := Equiv.piSplitAt i (fun _ : Fin N => Fin 2)
  have hsum := Fintype.sum_equiv split
    (fun choice => if choice i = k then a / (Fintype.card (Fin N → Fin 2) : ℝ) else 0)
    (fun pair : Fin 2 × Other => if pair.1 = k then
      a / (Fintype.card (Fin N → Fin 2) : ℝ) else 0) (fun _ => rfl)
  rw [hsum, Fintype.sum_prod_type]
  change (∑ j : Fin 2, ∑ _ : Other,
    if j = k then a / (Fintype.card (Fin N → Fin 2) : ℝ) else 0) = a / 2
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hcard : Fintype.card (Fin N → Fin 2) = 2 * Fintype.card Other := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr split
  have hpos : 0 < (Fintype.card Other : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [hcard, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

private theorem hierarchical_parent_event_weight
    {ι : Type*} [Fintype ι] {N : ℕ} (w : ι → ℝ) (E : ι → Prop) [DecidablePred E] :
    (∑ sample : ι × (Fin N → Fin 2),
      if E sample.1 then hierarchicalSupportWeight w sample else 0) =
      ∑ s, if E s then w s else 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : E s
  · simp only [hs, if_true, hierarchicalSupportWeight]
    exact sum_choice_weight N (w s)
  · simp only [hs, if_false, Finset.sum_const_zero]

private theorem hierarchical_child_event_weight
    {ι : Type*} [Fintype ι] {N : ℕ} (w : ι → ℝ) (E : ι → Prop) [DecidablePred E]
    (i : Fin N) (k : Fin 2) :
    (∑ sample : ι × (Fin N → Fin 2),
      if E sample.1 ∧ sample.2 i = k then hierarchicalSupportWeight w sample else 0) =
      (∑ s, if E s then w s else 0) / 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : E s
  · simp only [hs, true_and, if_true, hierarchicalSupportWeight]
    exact sum_choice_weight_eq_half i k (w s)
  · simp only [hs, false_and, if_false, Finset.sum_const_zero, zero_div]

/-- The finite hierarchy retains normalized total probability. -/
theorem hierarchicalSupportWeight_sum_one
    {ι : Type*} [Fintype ι] {N : ℕ} (w : ι → ℝ) (hsum : ∑ s, w s = 1) :
    ∑ sample : ι × (Fin N → Fin 2), hierarchicalSupportWeight w sample = 1 := by
  have h := hierarchical_parent_event_weight (N := N) w (fun _ => True)
  simpa only [if_true, hsum] using h

/-- Parent atoms have exactly the original parent-support marginal. -/
theorem hierarchical_parent_marginal
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (i : Fin N) :
    supportMarginalWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
        (hierarchicalParent i) = supportMarginalWeight P w i := by
  classical
  simp only [supportMarginalWeight, supportFamilyWeight, Finset.sum_filter,
    hierarchicalSupportFamily, mem_hierarchicalSupport_parent]
  exact hierarchical_parent_event_weight w (fun s => i ∈ P s)

/-- Each child has exactly half of its parent's marginal. -/
theorem hierarchical_child_marginal
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (i : Fin N) (k : Fin 2) :
    supportMarginalWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
        (hierarchicalChild i k) = supportMarginalWeight P w i / 2 := by
  classical
  simp only [supportMarginalWeight, supportFamilyWeight, Finset.sum_filter,
    hierarchicalSupportFamily, mem_hierarchicalSupport_child]
  exact hierarchical_child_event_weight w (fun s => i ∈ P s) i k

/-- The parent family of an arbitrary indexed atom. -/
def hierarchicalAtomFamily {N : ℕ} (a : Fin (N * 3)) : Fin N :=
  (finProdFinEquiv.symm a).1

@[simp] theorem hierarchicalAtomFamily_parent {N : ℕ} (i : Fin N) :
    hierarchicalAtomFamily (hierarchicalParent i) = i := by
  simp [hierarchicalAtomFamily, hierarchicalParent]

@[simp] theorem hierarchicalAtomFamily_child {N : ℕ} (i : Fin N) (k : Fin 2) :
    hierarchicalAtomFamily (hierarchicalChild i k) = i := by
  simp [hierarchicalAtomFamily, hierarchicalChild]

/-- Any active atom belongs to a selected parent family. -/
theorem hierarchicalAtomFamily_mem_of_mem {N : ℕ}
    (P : Finset (Fin N)) (choice : Fin N → Fin 2) (a : Fin (N * 3))
    (ha : a ∈ hierarchicalSupport P choice) : hierarchicalAtomFamily a ∈ P := by
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    simpa using hi
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    simpa using hi

/-- Every atom is either the parent or one of its two children. -/
theorem hierarchical_atom_cases {N : ℕ} (a : Fin (N * 3)) :
    (∃ i, a = hierarchicalParent i) ∨ (∃ i k, a = hierarchicalChild i k) := by
  obtain ⟨⟨i, r⟩, rfl⟩ := finProdFinEquiv.surjective a
  fin_cases r
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, 0, rfl⟩
  · exact Or.inr ⟨i, 1, rfl⟩

private theorem indicator_sum_mono {α : Type*} [Fintype α]
    (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) (E F : α → Prop)
    [DecidablePred E] [DecidablePred F] (hEF : ∀ a, E a → F a) :
    (∑ a, if E a then v a else 0) ≤ ∑ a, if F a then v a else 0 := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hE : E a
  · simp only [hE, hEF a hE, if_true, le_refl]
  · simp only [hE, if_false]
    split_ifs <;> simp_all

/-- Omitting a target's parent family separates it from any selected parent. -/
theorem hierarchical_parent_separation_lower
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s)
    (i : Fin N) (a : Fin (N * 3)) :
    supportSeparationWeight P w i (hierarchicalAtomFamily a) ≤
      supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
        (hierarchicalParent i) a := by
  classical
  unfold supportSeparationWeight supportFamilyWeight
  simp only [Finset.sum_filter]
  rw [← hierarchical_parent_event_weight (N := N) w
    (fun s => i ∈ P s ∧ hierarchicalAtomFamily a ∉ P s)]
  apply indicator_sum_mono _ (hierarchicalSupportWeight_nonneg w hw)
  intro sample hs
  refine ⟨(mem_hierarchicalSupport_parent _ _ _).mpr hs.1, ?_⟩
  intro ha
  exact hs.2 (hierarchicalAtomFamily_mem_of_mem _ _ _ ha)

/-- A prescribed child choice keeps exactly half the separating parent mass. -/
theorem hierarchical_child_separation_lower
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s)
    (i : Fin N) (k : Fin 2) (a : Fin (N * 3)) :
    supportSeparationWeight P w i (hierarchicalAtomFamily a) / 2 ≤
      supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
        (hierarchicalChild i k) a := by
  classical
  unfold supportSeparationWeight supportFamilyWeight
  simp only [Finset.sum_filter]
  rw [← hierarchical_child_event_weight w
    (fun s => i ∈ P s ∧ hierarchicalAtomFamily a ∉ P s) i k]
  apply indicator_sum_mono _ (hierarchicalSupportWeight_nonneg w hw)
  intro sample hs
  refine ⟨(mem_hierarchicalSupport_child _ _ _ _).mpr ⟨hs.1.1, hs.2⟩, ?_⟩
  intro ha
  exact hs.1.2 (hierarchicalAtomFamily_mem_of_mem _ _ _ ha)

/-- Within a family, the parent is present without a prescribed child on
exactly the other half of the family's samples. -/
theorem hierarchical_parent_child_separation
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (i : Fin N) (k : Fin 2) :
    supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
      (hierarchicalParent i) (hierarchicalChild i k) = supportMarginalWeight P w i / 2 := by
  classical
  have hsplit : supportSeparationWeight (hierarchicalSupportFamily P)
        (hierarchicalSupportWeight w) (hierarchicalParent i) (hierarchicalChild i k) +
      supportMarginalWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
        (hierarchicalChild i k) =
      supportMarginalWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
        (hierarchicalParent i) := by
    simp only [supportSeparationWeight, supportMarginalWeight, supportFamilyWeight,
      Finset.sum_filter, hierarchicalSupportFamily, mem_hierarchicalSupport_parent,
      mem_hierarchicalSupport_child]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro sample _
    by_cases hi : i ∈ P sample.1 <;> by_cases hk : sample.2 i = k <;> simp [hi, hk]
  rw [hierarchical_parent_marginal, hierarchical_child_marginal] at hsplit
  linarith

/-- Distinct siblings never co-occur, so their full marginal separates them. -/
theorem hierarchical_child_sibling_separation
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (i : Fin N) (k l : Fin 2) (hkl : k ≠ l) :
    supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
      (hierarchicalChild i k) (hierarchicalChild i l) = supportMarginalWeight P w i / 2 := by
  classical
  rw [← hierarchical_child_marginal P w i k]
  simp only [supportSeparationWeight, supportMarginalWeight, supportFamilyWeight,
    Finset.sum_filter, hierarchicalSupportFamily, mem_hierarchicalSupport_child]
  apply Finset.sum_congr rfl
  intro sample _
  by_cases hi : i ∈ P sample.1
  · by_cases hk : sample.2 i = k
    · simp [hi, hk, hkl]
    · simp [hi, hk]
  · simp [hi]

/-- A parent's nonidentical targets retain at least the smaller of the
parent separation fraction and the fair-child fraction. -/
theorem hierarchical_parent_quantitative_separation
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (ρ : ℝ)
    (hsep : ∀ i j, i ≠ j →
      ρ * supportMarginalWeight P w i ≤ supportSeparationWeight P w i j)
    (i : Fin N) (b : Fin (N * 3)) (hb : b ≠ hierarchicalParent i) :
    min ρ (1 / 2) * supportMarginalWeight (hierarchicalSupportFamily P)
        (hierarchicalSupportWeight w) (hierarchicalParent i) ≤
      supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
        (hierarchicalParent i) b := by
  classical
  rw [hierarchical_parent_marginal]
  have hq : 0 ≤ supportMarginalWeight P w i := supportFamilyWeight_nonneg w hw _
  have hcross (hne : hierarchicalAtomFamily b ≠ i) :
      min ρ (1 / 2) * supportMarginalWeight P w i ≤
        supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
          (hierarchicalParent i) b := by
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hq).trans
      ((hsep i _ (Ne.symm hne)).trans (hierarchical_parent_separation_lower P w hw i b))
  by_cases hfamily : hierarchicalAtomFamily b = i
  · rcases hierarchical_atom_cases b with ⟨j, rfl⟩ | ⟨j, k, rfl⟩
    · simp only [hierarchicalAtomFamily_parent] at hfamily
      exact (hb (congrArg hierarchicalParent hfamily)).elim
    · simp only [hierarchicalAtomFamily_child] at hfamily
      subst j
      rw [hierarchical_parent_child_separation]
      have h := mul_le_mul_of_nonneg_right (min_le_right ρ (1 / 2)) hq
      linarith
  · exact hcross hfamily

/-- A child's targets outside its parent and itself retain the same
quantitative separation fraction. -/
theorem hierarchical_child_quantitative_separation
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (ρ : ℝ)
    (hsep : ∀ i j, i ≠ j →
      ρ * supportMarginalWeight P w i ≤ supportSeparationWeight P w i j)
    (i : Fin N) (k : Fin 2) (b : Fin (N * 3))
    (hbparent : b ≠ hierarchicalParent i) (hbchild : b ≠ hierarchicalChild i k) :
    min ρ (1 / 2) * supportMarginalWeight (hierarchicalSupportFamily P)
        (hierarchicalSupportWeight w) (hierarchicalChild i k) ≤
      supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
        (hierarchicalChild i k) b := by
  classical
  rw [hierarchical_child_marginal]
  have hq : 0 ≤ supportMarginalWeight P w i := supportFamilyWeight_nonneg w hw _
  have hcross (hne : hierarchicalAtomFamily b ≠ i) :
      min ρ (1 / 2) * (supportMarginalWeight P w i / 2) ≤
        supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
          (hierarchicalChild i k) b := by
    have hscale := mul_le_mul_of_nonneg_right (min_le_left ρ (1 / 2)) hq
    have hparent := hsep i _ (Ne.symm hne)
    have hlower := hierarchical_child_separation_lower P w hw i k b
    linarith
  by_cases hfamily : hierarchicalAtomFamily b = i
  · rcases hierarchical_atom_cases b with ⟨j, rfl⟩ | ⟨j, l, rfl⟩
    · simp only [hierarchicalAtomFamily_parent] at hfamily
      exact (hbparent (congrArg hierarchicalParent hfamily)).elim
    · simp only [hierarchicalAtomFamily_child] at hfamily
      subst j
      have hkl : k ≠ l := by
        intro h
        exact hbchild (by rw [h])
      rw [hierarchical_child_sibling_separation P w i k l hkl]
      have h := mul_le_mul_of_nonneg_right (min_le_right ρ (1 / 2)) hq
      nlinarith
  · exact hcross hfamily

/-- The support implications generated by the hierarchy: every atom forces
itself and its family's parent. For parents these are the same atom. -/
def hierarchicalForcedAtoms {N : ℕ} (a : Fin (N * 3)) : Finset (Fin (N * 3)) :=
  {hierarchicalParent (hierarchicalAtomFamily a), a}

@[simp] theorem hierarchicalForcedAtoms_parent {N : ℕ} (i : Fin N) :
    hierarchicalForcedAtoms (hierarchicalParent i) = {hierarchicalParent i} := by
  simp [hierarchicalForcedAtoms]

@[simp] theorem hierarchicalForcedAtoms_child {N : ℕ} (i : Fin N) (k : Fin 2) :
    hierarchicalForcedAtoms (hierarchicalChild i k) =
      {hierarchicalParent i, hierarchicalChild i k} := by
  simp [hierarchicalForcedAtoms]

/-- Hierarchical implications hold in every support, independently of weights. -/
theorem hierarchicalForcedAtoms_subset_support {N : ℕ}
    (P : Finset (Fin N)) (choice : Fin N → Fin 2) (a : Fin (N * 3))
    (ha : a ∈ hierarchicalSupport P choice) :
    hierarchicalForcedAtoms a ⊆ hierarchicalSupport P choice := by
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact (mem_hierarchicalSupport_parent _ _ _).mpr
      (hierarchicalAtomFamily_mem_of_mem P choice a ha)
  · have hba : b = a := Finset.mem_singleton.mp hb
    simpa only [hba] using ha

/-- The finite support law derives separation outside the two explicit
hierarchical implications, using the actual weighted separation sums. -/
theorem hierarchical_quantitative_separation
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (ρ : ℝ)
    (hsep : ∀ i j, i ≠ j →
      ρ * supportMarginalWeight P w i ≤ supportSeparationWeight P w i j)
    (a b : Fin (N * 3)) (hb : b ∉ hierarchicalForcedAtoms a) :
    min ρ (1 / 2) * supportMarginalWeight (hierarchicalSupportFamily P)
        (hierarchicalSupportWeight w) a ≤
      supportSeparationWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w) a b := by
  rcases hierarchical_atom_cases a with ⟨i, rfl⟩ | ⟨i, k, rfl⟩
  · have hb' : b ≠ hierarchicalParent i := by simpa using hb
    exact hierarchical_parent_quantitative_separation P w hw ρ hsep i b hb'
  · have hb' : b ≠ hierarchicalParent i ∧ b ≠ hierarchicalChild i k := by simpa using hb
    exact hierarchical_child_quantitative_separation P w hw ρ hsep i k b hb'.1 hb'.2

/-- For positive-prevalence atoms and positive parent separation, the
explicit implications are exactly the actual zero-separation companions.
Positive prevalence is necessary: an absent atom has zero separation from
all atoms. -/
theorem hierarchical_forcedCompanionSet
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j →
      ρ * supportMarginalWeight P w i ≤ supportSeparationWeight P w i j)
    (a : Fin (N * 3))
    (ha : 0 < supportMarginalWeight (hierarchicalSupportFamily P) (hierarchicalSupportWeight w) a) :
    forcedCompanionSet (hierarchicalSupportFamily P) (hierarchicalSupportWeight w) a =
      hierarchicalForcedAtoms a := by
  classical
  ext b
  constructor
  · intro hb
    by_contra hn
    have hbound := hierarchical_quantitative_separation P w hw ρ hsep a b hn
    have hzero := (mem_forcedCompanionSet _ _ _ _).mp hb
    have hpos : 0 < min ρ (1 / 2) := lt_min hρ (by norm_num)
    have hprod := mul_pos hpos ha
    linarith
  · intro hb
    apply (mem_forcedCompanionSet_iff_positive_weight_occurrence
      (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
      (hierarchicalSupportWeight_nonneg w hw) a b).mpr
    intro sample _ hsample
    exact hierarchicalForcedAtoms_subset_support (P sample.1) sample.2 a hsample hb

/-- A positive-prevalence parent has only itself as forced companion. -/
theorem hierarchical_parent_forcedCompanionSet
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j →
      ρ * supportMarginalWeight P w i ≤ supportSeparationWeight P w i j)
    (i : Fin N) (hi : 0 < supportMarginalWeight P w i) :
    forcedCompanionSet (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
      (hierarchicalParent i) = {hierarchicalParent i} := by
  rw [hierarchical_forcedCompanionSet P w hw ρ hρ hsep _ (by
    simpa only [hierarchical_parent_marginal] using hi), hierarchicalForcedAtoms_parent]

/-- A positive-prevalence child forces exactly its parent and itself. -/
theorem hierarchical_child_forcedCompanionSet
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j →
      ρ * supportMarginalWeight P w i ≤ supportSeparationWeight P w i j)
    (i : Fin N) (k : Fin 2) (hi : 0 < supportMarginalWeight P w i) :
    forcedCompanionSet (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
      (hierarchicalChild i k) = {hierarchicalParent i, hierarchicalChild i k} := by
  rw [hierarchical_forcedCompanionSet P w hw ρ hρ hsep _ (by
    rw [hierarchical_child_marginal]
    exact div_pos hi (by norm_num)), hierarchicalForcedAtoms_child]

end PKG26AtomicFeatures
