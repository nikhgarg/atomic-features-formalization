import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Tauto

namespace PKG26AtomicFeatures

/-- The elements lying in every support indexed by `positive` and in no
support indexed by `negative`. -/
noncomputable def supportMembershipCell
    {ι A : Type*} [Fintype A] (S : ι → Finset A)
    (positive negative : Finset ι) : Finset A := by
  classical
  exact Finset.univ.filter fun a =>
    (∀ i ∈ positive, a ∈ S i) ∧ (∀ i ∈ negative, a ∉ S i)

/-- Requiring one more nonmembership removes the cell in which that
membership is instead required. -/
private theorem supportMembershipCell_insert_negative
    {ι A : Type*} [Fintype A] [DecidableEq ι] [DecidableEq A]
    (S : ι → Finset A) (positive negative : Finset ι) (i : ι) :
    supportMembershipCell S positive (insert i negative) =
      supportMembershipCell S positive negative \
        supportMembershipCell S (insert i positive) negative := by
  classical
  ext a
  simp only [supportMembershipCell, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, forall_eq_or_imp, Finset.mem_sdiff]
  tauto

private theorem supportMembershipCell_insert_positive_subset
    {ι A : Type*} [Fintype A] [DecidableEq ι]
    (S : ι → Finset A) (positive negative : Finset ι) (i : ι) :
    supportMembershipCell S (insert i positive) negative ⊆
      supportMembershipCell S positive negative := by
  classical
  intro a ha
  simp only [supportMembershipCell, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, forall_eq_or_imp] at ha ⊢
  exact ⟨ha.1.2, ha.2⟩

/-- Equal cardinalities of nonempty intersections determine every membership
cell that requires at least one positive membership. Iterating set difference
is the finite inclusion-exclusion argument. -/
theorem supportMembershipCell_card_eq_of_intersection_card_eq
    {ι A B : Type*} [Fintype A] [Fintype B]
    (S : ι → Finset A) (T : ι → Finset B)
    (hinter : ∀ J : Finset ι, J.Nonempty →
      Nat.card {a : A // ∀ i ∈ J, a ∈ S i} =
        Nat.card {b : B // ∀ i ∈ J, b ∈ T i})
    (positive negative : Finset ι) (hpositive : positive.Nonempty) :
    (supportMembershipCell S positive negative).card =
      (supportMembershipCell T positive negative).card := by
  classical
  induction negative using Finset.induction_on generalizing positive with
  | empty =>
      simpa only [supportMembershipCell, Finset.notMem_empty, IsEmpty.forall_iff,
        implies_true, and_true, Nat.card_eq_fintype_card, Fintype.card_subtype]
        using hinter positive hpositive
  | @insert i negative hi ih =>
      rw [supportMembershipCell_insert_negative, supportMembershipCell_insert_negative,
        Finset.card_sdiff_of_subset (supportMembershipCell_insert_positive_subset _ _ _ _),
        Finset.card_sdiff_of_subset (supportMembershipCell_insert_positive_subset _ _ _ _),
        ih positive hpositive, ih (insert i positive) (Finset.insert_nonempty _ _)]

/-- The set of support indices containing an element. -/
noncomputable def supportMembershipPattern
    {ι A : Type*} [Fintype ι] (S : ι → Finset A) (a : A) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => a ∈ S i

@[simp] theorem mem_supportMembershipPattern
    {ι A : Type*} [Fintype ι] (S : ι → Finset A) (a : A) (i : ι) :
    i ∈ supportMembershipPattern S a ↔ a ∈ S i := by
  classical
  simp [supportMembershipPattern]

private theorem supportMembershipPattern_eq_iff
    {ι A : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset A) (a : A) (p : Finset ι) :
    supportMembershipPattern S a = p ↔
      (∀ i ∈ p, a ∈ S i) ∧ (∀ i ∈ pᶜ, a ∉ S i) := by
  classical
  constructor
  · intro h
    constructor
    · intro i hi
      exact (mem_supportMembershipPattern S a i).mp (h.symm ▸ hi)
    · intro i hi hai
      have hip : i ∈ p := h ▸ (mem_supportMembershipPattern S a i).mpr hai
      exact Finset.mem_compl.mp hi hip
  · rintro ⟨hp, hn⟩
    ext i
    rw [mem_supportMembershipPattern]
    exact ⟨fun hi => by_contra fun hnip => hn i (Finset.mem_compl.mpr hnip) hi,
      hp i⟩

private theorem card_supportMembershipPattern_fiber
    {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (S : ι → Finset A) (p : Finset ι) :
    Nat.card {a : A // supportMembershipPattern S a = p} =
      (supportMembershipCell S p pᶜ).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, supportMembershipCell,
    supportMembershipPattern_eq_iff]

/-- A nonempty membership pattern already ensures membership in the union,
so restricting the carrier to the union does not change this fiber. -/
private noncomputable def supportMembershipFiberEquiv
    {ι A : Type*} [Fintype ι] (S : ι → Finset A)
    (p : Finset ι) (hp : p.Nonempty) :
    {a : {a : A // ∃ i, a ∈ S i} // supportMembershipPattern S a.1 = p} ≃
      {a : A // supportMembershipPattern S a = p} where
  toFun a := ⟨a.1.1, a.2⟩
  invFun a := ⟨⟨a.1, by
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, (mem_supportMembershipPattern S a.1 i).mp (a.2.symm ▸ hi)⟩⟩, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- If every nonempty intersection in two finite support families has the
same cardinality, their unions have a bijection preserving every individual
support membership. Elements outside the unions are unrestricted.

The nonempty membership cells have equal sizes by inclusion-exclusion, and
equivalences on those cells combine into the required equivalence. -/
theorem exists_support_membership_equiv_of_intersection_card_eq
    {ι A B : Type*} [Fintype ι] [Fintype A] [Fintype B]
    (S : ι → Finset A) (T : ι → Finset B)
    (hinter : ∀ J : Finset ι, J.Nonempty →
      Nat.card {a : A // ∀ i ∈ J, a ∈ S i} =
        Nat.card {b : B // ∀ i ∈ J, b ∈ T i}) :
    ∃ e : {a : A // ∃ i, a ∈ S i} ≃ {b : B // ∃ i, b ∈ T i},
      ∀ a i, a.1 ∈ S i ↔ (e a).1 ∈ T i := by
  classical
  let f : {a : A // ∃ i, a ∈ S i} → Finset ι :=
    fun a => supportMembershipPattern S a.1
  let g : {b : B // ∃ i, b ∈ T i} → Finset ι :=
    fun b => supportMembershipPattern T b.1
  have hcards (p : Finset ι) :
      Fintype.card {a // f a = p} = Fintype.card {b // g b = p} := by
    by_cases hp : p.Nonempty
    · rw [Fintype.card_congr (supportMembershipFiberEquiv S p hp),
        Fintype.card_congr (supportMembershipFiberEquiv T p hp)]
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        card_supportMembershipPattern_fiber, card_supportMembershipPattern_fiber]
      exact supportMembershipCell_card_eq_of_intersection_card_eq S T hinter p pᶜ hp
    · have hp0 : p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      have hemptyS : IsEmpty {a // f a = p} := ⟨by
        rintro ⟨⟨a, ⟨i, hi⟩⟩, ha⟩
        have himem : i ∈ supportMembershipPattern S a :=
          (mem_supportMembershipPattern S a i).mpr hi
        change supportMembershipPattern S a = p at ha
        simp only [ha, hp0, Finset.notMem_empty] at himem⟩
      have hemptyT : IsEmpty {b // g b = p} := ⟨by
        rintro ⟨⟨b, ⟨i, hi⟩⟩, hb⟩
        have himem : i ∈ supportMembershipPattern T b :=
          (mem_supportMembershipPattern T b i).mpr hi
        change supportMembershipPattern T b = p at hb
        simp only [hb, hp0, Finset.notMem_empty] at himem⟩
      simp only [Fintype.card_of_isEmpty]
  let fiberEquiv (p : Finset ι) := Fintype.equivOfCardEq (hcards p)
  refine ⟨Equiv.ofFiberEquiv fiberEquiv, ?_⟩
  intro a i
  have hpattern := Equiv.ofFiberEquiv_map fiberEquiv a
  have hmem := Finset.ext_iff.mp hpattern i
  simpa only [f, g, mem_supportMembershipPattern] using hmem.symm

end PKG26AtomicFeatures
