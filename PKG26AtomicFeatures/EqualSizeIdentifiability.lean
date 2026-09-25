import PKG26AtomicFeatures.SparseCoverCounting

/-!
# Equal-size sparse-dictionary identifiability

This module proves equal-size identifiability under full coordinate-subspace
richness. Its combinatorial matrix theorem formalizes
Hillar and Sommer, "When can dictionary learning uniquely recover sparse data
from subsamples?", IEEE Transactions on Information Theory 61(11), 2015,
Lemma 1 (arXiv:1106.3616v5, July 31, 2015).  The pinned source PDF has SHA-256
`b9e308092dd1d35b2bbd548911f6af27bfe0e7f9a5bb8a228b9f1b13b3cb3602`.

The external lemma is re-proved here by its descending-support induction; it
is not taken as an unproved premise.  The final theorem derives the required
span map from the manuscript's richness and two sparse factorizations, then
recovers both columns and codes under `2*K < spark(A)`.  Only the source matrix
needs the spark hypothesis.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

variable {R V ι : Type*} [Field R] [AddCommGroup V] [Module R V]
  [FiniteDimensional R V] [Fintype ι] [DecidableEq ι]

/-- The span of a finite subfamily, indexed without duplicate vectors. -/
noncomputable def familySpan (v : ι → V) (s : Finset ι) : Submodule R V :=
  Submodule.span R (Set.range fun i : {i // i ∈ s} => v i)

omit [FiniteDimensional R V] [Fintype ι] [DecidableEq ι] in
theorem familySpan_mono (v : ι → V) {s t : Finset ι} (hst : s ⊆ t) :
    familySpan (R := R) v s ≤ familySpan (R := R) v t := by
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i.1, hst i.2⟩, rfl⟩

omit [FiniteDimensional R V] [Fintype ι] in
theorem familySpan_union (v : ι → V) (s t : Finset ι) :
    familySpan (R := R) v (s ∪ t) =
      familySpan (R := R) v s ⊔ familySpan (R := R) v t := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    rcases Finset.mem_union.mp i.2 with hi | hi
    · exact Submodule.mem_sup_left
        (Submodule.subset_span ⟨⟨i.1, hi⟩, rfl⟩)
    · exact Submodule.mem_sup_right
        (Submodule.subset_span ⟨⟨i.1, hi⟩, rfl⟩)
  · exact sup_le
      (familySpan_mono (R := R) v Finset.subset_union_left)
      (familySpan_mono (R := R) v Finset.subset_union_right)

omit [FiniteDimensional R V] [Fintype ι] [DecidableEq ι] in
theorem finrank_familySpan_eq_card (v : ι → V) (s : Finset ι)
    (hli : LinearIndependent R (fun i : {i // i ∈ s} => v i)) :
    Module.finrank R (familySpan (R := R) v s) = s.card := by
  simpa [familySpan] using finrank_span_eq_card hli

omit [FiniteDimensional R V] [Fintype ι] [DecidableEq ι] in
theorem finrank_familySpan_le_card (v : ι → V) (s : Finset ι) :
    Module.finrank R (familySpan (R := R) v s) ≤ s.card := by
  simpa [familySpan] using
    (finrank_range_le_card (R := R) (fun i : {i // i ∈ s} => v i))

omit [Fintype ι] in
theorem familySpan_inter_eq_inf (v : ι → V) (s t : Finset ι)
    (hli : LinearIndependent R (fun i : {i // i ∈ s ∪ t} => v i)) :
    familySpan (R := R) v (s ∩ t) =
      familySpan (R := R) v s ⊓ familySpan (R := R) v t := by
  have hli_s : LinearIndependent R (fun i : {i // i ∈ s} => v i) :=
    by
      simpa only [Function.comp_apply] using hli.comp
        (fun i : {i // i ∈ s} =>
          (⟨i.1, Finset.mem_union_left t i.2⟩ : {i // i ∈ s ∪ t}))
        (fun _ _ h => Subtype.ext
          (congrArg (fun z : {i // i ∈ s ∪ t} => z.1) h))
  have hli_t : LinearIndependent R (fun i : {i // i ∈ t} => v i) :=
    by
      simpa only [Function.comp_apply] using hli.comp
        (fun i : {i // i ∈ t} =>
          (⟨i.1, Finset.mem_union_right s i.2⟩ : {i // i ∈ s ∪ t}))
        (fun _ _ h => Subtype.ext
          (congrArg (fun z : {i // i ∈ s ∪ t} => z.1) h))
  have hli_inter : LinearIndependent R (fun i : {i // i ∈ s ∩ t} => v i) :=
    by
      simpa only [Function.comp_apply] using hli.comp
        (fun i : {i // i ∈ s ∩ t} =>
          (⟨i.1, Finset.mem_union_left t (Finset.mem_inter.mp i.2).1⟩ :
            {i // i ∈ s ∪ t}))
        (fun _ _ h => Subtype.ext
          (congrArg (fun z : {i // i ∈ s ∪ t} => z.1) h))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (familySpan (R := R) v s) (familySpan (R := R) v t)
  rw [← familySpan_union (R := R) v s t,
    finrank_familySpan_eq_card (R := R) v (s ∪ t) hli,
    finrank_familySpan_eq_card (R := R) v s hli_s,
    finrank_familySpan_eq_card (R := R) v t hli_t] at hdim
  have hcard := Finset.card_union_add_card_inter s t
  have hinf_dim : Module.finrank R
      ↥((familySpan (R := R) v s : Submodule R V) ⊓
        (familySpan (R := R) v t : Submodule R V)) =
      (s ∩ t).card := by omega
  apply Submodule.eq_of_le_of_finrank_le
  · exact le_inf
      (familySpan_mono (R := R) v Finset.inter_subset_left)
      (familySpan_mono (R := R) v Finset.inter_subset_right)
  · rw [hinf_dim,
      finrank_familySpan_eq_card (R := R) v (s ∩ t) hli_inter]

omit [FiniteDimensional R V] [Fintype ι] in
/-- Equal spans of equally large index sets are equal if adjoining any index
from the first set to the second keeps the family independent.  This is the
finite-dimensional form of Hillar--Sommer Lemma 4(13). -/
theorem finset_eq_of_card_eq_of_familySpan_eq
    (v : ι → V) {s t : Finset ι} (hcard : s.card = t.card)
    (hind : ∀ i ∈ s, i ∉ t →
      LinearIndependent R (fun j : {j // j ∈ insert i t} => v j))
    (hspan : familySpan (R := R) v s = familySpan (R := R) v t) :
    s = t := by
  have hsubset : s ⊆ t := by
    intro i hi
    by_contra hit
    have hvi : v i ∈ familySpan (R := R) v t := by
      rw [← hspan]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    have hinsert_span : familySpan (R := R) v (insert i t) =
        familySpan (R := R) v t := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨j, rfl⟩
        rcases Finset.mem_insert.mp j.2 with hj | hj
        · simpa [hj] using hvi
        · exact Submodule.subset_span ⟨⟨j.1, hj⟩, rfl⟩
      · exact familySpan_mono (R := R) v (Finset.subset_insert i t)
    have hind_insert := hind i hi hit
    have hdim_insert :=
      finrank_familySpan_eq_card (R := R) v (insert i t) hind_insert
    have hdim_t := finrank_familySpan_le_card (R := R) v t
    rw [hinsert_span, Finset.card_insert_of_notMem hit] at hdim_insert
    omega
  exact Finset.eq_of_subset_of_card_le hsubset hcard.ge

/-- A finite subset packaged together with its prescribed cardinality. -/
abbrev CardSubset (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :=
  {s : Finset ι // s.card = k}

/-- Indices are canonically equivalent to singleton finite subsets. -/
noncomputable def singletonCardSubsetEquiv : ι ≃ CardSubset ι 1 where
  toFun i := ⟨{i}, Finset.card_singleton i⟩
  invFun s := Classical.choose (Finset.card_eq_one.mp s.2)
  left_inv i := by
    have hset := Classical.choose_spec
      (Finset.card_eq_one.mp (show ({i} : Finset ι).card = 1 by simp))
    exact (Finset.singleton_inj.mp hset).symm
  right_inv s := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.card_eq_one.mp s.2)).symm

@[simp] theorem singletonCardSubsetEquiv_apply_val (i : ι) :
    (singletonCardSubsetEquiv (ι := ι) i).1 = {i} := rfl

omit [FiniteDimensional R V] [Fintype ι] [DecidableEq ι] in
theorem familySpan_singleton (v : ι → V) (i : ι) :
    familySpan (R := R) v {i} = R ∙ v i := by
  rw [familySpan]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    have hj : j.1 = i := Finset.mem_singleton.mp j.2
    simp [hj]
  · intro hx
    have hxv : x = v i := by simpa using hx
    subst x
    exact ⟨⟨i, by simp⟩, rfl⟩

omit [FiniteDimensional R V] in
/-- A span-preserving map on `k`-subsets is injective when the source family
is independent through `2k`. -/
theorem cardSubset_spanMap_injective
    (a b : ι → V) (k : ℕ) (hk : 0 < k)
    (hind : ∀ s : Finset ι, s.card ≤ 2 * k →
      LinearIndependent R (fun i : {i // i ∈ s} => a i))
    (π : CardSubset ι k → CardSubset ι k)
    (hspan : ∀ s, familySpan (R := R) a s.1 =
      familySpan (R := R) b (π s).1) :
    Function.Injective π := by
  intro s t hπ
  apply Subtype.ext
  apply finset_eq_of_card_eq_of_familySpan_eq (R := R) a (by rw [s.2, t.2])
  · intro i hi hit
    apply hind
    rw [Finset.card_insert_of_notMem hit, t.2]
    omega
  · calc
      familySpan (R := R) a s.1 = familySpan (R := R) b (π s).1 := hspan s
      _ = familySpan (R := R) b (π t).1 := by rw [hπ]
      _ = familySpan (R := R) a t.1 := (hspan t).symm

omit [FiniteDimensional R V] in
/-- Once a span map is bijective, independence of every source `k`-subset
transfers to every target `k`-subset. -/
theorem target_cardSubset_linearIndependent
    (a b : ι → V) (k : ℕ)
    (hind : ∀ s : CardSubset ι k,
      LinearIndependent R (fun i : {i // i ∈ s.1} => a i))
    (π : CardSubset ι k ≃ CardSubset ι k)
    (hspan : ∀ s, familySpan (R := R) a s.1 =
      familySpan (R := R) b (π s).1)
    (t : CardSubset ι k) :
    LinearIndependent R (fun i : {i // i ∈ t.1} => b i) := by
  let s := π.symm t
  have hπs : π s = t := π.apply_symm_apply t
  have hdim : Module.finrank R (familySpan (R := R) b t.1) = t.1.card := by
    calc
      Module.finrank R (familySpan (R := R) b t.1) =
          Module.finrank R (familySpan (R := R) a s.1) := by
            rw [hspan s, hπs]
      _ = s.1.card := finrank_familySpan_eq_card (R := R) a s.1 (hind s)
      _ = t.1.card := by rw [s.2, t.2]
  rw [linearIndependent_iff_card_eq_finrank_span]
  simpa [familySpan] using hdim.symm

omit [Fintype ι] in
theorem card_inter_lt_of_card_eq_of_ne
    {s t : Finset ι} {k : ℕ} (hs : s.card = k) (ht : t.card = k)
    (hne : s ≠ t) :
    (s ∩ t).card < k := by
  have hle : (s ∩ t).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
  by_contra hnot
  have hinter_card : (s ∩ t).card = s.card := by omega
  have hinter_eq : s ∩ t = s :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left hinter_card.ge
  have hst : s ⊆ t := by
    rw [← Finset.inter_eq_left]
    exact hinter_eq
  exact hne (Finset.eq_of_subset_of_card_le hst (by omega))

/-- A `(k-1)`-set has two distinct outside indices whenever `k` is strictly
smaller than the finite ground-set cardinality. -/
theorem exists_two_not_mem_cardSubset
    {k : ℕ} (hkpos : 0 < k) (hklt : k < Fintype.card ι)
    (s : CardSubset ι (k - 1)) :
    ∃ r q : ι, r ∉ s.1 ∧ q ∉ s.1 ∧ r ≠ q := by
  classical
  have hs_lt_univ : s.1.card < (Finset.univ : Finset ι).card := by
    rw [s.2]
    simpa using (Nat.sub_le k 1).trans_lt hklt
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hs_lt_univ
  have hinsert_lt_univ : (insert r s.1).card < (Finset.univ : Finset ι).card := by
    rw [Finset.card_insert_of_notMem hr, s.2]
    simpa [Nat.sub_add_cancel hkpos] using hklt
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hinsert_lt_univ
  refine ⟨r, q, hr, ?_, ?_⟩
  · intro hqs
    exact hq (Finset.mem_insert_of_mem hqs)
  · intro hrq
    subst q
    exact hq (Finset.mem_insert_self r s.1)

/-- Hillar--Sommer's induction step: a span equivalence on `k`-subsets
descends to one on `(k-1)`-subsets.  The construction uses only source
independence through `2k`; target `k`-independence is derived, not assumed. -/
theorem exists_lower_span_equiv
    (a b : ι → V) (k : ℕ) (hk : 1 < k) (hklt : k < Fintype.card ι)
    (hind : ∀ s : Finset ι, s.card ≤ 2 * k →
      LinearIndependent R (fun i : {i // i ∈ s} => a i))
    (π : CardSubset ι k ≃ CardSubset ι k)
    (hspan : ∀ s, familySpan (R := R) a s.1 =
      familySpan (R := R) b (π s).1) :
    ∃ γ : CardSubset ι (k - 1) ≃ CardSubset ι (k - 1),
      ∀ s, familySpan (R := R) b s.1 =
        familySpan (R := R) a (γ s).1 := by
  classical
  let Lower := CardSubset ι (k - 1)
  let Upper := CardSubset ι k
  have hA_k : ∀ s : Upper,
      LinearIndependent R (fun i : {i // i ∈ s.1} => a i) := by
    intro s
    apply hind
    rw [s.2]
    omega
  have hB_k : ∀ s : Upper,
      LinearIndependent R (fun i : {i // i ∈ s.1} => b i) := by
    intro s
    exact target_cardSubset_linearIndependent (R := R) a b k hA_k π hspan s
  have hchoice : ∀ s : Lower,
      ∃ r q : ι, r ∉ s.1 ∧ q ∉ s.1 ∧ r ≠ q := by
    intro s
    exact exists_two_not_mem_cardSubset (by omega) hklt s
  let r : Lower → ι := fun s => Classical.choose (hchoice s)
  let q : Lower → ι := fun s =>
    Classical.choose (Classical.choose_spec (hchoice s))
  have hrq : ∀ s : Lower, r s ∉ s.1 ∧ q s ∉ s.1 ∧ r s ≠ q s := by
    intro s
    dsimp [r, q]
    exact Classical.choose_spec (Classical.choose_spec (hchoice s))
  let up₁ : Lower → Upper := fun s =>
    ⟨insert (r s) s.1, by
      rw [Finset.card_insert_of_notMem (hrq s).1, s.2]
      omega⟩
  let up₂ : Lower → Upper := fun s =>
    ⟨insert (q s) s.1, by
      rw [Finset.card_insert_of_notMem (hrq s).2.1, s.2]
      omega⟩
  have hup_ne : ∀ s : Lower, up₁ s ≠ up₂ s := by
    intro s heq
    have hsets : insert (r s) s.1 = insert (q s) s.1 :=
      congrArg Subtype.val heq
    have hrmem : r s ∈ insert (q s) s.1 := by
      rw [← hsets]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hrmem with hequal | hrmem
    · exact (hrq s).2.2 hequal
    · exact (hrq s).1 hrmem
  let pre₁ : Lower → Upper := fun s => π.symm (up₁ s)
  let pre₂ : Lower → Upper := fun s => π.symm (up₂ s)
  have hpre_ne : ∀ s : Lower, pre₁ s ≠ pre₂ s := by
    intro s heq
    exact hup_ne s (π.symm.injective heq)
  have hspan₁ : ∀ s : Lower,
      familySpan (R := R) a (pre₁ s).1 =
        familySpan (R := R) b (up₁ s).1 := by
    intro s
    simpa [pre₁] using hspan (pre₁ s)
  have hspan₂ : ∀ s : Lower,
      familySpan (R := R) a (pre₂ s).1 =
        familySpan (R := R) b (up₂ s).1 := by
    intro s
    simpa [pre₂] using hspan (pre₂ s)
  have hA_union : ∀ s : Lower,
      LinearIndependent R
        (fun i : {i // i ∈ (pre₁ s).1 ∪ (pre₂ s).1} => a i) := by
    intro s
    apply hind
    calc
      ((pre₁ s).1 ∪ (pre₂ s).1).card ≤
          (pre₁ s).1.card + (pre₂ s).1.card := Finset.card_union_le _ _
      _ = k + k := by rw [(pre₁ s).2, (pre₂ s).2]
      _ = 2 * k := by omega
  have hA_inter : ∀ s : Lower,
      LinearIndependent R
        (fun i : {i // i ∈ (pre₁ s).1 ∩ (pre₂ s).1} => a i) := by
    intro s
    simpa only [Function.comp_apply] using (hA_union s).comp
      (fun i : {i // i ∈ (pre₁ s).1 ∩ (pre₂ s).1} =>
        (⟨i.1, Finset.mem_union_left _ (Finset.mem_inter.mp i.2).1⟩ :
          {i // i ∈ (pre₁ s).1 ∪ (pre₂ s).1}))
      (fun _ _ h => Subtype.ext
        (congrArg (fun z : {i // i ∈ (pre₁ s).1 ∪ (pre₂ s).1} => z.1) h))
  have hB_lower : ∀ s : Lower,
      LinearIndependent R (fun i : {i // i ∈ s.1} => b i) := by
    intro s
    simpa only [Function.comp_apply] using (hB_k (up₁ s)).comp
      (fun i : {i // i ∈ s.1} =>
        (⟨i.1, Finset.mem_insert_of_mem i.2⟩ : {i // i ∈ (up₁ s).1}))
      (fun _ _ h => Subtype.ext
        (congrArg (fun z : {i // i ∈ (up₁ s).1} => z.1) h))
  have hle : ∀ s : Lower,
      familySpan (R := R) b s.1 ≤
        familySpan (R := R) a ((pre₁ s).1 ∩ (pre₂ s).1) := by
    intro s
    rw [familySpan_inter_eq_inf (R := R) a (pre₁ s).1 (pre₂ s).1
      (hA_union s)]
    apply le_inf
    · exact (familySpan_mono (R := R) b (Finset.subset_insert (r s) s.1)).trans_eq
        (hspan₁ s).symm
    · exact (familySpan_mono (R := R) b (Finset.subset_insert (q s) s.1)).trans_eq
        (hspan₂ s).symm
  have hinter_card : ∀ s : Lower,
      ((pre₁ s).1 ∩ (pre₂ s).1).card = k - 1 := by
    intro s
    have hdim := Submodule.finrank_mono (hle s)
    rw [finrank_familySpan_eq_card (R := R) b s.1 (hB_lower s),
      finrank_familySpan_eq_card (R := R) a
        ((pre₁ s).1 ∩ (pre₂ s).1) (hA_inter s), s.2] at hdim
    have hupper := card_inter_lt_of_card_eq_of_ne
      (pre₁ s).2 (pre₂ s).2
      (fun h => hpre_ne s (Subtype.ext h))
    omega
  let gamma : Lower → Lower := fun s =>
    ⟨(pre₁ s).1 ∩ (pre₂ s).1, hinter_card s⟩
  have hgamma_span : ∀ s : Lower,
      familySpan (R := R) b s.1 =
        familySpan (R := R) a (gamma s).1 := by
    intro s
    apply Submodule.eq_of_le_of_finrank_le
    · simpa [gamma] using hle s
    · rw [finrank_familySpan_eq_card (R := R) a _
          (by simpa [gamma] using hA_inter s),
        finrank_familySpan_eq_card (R := R) b s.1 (hB_lower s),
        (gamma s).2, s.2]
  have hgamma_injective : Function.Injective gamma := by
    intro s t hgamma
    apply Subtype.ext
    apply finset_eq_of_card_eq_of_familySpan_eq (R := R) b
      (by rw [s.2, t.2])
    · intro i hi hit
      let enlarged : Upper :=
        ⟨insert i t.1, by
          rw [Finset.card_insert_of_notMem hit, t.2]
          omega⟩
      exact hB_k enlarged
    · calc
        familySpan (R := R) b s.1 =
            familySpan (R := R) a (gamma s).1 := hgamma_span s
        _ = familySpan (R := R) a (gamma t).1 := by rw [hgamma]
        _ = familySpan (R := R) b t.1 := (hgamma_span t).symm
  have hgamma_surjective : Function.Surjective gamma :=
    Finite.surjective_of_injective hgamma_injective
  let gammaEquiv : Lower ≃ Lower :=
    Equiv.ofBijective gamma ⟨hgamma_injective, hgamma_surjective⟩
  refine ⟨gammaEquiv, ?_⟩
  intro s
  simpa [gammaEquiv] using hgamma_span s

omit [FiniteDimensional R V] in
/-- The singleton endpoint of the span-identifiability induction extracts a
permutation of atoms and a nonzero scaling of each target atom. -/
theorem equivalent_of_singleton_span_equiv
    (a b : ι → V)
    (hA : ∀ s : CardSubset ι 1,
      LinearIndependent R (fun i : {i // i ∈ s.1} => a i))
    (π : CardSubset ι 1 ≃ CardSubset ι 1)
    (hspan : ∀ s, familySpan (R := R) a s.1 =
      familySpan (R := R) b (π s).1) :
    ∃ permutation : Equiv.Perm ι, ∃ scale : ι → R,
      (∀ i, scale i ≠ 0) ∧
        ∀ i, b i = scale i • a (permutation i) := by
  classical
  let singletonEquiv : ι ≃ CardSubset ι 1 :=
    singletonCardSubsetEquiv (ι := ι)
  let sourceToTarget : Equiv.Perm ι :=
    singletonEquiv.trans (π.trans singletonEquiv.symm)
  let permutation : Equiv.Perm ι := sourceToTarget.symm
  have hsupport : ∀ j : ι,
      π (singletonEquiv (permutation j)) = singletonEquiv j := by
    intro j
    apply singletonEquiv.symm.injective
    rw [singletonEquiv.symm_apply_apply]
    change sourceToTarget (permutation j) = j
    exact sourceToTarget.apply_symm_apply j
  have hB : ∀ s : CardSubset ι 1,
      LinearIndependent R (fun i : {i // i ∈ s.1} => b i) := by
    intro s
    exact target_cardSubset_linearIndependent (R := R) a b 1 hA π hspan s
  have hscale_exists : ∀ j : ι, ∃ c : R,
      c ≠ 0 ∧ b j = c • a (permutation j) := by
    intro j
    have hsingleton_span : R ∙ a (permutation j) = R ∙ b j := by
      calc
        R ∙ a (permutation j) =
            familySpan (R := R) a {permutation j} :=
          (familySpan_singleton (R := R) a (permutation j)).symm
        _ = familySpan (R := R) a (singletonEquiv (permutation j)).1 := by
          rw [singletonCardSubsetEquiv_apply_val]
        _ = familySpan (R := R) b
            (π (singletonEquiv (permutation j))).1 :=
          hspan (singletonEquiv (permutation j))
        _ = familySpan (R := R) b (singletonEquiv j).1 := by
          rw [hsupport j]
        _ = familySpan (R := R) b {j} := by
          rw [singletonCardSubsetEquiv_apply_val]
        _ = R ∙ b j := familySpan_singleton (R := R) b j
    have hbj_mem : b j ∈ R ∙ a (permutation j) := by
      rw [hsingleton_span]
      exact Submodule.mem_span_singleton_self (b j)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbj_mem
    have hbj_ne : b j ≠ 0 := by
      have hlinear := hB (singletonEquiv j)
      have hj : j ∈ (singletonEquiv j).1 := by
        rw [singletonCardSubsetEquiv_apply_val]
        simp
      exact hlinear.ne_zero ⟨j, hj⟩
    refine ⟨c, ?_, hc.symm⟩
    intro hc_zero
    apply hbj_ne
    rw [← hc, hc_zero]
    simp
  choose scale hscale_ne hscale_eq using hscale_exists
  exact ⟨permutation, scale, hscale_ne, hscale_eq⟩

/-- Combinatorial matrix identifiability (Hillar--Sommer Lemma 1), stated for
finite vector families over any field.  A span-preserving map on all
`k`-subsets, together with source independence through `2k`, forces the target
family to be a permutation and nonzero rescaling of the source family. -/
theorem hillar_sommer_family_identifiability
    (a b : ι → V) (k : ℕ) (hkpos : 0 < k)
    (hklt : k < Fintype.card ι)
    (hind : ∀ s : Finset ι, s.card ≤ 2 * k →
      LinearIndependent R (fun i : {i // i ∈ s} => a i))
    (π : CardSubset ι k → CardSubset ι k)
    (hspan : ∀ s, familySpan (R := R) a s.1 =
      familySpan (R := R) b (π s).1) :
    ∃ permutation : Equiv.Perm ι, ∃ scale : ι → R,
      (∀ i, scale i ≠ 0) ∧
        ∀ i, b i = scale i • a (permutation i) := by
  revert hkpos hklt hind π hspan
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hkpos hklt hind π hspan
      have hπ_injective := cardSubset_spanMap_injective
        (R := R) a b k hkpos hind π hspan
      have hπ_surjective : Function.Surjective π :=
        Finite.surjective_of_injective hπ_injective
      let πEquiv : CardSubset ι k ≃ CardSubset ι k :=
        Equiv.ofBijective π ⟨hπ_injective, hπ_surjective⟩
      have hspanEquiv : ∀ s, familySpan (R := R) a s.1 =
          familySpan (R := R) b (πEquiv s).1 := by
        intro s
        simpa [πEquiv] using hspan s
      by_cases hkone : k = 1
      · subst k
        apply equivalent_of_singleton_span_equiv (R := R) a b
          (π := πEquiv) (hspan := hspanEquiv)
        intro s
        apply hind
        rw [s.2]
        norm_num
      · have hkgt : 1 < k := by omega
        obtain ⟨gamma, hgamma⟩ := exists_lower_span_equiv
          (R := R) a b k hkgt hklt hind πEquiv hspanEquiv
        have hlower_span : ∀ s : CardSubset ι (k - 1),
            familySpan (R := R) a s.1 =
              familySpan (R := R) b (gamma.symm s).1 := by
          intro s
          calc
            familySpan (R := R) a s.1 =
                familySpan (R := R) a (gamma (gamma.symm s)).1 := by
              rw [gamma.apply_symm_apply]
            _ = familySpan (R := R) b (gamma.symm s).1 :=
              (hgamma (gamma.symm s)).symm
        apply ih (k - 1) (by omega) (by omega) (by omega)
          (fun s hs => hind s (by omega)) gamma.symm hlower_span

theorem familySpan_matrix_columns_eq_columnSpan
    {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (s : Finset (Fin M)) :
    familySpan (R := ℝ) matrix.col s = columnSpan matrix s := by
  rfl

theorem finrank_columnSpan_eq_card
    {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (s : Finset (Fin M))
    (hli : LinearIndependent ℝ (selectedColumns matrix s)) :
    Module.finrank ℝ (columnSpan matrix s) = s.card := by
  simpa [columnSpan] using finrank_span_eq_card hli

/-- In the equal-sparsity case, every source `K`-span is equal to an
alternative span supported on exactly `K` atoms.  Exact cardinality follows
from source independence and dimension; it is not an extra target assumption. -/
theorem exists_equal_card_alternative_span
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hK_lt_spark : K < spark matrix)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x))
    (source : CardSubset (Fin M) K) :
    ∃ target : CardSubset (Fin M) K,
      columnSpan matrix source.1 = columnSpan alternative target.1 := by
  classical
  obtain ⟨support, hcontain⟩ :=
    AppendixHall.exists_sparse_alternative_subspace_containing_coordinate_image
      matrix z f alternative alternativeCode hrich hfactors halternativeSparse
      halternativeFactors source.1 source.2
  rw [map_mulVecLin_coordinateSpan_eq_columnSpan] at hcontain
  have hsource_li : LinearIndependent ℝ (selectedColumns matrix source.1) :=
    linearIndependent_of_card_lt_spark matrix source.1 (by simpa [source.2])
  have hsource_dim := finrank_columnSpan_eq_card matrix source.1 hsource_li
  have htarget_dim := finrank_columnSpan_le_card alternative support.1
  have hdim_mono := Submodule.finrank_mono hcontain
  have hsupport_card : support.1.card = K := by
    rw [hsource_dim, source.2] at hdim_mono
    omega
  let target : CardSubset (Fin M) K := ⟨support.1, hsupport_card⟩
  refine ⟨target, Submodule.eq_of_le_of_finrank_le hcontain ?_⟩
  calc
    Module.finrank ℝ (columnSpan alternative support.1) ≤ support.1.card :=
      htarget_dim
    _ = K := hsupport_card
    _ = source.1.card := source.2.symm
    _ = Module.finrank ℝ (columnSpan matrix source.1) := hsource_dim.symm

/-- Equal-width, equal-sparsity dictionary identifiability under the exact
finite-column form of the standard source condition.  The minimum matters for
a square source dictionary: once every source column is independent, unions
of two sparse supports cannot use more than all `M` columns. No spark
hypothesis is imposed on the alternative dictionary. -/
theorem equal_size_columnsEquivalent_of_kRich_and_factorizations_of_min_lt_spark
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hKpos : 0 < K) (hK_lt_M : K < M)
    (hmin_lt_spark : min (2 * K) M < spark matrix)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ColumnsEquivalentUpToPermutationAndScaling matrix alternative := by
  classical
  have hK_lt_spark : K < spark matrix := by
    have hK_le_twoK : K ≤ 2 * K := by omega
    exact ((Nat.le_min).2 ⟨hK_le_twoK, hK_lt_M.le⟩).trans_lt
      hmin_lt_spark
  have hK_lt_card : K < Fintype.card (Fin M) := by
    simpa using hK_lt_M
  have hchoice : ∀ source : CardSubset (Fin M) K,
      ∃ target : CardSubset (Fin M) K,
        columnSpan matrix source.1 = columnSpan alternative target.1 := by
    intro source
    exact exists_equal_card_alternative_span matrix z f alternative
      alternativeCode hK_lt_spark hrich hfactors halternativeSparse
      halternativeFactors source
  let π : CardSubset (Fin M) K → CardSubset (Fin M) K :=
    fun source => Classical.choose (hchoice source)
  have hπ_span : ∀ source : CardSubset (Fin M) K,
      columnSpan matrix source.1 = columnSpan alternative (π source).1 := by
    intro source
    exact Classical.choose_spec (hchoice source)
  have hind : ∀ s : Finset (Fin M), s.card ≤ 2 * K →
      LinearIndependent ℝ (fun i : {i // i ∈ s} => matrix.col i) := by
    intro s hs
    have hsM : s.card ≤ M := by simpa using Finset.card_le_univ s
    simpa [selectedColumns] using
      linearIndependent_of_card_lt_spark matrix s
        (((Nat.le_min).2 ⟨hs, hsM⟩).trans_lt hmin_lt_spark)
  have hfamily_span : ∀ source : CardSubset (Fin M) K,
      familySpan (R := ℝ) matrix.col source.1 =
        familySpan (R := ℝ) alternative.col (π source).1 := by
    intro source
    simpa [familySpan_matrix_columns_eq_columnSpan] using hπ_span source
  have hidentified := hillar_sommer_family_identifiability
    (R := ℝ) matrix.col alternative.col K hKpos hK_lt_card hind π hfamily_span
  simpa [ColumnsEquivalentUpToPermutationAndScaling] using hidentified

/-- Familiar overcomplete specialization of equal-size dictionary
identifiability under `2*K < spark(A)`. -/
theorem equal_size_columnsEquivalent_of_kRich_and_factorizations
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hKpos : 0 < K)
    (h2K_lt_spark : 2 * K < spark matrix)
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ColumnsEquivalentUpToPermutationAndScaling matrix alternative := by
  have hK_lt_M : K < M := by
    have hspark_le := spark_le_column_count_succ matrix
    omega
  apply
    equal_size_columnsEquivalent_of_kRich_and_factorizations_of_min_lt_spark
      matrix z f alternative alternativeCode hKpos hK_lt_M
      ((Nat.min_le_left (2 * K) M).trans_lt h2K_lt_spark)
      hrich hfactors halternativeSparse halternativeFactors

/-- Reindex and rescale an alternative code into source-dictionary
coordinates. -/
def alignAlternativeCode {M : ℕ} (permutation : Equiv.Perm (Fin M))
    (scale : Fin M → ℝ) (code : FeatureVector M) : FeatureVector M :=
  fun i => scale (permutation.symm i) * code (permutation.symm i)

/-- Express a source-coordinate code in the alternative coordinates determined
by a column permutation and nonzero scaling. -/
noncomputable def unalignSourceCode {M : ℕ} (permutation : Equiv.Perm (Fin M))
    (scale : Fin M → ℝ) (code : FeatureVector M) : FeatureVector M :=
  fun j => (scale j)⁻¹ * code (permutation j)

theorem alignAlternativeCode_unalignSourceCode
    {M : ℕ} (permutation : Equiv.Perm (Fin M))
    (scale : Fin M → ℝ) (hscale : ∀ i, scale i ≠ 0)
    (code : FeatureVector M) :
    alignAlternativeCode permutation scale
      (unalignSourceCode permutation scale code) = code := by
  ext i
  simp [alignAlternativeCode, unalignSourceCode, hscale]

theorem mulVec_alignAlternativeCode
    {d M : ℕ} (matrix alternative : Matrix (Fin d) (Fin M) ℝ)
    (permutation : Equiv.Perm (Fin M)) (scale : Fin M → ℝ)
    (hcolumns : ∀ j,
      alternative.col j = scale j • matrix.col (permutation j))
    (code : FeatureVector M) :
    alternative.mulVec code =
      matrix.mulVec (alignAlternativeCode permutation scale code) := by
  ext row
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ j, alternative row j * code j) =
        ∑ j, (scale j * matrix row (permutation j)) * code j := by
      apply Finset.sum_congr rfl
      intro j _
      have hentry := congrFun (hcolumns j) row
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hentry
      rw [hentry]
    _ = ∑ j, matrix row (permutation j) * (scale j * code j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, matrix row i *
        (scale (permutation.symm i) * code (permutation.symm i)) := by
      apply Fintype.sum_equiv permutation
      intro j
      simp
    _ = (∑ i, matrix row i * alignAlternativeCode permutation scale code i) := by
      rfl

theorem mulVec_unalignSourceCode
    {d M : ℕ} (matrix alternative : Matrix (Fin d) (Fin M) ℝ)
    (permutation : Equiv.Perm (Fin M)) (scale : Fin M → ℝ)
    (hscale : ∀ i, scale i ≠ 0)
    (hcolumns : ∀ j,
      alternative.col j = scale j • matrix.col (permutation j))
    (code : FeatureVector M) :
    alternative.mulVec (unalignSourceCode permutation scale code) =
      matrix.mulVec code := by
  calc
    alternative.mulVec (unalignSourceCode permutation scale code) =
        matrix.mulVec (alignAlternativeCode permutation scale
          (unalignSourceCode permutation scale code)) :=
      mulVec_alignAlternativeCode matrix alternative permutation scale hcolumns _
    _ = matrix.mulVec code := by
      rw [alignAlternativeCode_unalignSourceCode permutation scale hscale]

theorem nonzeroSupport_alignAlternativeCode
    {M : ℕ} (permutation : Equiv.Perm (Fin M)) (scale : Fin M → ℝ)
    (hscale : ∀ i, scale i ≠ 0) (code : FeatureVector M) :
    nonzeroSupport (alignAlternativeCode permutation scale code) =
      (nonzeroSupport code).map permutation.toEmbedding := by
  ext i
  simp [alignAlternativeCode, hscale]

theorem nonzeroSupport_unalignSourceCode
    {M : ℕ} (permutation : Equiv.Perm (Fin M)) (scale : Fin M → ℝ)
    (hscale : ∀ i, scale i ≠ 0) (code : FeatureVector M) :
    nonzeroSupport (unalignSourceCode permutation scale code) =
      (nonzeroSupport code).map permutation.symm.toEmbedding := by
  ext j
  simp [unalignSourceCode, hscale]

theorem kSparse_alignAlternativeCode
    {X : Type*} {M K : ℕ} (permutation : Equiv.Perm (Fin M))
    (scale : Fin M → ℝ) (hscale : ∀ i, scale i ≠ 0)
    (code : X → FeatureVector M) (hsparse : KSparse (K := K) code) :
    KSparse (K := K)
      (fun x => alignAlternativeCode permutation scale (code x)) := by
  intro x
  rw [nonzeroSupport_alignAlternativeCode permutation scale hscale,
    Finset.card_map]
  exact hsparse x

theorem kSparse_unalignSourceCode
    {X : Type*} {M K : ℕ} (permutation : Equiv.Perm (Fin M))
    (scale : Fin M → ℝ) (hscale : ∀ i, scale i ≠ 0)
    (code : X → FeatureVector M) (hsparse : KSparse (K := K) code) :
    KSparse (K := K)
      (fun x => unalignSourceCode permutation scale (code x)) := by
  intro x
  rw [nonzeroSupport_unalignSourceCode permutation scale hscale,
    Finset.card_map]
  exact hsparse x

theorem nonzeroSupport_sub_subset
    {M : ℕ} (left right : FeatureVector M) :
    nonzeroSupport (left - right) ⊆
      nonzeroSupport left ∪ nonzeroSupport right := by
  intro i hi
  by_contra hnot
  have hleft : left i = 0 := by
    by_contra hne
    exact hnot (Finset.mem_union_left _
      ((mem_nonzeroSupport_iff left i).mpr hne))
  have hright : right i = 0 := by
    by_contra hne
    exact hnot (Finset.mem_union_right _
      ((mem_nonzeroSupport_iff right i).mpr hne))
  rw [mem_nonzeroSupport_iff] at hi
  simp [hleft, hright] at hi

/-- A dependent finite column selection supplies a nonzero kernel vector
supported entirely on that selection. -/
theorem exists_nonzero_kernel_code_of_dependent
    {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (coordinates : Finset (Fin M))
    (hdependent : ¬ LinearIndependent ℝ
      (selectedColumns matrix coordinates)) :
    ∃ code : FeatureVector M,
      nonzeroSupport code ⊆ coordinates ∧ code ≠ 0 ∧
        matrix.mulVec code = 0 := by
  classical
  obtain ⟨coefficients, hsum, index, hindex⟩ :=
    Fintype.not_linearIndependent_iff.mp hdependent
  let code : FeatureVector M := fun j =>
    if hj : j ∈ coordinates then coefficients ⟨j, hj⟩ else 0
  have hsupport : nonzeroSupport code ⊆ coordinates := by
    intro j hj
    by_contra hnot
    have hzero : code j = 0 := by simp [code, hnot]
    exact (mem_nonzeroSupport_iff code j).mp hj hzero
  have hcode_nonzero : code ≠ 0 := by
    intro hzero
    have hentry := congrFun hzero index.1
    simp [code, index.2] at hentry
    exact hindex hentry
  refine ⟨code, hsupport, hcode_nonzero, ?_⟩
  ext row
  have hsum_row := congrFun hsum row
  simp only [Finset.sum_apply, Pi.smul_apply, selectedColumns,
    smul_eq_mul, Pi.zero_apply] at hsum_row
  rw [Matrix.mulVec, dotProduct]
  calc
    (∑ j : Fin M, matrix row j * code j) =
        ∑ j ∈ coordinates, matrix row j * code j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ coordinates)
      intro j _hj hnot
      simp [code, hnot]
    _ = ∑ j : {j // j ∈ coordinates},
        coefficients j * matrix row j.1 := by
      rw [Finset.sum_subtype coordinates (fun _ => Iff.rfl)
        (fun j => matrix row j * code j)]
      apply Finset.sum_congr rfl
      intro j _hj
      simp [code, j.2, mul_comm]
    _ = 0 := hsum_row

/-- A vector supported on fewer than `spark(A)` coordinates is uniquely
determined by its image under `A`. -/
theorem eq_zero_of_mulVec_eq_zero_of_support_lt_spark
    {d M : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (code : FeatureVector M)
    (hcard : (nonzeroSupport code).card < spark matrix)
    (hzero : matrix.mulVec code = 0) :
    code = 0 := by
  classical
  let support := nonzeroSupport code
  have hli : LinearIndependent ℝ (selectedColumns matrix support) :=
    linearIndependent_of_card_lt_spark matrix support hcard
  have hcombination : Fintype.linearCombination ℝ
      (selectedColumns matrix support) (fun i => code i) = 0 := by
    rw [Fintype.linearCombination_apply]
    ext row
    have hfull : (∑ i : Fin M, matrix row i * code i) = 0 := by
      have hrow := congrFun hzero row
      simpa [Matrix.mulVec, dotProduct] using hrow
    have hrestrict : (∑ i : Fin M, matrix row i * code i) =
        ∑ i ∈ support, matrix row i * code i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ support)
      intro i _ hi
      have hcode : code i = 0 := by
        by_contra hne
        exact hi ((mem_nonzeroSupport_iff code i).mpr hne)
      simp [hcode]
    rw [hrestrict] at hfull
    simp only [Finset.sum_apply, Pi.smul_apply, selectedColumns,
      smul_eq_mul, Pi.zero_apply]
    change (∑ i : {i // i ∈ support}, code i * matrix row i) = 0
    calc
      (∑ i : {i // i ∈ support}, code i * matrix row i) =
          ∑ i ∈ support, code i * matrix row i := by
        symm
        apply Finset.sum_subtype support
        simp
      _ = ∑ i ∈ support, matrix row i * code i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := hfull
  have hcoefficients : (fun i : {i // i ∈ support} => code i) = 0 := by
    apply hli.fintypeLinearCombination_injective
    rw [hcombination]
    simp
  funext i
  by_cases hi : i ∈ support
  · have hcoefficient := congrFun hcoefficients ⟨i, hi⟩
    simpa using hcoefficient
  · by_contra hne
    exact hi ((mem_nonzeroSupport_iff code i).mpr hne)

/-- Heterogeneous exact finite-column injectivity. Two codes with respective
support bounds `leftSparsity` and `rightSparsity` are separated whenever every
realizable union of those supports is smaller than the matrix spark.  The
minimum with the total column count retains the globally-injective square
case and is sharper than replacing both bounds by their maximum. -/
theorem eq_of_mulVec_eq_of_two_sparse_supports_of_sum_min_lt_spark
    {d M leftSparsity rightSparsity : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (left right : FeatureVector M)
    (hleft : (nonzeroSupport left).card ≤ leftSparsity)
    (hright : (nonzeroSupport right).card ≤ rightSparsity)
    (hmin_lt_spark : min (leftSparsity + rightSparsity) M < spark matrix)
    (hequal : matrix.mulVec left = matrix.mulVec right) :
    left = right := by
  have hsupportSparsity :
      (nonzeroSupport (left - right)).card ≤
        leftSparsity + rightSparsity := by
    calc
      (nonzeroSupport (left - right)).card ≤
          (nonzeroSupport left ∪ nonzeroSupport right).card :=
        Finset.card_le_card (nonzeroSupport_sub_subset left right)
      _ ≤ (nonzeroSupport left).card + (nonzeroSupport right).card :=
        Finset.card_union_le _ _
      _ ≤ leftSparsity + rightSparsity := Nat.add_le_add hleft hright
  have hsupportColumns : (nonzeroSupport (left - right)).card ≤ M := by
    simpa using Finset.card_le_univ (nonzeroSupport (left - right))
  have hsupport : (nonzeroSupport (left - right)).card < spark matrix :=
    ((Nat.le_min).2 ⟨hsupportSparsity, hsupportColumns⟩).trans_lt
      hmin_lt_spark
  have hzero : matrix.mulVec (left - right) = 0 := by
    change matrix.mulVecLin (left - right) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hequal
  have hdiff := eq_zero_of_mulVec_eq_zero_of_support_lt_spark
    matrix (left - right) hsupport hzero
  exact sub_eq_zero.mp hdiff

/-- Exact finite-column injectivity criterion in the forward direction: two
`K`-sparse codes are separated whenever every realizable union of their
supports is smaller than the source spark. -/
theorem eq_of_mulVec_eq_of_two_sparse_supports_of_min_lt_spark
    {d M K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (left right : FeatureVector M)
    (hleft : (nonzeroSupport left).card ≤ K)
    (hright : (nonzeroSupport right).card ≤ K)
    (hmin_lt_spark : min (2 * K) M < spark matrix)
    (hequal : matrix.mulVec left = matrix.mulVec right) :
    left = right := by
  exact eq_of_mulVec_eq_of_two_sparse_supports_of_sum_min_lt_spark
    matrix left right hleft hright (by simpa [two_mul] using hmin_lt_spark)
      hequal

theorem eq_of_mulVec_eq_of_two_sparse_supports
    {d M K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (left right : FeatureVector M)
    (hleft : (nonzeroSupport left).card ≤ K)
    (hright : (nonzeroSupport right).card ≤ K)
    (h2K_lt_spark : 2 * K < spark matrix)
    (hequal : matrix.mulVec left = matrix.mulVec right) :
    left = right := by
  apply eq_of_mulVec_eq_of_two_sparse_supports_of_min_lt_spark matrix
    left right hleft hright
    ((Nat.min_le_left (2 * K) M).trans_lt h2K_lt_spark) hequal

/-- Failure of the exact spark threshold produces two distinct `K`-sparse
codes with the same image. A minimum dependent column set is partitioned into
two supports and its nonzero linear relation is split across the two codes. -/
theorem exists_sparse_collision_of_spark_le_min
    {d M K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ)
    (hspark : spark matrix ≤ min (2 * K) M) :
    ∃ left right : FeatureVector M,
      (nonzeroSupport left).card ≤ K ∧
      (nonzeroSupport right).card ≤ K ∧
      left ≠ right ∧ matrix.mulVec left = matrix.mulVec right := by
  classical
  obtain ⟨coordinates, hcard, hdependent⟩ :=
    exists_dependent_card_eq_spark matrix
      (hspark.trans (Nat.min_le_right (2 * K) M))
  obtain ⟨relation, hrelation_support, hrelation_nonzero, hrelation_zero⟩ :=
    exists_nonzero_kernel_code_of_dependent matrix coordinates hdependent
  have hcoordinates_twoK : coordinates.card ≤ 2 * K := by
    rw [hcard]
    exact hspark.trans (Nat.min_le_left (2 * K) M)
  obtain ⟨leftSupport, hleft_subset, hleft_card⟩ :=
    Finset.exists_subset_card_eq (Nat.min_le_right K coordinates.card)
  let rightSupport := coordinates \ leftSupport
  have hright_card : rightSupport.card ≤ K := by
    rw [show rightSupport = coordinates \ leftSupport by rfl,
      Finset.card_sdiff_of_subset hleft_subset, hleft_card]
    omega
  let left : FeatureVector M := fun j =>
    if j ∈ leftSupport then relation j else 0
  let right : FeatureVector M := fun j =>
    if j ∈ rightSupport then -relation j else 0
  have hleft_support : nonzeroSupport left ⊆ leftSupport := by
    intro j hj
    by_contra hnot
    exact (mem_nonzeroSupport_iff left j).mp hj (by simp [left, hnot])
  have hright_support : nonzeroSupport right ⊆ rightSupport := by
    intro j hj
    by_contra hnot
    exact (mem_nonzeroSupport_iff right j).mp hj (by simp [right, hnot])
  have hleft_sparse : (nonzeroSupport left).card ≤ K := by
    apply (Finset.card_le_card hleft_support).trans
    rw [hleft_card]
    exact Nat.min_le_left K coordinates.card
  have hright_sparse : (nonzeroSupport right).card ≤ K :=
    (Finset.card_le_card hright_support).trans hright_card
  have hrelation_eq : relation = left - right := by
    funext j
    by_cases hjcoordinates : j ∈ coordinates
    · by_cases hjleft : j ∈ leftSupport
      · have hjright : j ∉ rightSupport := by
          simp [rightSupport, hjleft]
        simp [left, right, hjleft, hjright]
      · have hjright : j ∈ rightSupport := by
          simp [rightSupport, hjcoordinates, hjleft]
        simp [left, right, hjleft, hjright]
    · have hjleft : j ∉ leftSupport := fun hj =>
        hjcoordinates (hleft_subset hj)
      have hjright : j ∉ rightSupport := by
        simp [rightSupport, hjcoordinates]
      have hjrelation : relation j = 0 := by
        by_contra hnonzero
        exact hjcoordinates
          (hrelation_support ((mem_nonzeroSupport_iff relation j).mpr hnonzero))
      simp [left, right, hjleft, hjright, hjrelation]
  have hleft_ne_right : left ≠ right := by
    intro heq
    apply hrelation_nonzero
    rw [hrelation_eq, heq, sub_self]
  have hequal : matrix.mulVec left = matrix.mulVec right := by
    apply sub_eq_zero.mp
    change matrix.mulVecLin left - matrix.mulVecLin right = 0
    rw [← map_sub, ← hrelation_eq]
    exact hrelation_zero
  exact ⟨left, right, hleft_sparse, hright_sparse, hleft_ne_right, hequal⟩

/-- Injectivity of a matrix on all coefficient vectors with support at most
`K`. -/
def KSparseInjective {d M : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ) (K : ℕ) : Prop :=
  ∀ left right : FeatureVector M,
    (nonzeroSupport left).card ≤ K →
    (nonzeroSupport right).card ≤ K →
    matrix.mulVec left = matrix.mulVec right → left = right

/-- Sharp finite-column characterization of sparse-code injectivity. The
usual `2*K < spark(A)` condition is exact for an overcomplete dictionary; the
minimum also captures the globally injective square case. -/
theorem kSparseInjective_iff_min_lt_spark
    {d M K : ℕ} (matrix : Matrix (Fin d) (Fin M) ℝ) :
    KSparseInjective matrix K ↔ min (2 * K) M < spark matrix := by
  constructor
  · intro hinjective
    by_contra hnot
    have hspark : spark matrix ≤ min (2 * K) M := by omega
    obtain ⟨left, right, hleft, hright, hne, heq⟩ :=
      exists_sparse_collision_of_spark_le_min matrix hspark
    exact hne (hinjective left right hleft hright heq)
  · intro hmin left right hleft hright heq
    exact eq_of_mulVec_eq_of_two_sparse_supports_of_min_lt_spark
      matrix left right hleft hright hmin heq

/-- Complete equal-size endpoint under the exact finite-column spark
threshold: both the dictionary columns and every code vector are recovered up
to the same permutation and nonzero coordinate scaling. -/
theorem equal_size_dictionary_and_code_identifiability_of_min_lt_spark
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hKpos : 0 < K) (hK_lt_M : K < M)
    (hmin_lt_spark : min (2 * K) M < spark matrix)
    (hrich : KRich (K := K) z)
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ permutation : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      (∀ i, alternative.col i = scale i • matrix.col (permutation i)) ∧
      ∀ x, z x = alignAlternativeCode permutation scale (alternativeCode x) := by
  obtain ⟨permutation, scale, hscale, hcolumns⟩ :=
    equal_size_columnsEquivalent_of_kRich_and_factorizations_of_min_lt_spark
      matrix z f alternative alternativeCode hKpos hK_lt_M hmin_lt_spark
      hrich hfactors halternativeSparse halternativeFactors
  refine ⟨permutation, scale, hscale, hcolumns, ?_⟩
  have halignedSparse : KSparse (K := K)
      (fun x => alignAlternativeCode permutation scale (alternativeCode x)) :=
    kSparse_alignAlternativeCode permutation scale hscale alternativeCode
      halternativeSparse
  intro x
  apply eq_of_mulVec_eq_of_two_sparse_supports_of_min_lt_spark matrix (z x)
    (alignAlternativeCode permutation scale (alternativeCode x))
    (hsourceSparse x) (halignedSparse x) hmin_lt_spark
  calc
    matrix.mulVec (z x) = f x := (hfactors x).symm
    _ = alternative.mulVec (alternativeCode x) := halternativeFactors x
    _ = matrix.mulVec
        (alignAlternativeCode permutation scale (alternativeCode x)) :=
      mulVec_alignAlternativeCode matrix alternative permutation scale
        hcolumns (alternativeCode x)

/-- Familiar sufficient specialization of the complete equal-size endpoint
under `2*K < spark(A)`. -/
theorem equal_size_dictionary_and_code_identifiability
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hKpos : 0 < K)
    (h2K_lt_spark : 2 * K < spark matrix)
    (hrich : KRich (K := K) z)
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ permutation : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      (∀ i, alternative.col i = scale i • matrix.col (permutation i)) ∧
      ∀ x, z x = alignAlternativeCode permutation scale (alternativeCode x) := by
  have hK_lt_M : K < M := by
    have hspark_le := spark_le_column_count_succ matrix
    omega
  apply equal_size_dictionary_and_code_identifiability_of_min_lt_spark
    matrix z f alternative alternativeCode hKpos hK_lt_M
    ((Nat.min_le_left (2 * K) M).trans_lt h2K_lt_spark)
    hrich hsourceSparse hfactors halternativeSparse halternativeFactors

/-- Full-spark specialization with the exact square/overcomplete threshold.
When `M = d` the minimum condition is automatic; when `d < M` it reduces to
the familiar `2*K ≤ d`. -/
theorem equal_size_dictionary_and_code_identifiability_full_spark_of_min
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hspark : spark matrix = d + 1)
    (hKpos : 0 < K) (hK_lt_M : K < M)
    (hmin_le_d : min (2 * K) M ≤ d)
    (hrich : KRich (K := K) z)
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ permutation : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      (∀ i, alternative.col i = scale i • matrix.col (permutation i)) ∧
      ∀ x, z x = alignAlternativeCode permutation scale (alternativeCode x) := by
  apply equal_size_dictionary_and_code_identifiability_of_min_lt_spark
    matrix z f alternative alternativeCode hKpos hK_lt_M
  · rw [hspark]
    omega
  · exact hrich
  · exact hsourceSparse
  · exact hfactors
  · exact halternativeSparse
  · exact halternativeFactors

/-- Primitive pair-equivalence formulation of the exact full-spark equal-size
endpoint.  It exposes one common column permutation and scaling together with
the matching pointwise coefficient transformation. -/
theorem equal_size_dictionaryPairsEquivalent_full_spark_of_min
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hspark : spark matrix = d + 1)
    (hKpos : 0 < K) (hK_lt_M : K < M)
    (hmin_le_d : min (2 * K) M ≤ d)
    (hrich : KRich (K := K) z)
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    DictionaryPairsEquivalentUpToPermutationAndScaling matrix z
      alternative alternativeCode := by
  obtain ⟨permutation, scale, hscale, hcolumns, hcodes⟩ :=
    equal_size_dictionary_and_code_identifiability_full_spark_of_min
      matrix z f alternative alternativeCode hspark hKpos hK_lt_M
        hmin_le_d hrich hsourceSparse hfactors halternativeSparse
        halternativeFactors
  refine ⟨permutation, scale, hscale, hcolumns, ?_⟩
  intro x i
  have hcoordinate := congrFun (hcodes x) (permutation i)
  simpa [alignAlternativeCode] using hcoordinate

/-- Full-spark numerical specialization used by the repaired paper theorem:
`spark(A)=d+1` turns `2*K < spark(A)` into the displayed condition
`2*K ≤ d`. -/
theorem equal_size_dictionary_and_code_identifiability_full_spark
    {X : Type*} {d M K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M) ℝ)
    (alternativeCode : X → FeatureVector M)
    (hspark : spark matrix = d + 1)
    (hKpos : 0 < K) (h2K_le_d : 2 * K ≤ d)
    (hrich : KRich (K := K) z)
    (hsourceSparse : KSparse (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x,
      f x = alternative.mulVec (alternativeCode x)) :
    ∃ permutation : Equiv.Perm (Fin M), ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      (∀ i, alternative.col i = scale i • matrix.col (permutation i)) ∧
      ∀ x, z x = alignAlternativeCode permutation scale (alternativeCode x) := by
  apply equal_size_dictionary_and_code_identifiability matrix z f alternative
    alternativeCode hKpos
  · rw [hspark]
    omega
  · exact hrich
  · exact hsourceSparse
  · exact hfactors
  · exact halternativeSparse
  · exact halternativeFactors

end PKG26AtomicFeatures
