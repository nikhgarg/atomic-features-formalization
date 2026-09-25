import PKG26AtomicFeatures.OvercompleteIdentifiability

/-!
# Atom identification from adjacent support spaces

Exact rich `K`-sparse reconstruction at arbitrary learned width identifies
all source atom lines when every `K + 1` source columns and every `K + 2`
learned columns are independent. Two adjacent source `r`-spaces span an
`r + 1`-space. Learned independence forces their labels to intersect in
exactly `r - 1` columns, so the representation descends to the source
intersection. Iterating gives distinct singleton representatives.

This support-intersection argument is related to the induction in
Hillar--Sommer, arXiv:1106.3616, Lemma 1. The explicit learned independence
hypothesis permits unequal widths without a bijection of all support labels.
-/

namespace PKG26AtomicFeatures

section Families

variable {R V ι κ : Type*} [Field R] [AddCommGroup V] [Module R V]
  [FiniteDimensional R V] [Fintype ι]

/-- A family independent through order `q` cannot place more than `r`
columns in an `r`-dimensional span when `r < q`. -/
theorem card_le_finrank_familySpan_of_independence_order
    (b : κ → V) (q : ℕ)
    (hind : ∀ t : Finset κ, t.card ≤ q →
      LinearIndependent R (fun j : {j // j ∈ t} => b j))
    (s : Finset κ) (hdim : Module.finrank R (familySpan (R := R) b s) < q) :
    s.card ≤ Module.finrank R (familySpan (R := R) b s) := by
  classical
  by_contra hnot
  have hle : Module.finrank R (familySpan (R := R) b s) + 1 ≤ s.card := by omega
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hle
  have htli := hind t (by omega)
  have htrank := finrank_familySpan_eq_card (R := R) b t htli
  have hmono := Submodule.finrank_mono (familySpan_mono (R := R) b hts)
  omega

/-- A representation of all source `r`-spaces by `r` learned columns
descends to all source `(r-1)`-spaces. Only adjacent source supports are
intersected, so source order `r+1` and learned order `r+2` suffice. -/
theorem exists_lower_span_cover_of_adjacent_independence
    (a : ι → V) (b : κ → V) (r : ℕ) (hr : 1 < r)
    (hrlt : r < Fintype.card ι)
    (hA : ∀ s : Finset ι, s.card ≤ r + 1 →
      LinearIndependent R (fun i : {i // i ∈ s} => a i))
    (hB : ∀ t : Finset κ, t.card ≤ r + 2 →
      LinearIndependent R (fun j : {j // j ∈ t} => b j))
    (hcover : ∀ s : Finset ι, s.card = r →
      ∃ t : Finset κ, t.card = r ∧
        familySpan (R := R) a s = familySpan (R := R) b t) :
    ∀ s : Finset ι, s.card = r - 1 →
      ∃ t : Finset κ, t.card = r - 1 ∧
        familySpan (R := R) a s = familySpan (R := R) b t := by
  classical
  intro s hs
  obtain ⟨i, j, hi, hj, hij⟩ :=
    exists_two_not_mem_cardSubset (ι := ι) (by omega) hrlt ⟨s, hs⟩
  let S := insert i s
  let T := insert j s
  have hScard : S.card = r := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem hi, hs]
    omega
  have hTcard : T.card = r := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hj, hs]
    omega
  have hUnion : S ∪ T = insert i (insert j s) := by
    ext x
    simp only [S, T, Finset.mem_union, Finset.mem_insert]
    tauto
  have hInter : S ∩ T = s := by
    ext x
    simp only [S, T, Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hxi | hxs, hxj | hxs'⟩
      · exact (hij (hxi.symm.trans hxj)).elim
      · exact hxs'
      · exact hxs
      · exact hxs
    · intro hx
      exact ⟨Or.inr hx, Or.inr hx⟩
  have hUnionCard : (S ∪ T).card = r + 1 := by
    rw [hUnion, Finset.card_insert_of_notMem (by simp [hij, hi]),
      Finset.card_insert_of_notMem hj, hs]
    omega
  obtain ⟨P, hPcard, hPspan⟩ := hcover S hScard
  obtain ⟨Q, hQcard, hQspan⟩ := hcover T hTcard
  have hAUnion := hA (S ∪ T) (by omega)
  have hUnionSpan : familySpan (R := R) b (P ∪ Q) =
      familySpan (R := R) a (S ∪ T) := by
    rw [familySpan_union, ← hPspan, ← hQspan, ← familySpan_union]
  have hUnionRank : Module.finrank R (familySpan (R := R) b (P ∪ Q)) = r + 1 := by
    rw [hUnionSpan, finrank_familySpan_eq_card (R := R) a (S ∪ T) hAUnion,
      hUnionCard]
  have hBUnionCard : (P ∪ Q).card = r + 1 := by
    have hle := card_le_finrank_familySpan_of_independence_order
      (R := R) b (r + 2) hB (P ∪ Q) (by omega)
    have hge := finrank_familySpan_le_card (R := R) b (P ∪ Q)
    omega
  have hInterCard : (P ∩ Q).card = r - 1 := by
    have hcount := Finset.card_union_add_card_inter P Q
    omega
  refine ⟨P ∩ Q, hInterCard, ?_⟩
  rw [← hInter, familySpan_inter_eq_inf (R := R) a S T hAUnion,
    hPspan, hQspan, ← familySpan_inter_eq_inf (R := R) b P Q (hB _ (by omega))]

/-- Full support-space richness and adjacent independence force every
source line to be a learned singleton span, at any finite learned width. -/
theorem singleton_span_cover_of_adjacent_independence
    (a : ι → V) (b : κ → V) (K : ℕ) (hKpos : 0 < K)
    (hKlt : K < Fintype.card ι)
    (hA : ∀ s : Finset ι, s.card ≤ K + 1 →
      LinearIndependent R (fun i : {i // i ∈ s} => a i))
    (hB : ∀ t : Finset κ, t.card ≤ K + 2 →
      LinearIndependent R (fun j : {j // j ∈ t} => b j))
    (hcover : ∀ s : Finset ι, s.card = K →
      ∃ t : Finset κ, t.card = K ∧
        familySpan (R := R) a s = familySpan (R := R) b t) :
    ∀ s : Finset ι, s.card = 1 →
      ∃ t : Finset κ, t.card = 1 ∧
        familySpan (R := R) a s = familySpan (R := R) b t := by
  revert hKpos hKlt hA hB hcover
  induction K using Nat.strong_induction_on with
  | h K ih =>
      intro hKpos hKlt hA hB hcover
      by_cases hKone : K = 1
      · subst K
        exact hcover
      · have hlower := exists_lower_span_cover_of_adjacent_independence
          (R := R) a b K (by omega) hKlt hA hB hcover
        exact ih (K - 1) (by omega) (by omega) (by omega)
          (fun s hs => hA s (by omega)) (fun t ht => hB t (by omega)) hlower

/-- Adjacent support independence yields distinct learned representatives
of all source columns, up to nonzero scaling. -/
theorem family_columns_embed_of_adjacent_independence
    (a : ι → V) (b : κ → V) (K : ℕ) (hKpos : 0 < K)
    (hKlt : K < Fintype.card ι)
    (hA : ∀ s : Finset ι, s.card ≤ K + 1 →
      LinearIndependent R (fun i : {i // i ∈ s} => a i))
    (hB : ∀ t : Finset κ, t.card ≤ K + 2 →
      LinearIndependent R (fun j : {j // j ∈ t} => b j))
    (hcover : ∀ s : Finset ι, s.card = K →
      ∃ t : Finset κ, t.card = K ∧
        familySpan (R := R) a s = familySpan (R := R) b t) :
    ∃ matching : ι ↪ κ, ∃ scale : ι → R,
      (∀ i, scale i ≠ 0) ∧ ∀ i, a i = scale i • b (matching i) := by
  classical
  have hsingle := singleton_span_cover_of_adjacent_independence
    (R := R) a b K hKpos hKlt hA hB hcover
  have hrep : ∀ i : ι, ∃ j : κ,
      familySpan (R := R) a {i} = familySpan (R := R) b {j} := by
    intro i
    obtain ⟨t, htcard, htspan⟩ := hsingle {i} (Finset.card_singleton i)
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp htcard
    exact ⟨j, htspan⟩
  choose matching hmatching using hrep
  have hinj : Function.Injective matching := by
    intro i j hij
    have hspan : familySpan (R := R) a {i} = familySpan (R := R) a {j} := by
      rw [hmatching i, hmatching j, hij]
    have hsets := finset_eq_of_card_eq_of_familySpan_eq (R := R) a
      (s := {i}) (t := {j}) (by simp)
      (fun x _ _ => hA (insert x {j}) (by
        have hcard := Finset.card_insert_le x ({j} : Finset ι)
        simp only [Finset.card_singleton] at hcard
        omega)) hspan
    simpa using hsets
  have hscale : ∀ i : ι, ∃ c : R, c ≠ 0 ∧ a i = c • b (matching i) := by
    intro i
    have hai : a i ∈ familySpan (R := R) b {matching i} := by
      rw [← hmatching i]
      exact Submodule.subset_span ⟨⟨i, Finset.mem_singleton_self i⟩, rfl⟩
    rw [familySpan_singleton] at hai
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hai
    have hli := hA {i} (by simp)
    have hane : a i ≠ 0 := by
      exact hli.ne_zero (⟨i, Finset.mem_singleton_self i⟩ : {j // j ∈ ({i} : Finset ι)})
    refine ⟨c, ?_, hc.symm⟩
    intro hzero
    exact hane (by rw [← hc, hzero]; simp)
  choose scale hscale_ne hscale_eq using hscale
  exact ⟨⟨matching, hinj⟩, scale, hscale_ne, hscale_eq⟩

end Families

/-- Realizing every `K`-sparse point of the positive unit cube supplies a
relatively open patch on every source support. This is the cube-richness
assumption in the atomic model. -/
theorem openKRich_of_sparse_unit_cube_range
    {X : Type*} {M K : ℕ} (z : X → FeatureVector M)
    (hcube : ∀ v : FeatureVector M, (nonzeroSupport v).card ≤ K →
      (∀ i, 0 ≤ v i ∧ v i ≤ 1) → v ∈ Set.range z) :
    OpenKRich (K := K) z := by
  classical
  intro s hs
  let region : Set (coordinateSpan s) :=
    ⋂ i ∈ s, (fun v : coordinateSpan s => (v : FeatureVector M) i) ⁻¹' Set.Ioo 0 1
  have hopen : IsOpen region := by
    apply isOpen_biInter_finset
    intro i _
    exact isOpen_Ioo.preimage ((continuous_apply i).comp continuous_subtype_val)
  let midpoint : FeatureVector M := fun i => if i ∈ s then (1 / 2 : ℝ) else 0
  have hmidpoint : midpoint ∈ coordinateSpan s := by
    apply mem_coordinateSpan_of_nonzeroSupport_subset
    intro i hi
    by_contra his
    have hne := (mem_nonzeroSupport_iff midpoint i).mp hi
    exact hne (by simp [midpoint, his])
  let point : coordinateSpan s := ⟨midpoint, hmidpoint⟩
  have hpoint : point ∈ region := by
    simp only [region, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioo]
    intro i hi
    norm_num [point, midpoint, hi]
  refine ⟨region, hopen, ⟨point, hpoint⟩, ?_⟩
  intro v hv
  apply subset_closure
  apply hcube v
  · exact (Finset.card_le_card
      (nonzeroSupport_subset_of_mem_coordinateSpan v.property)).trans_eq hs
  · intro i
    by_cases hi : i ∈ s
    · have hinterval := Set.mem_iInter.mp (Set.mem_iInter.mp hv i) hi
      exact ⟨hinterval.1.le, hinterval.2.le⟩
    · have hzero := eq_zero_of_mem_coordinateSpan_of_not_mem v.property hi
      simp [hzero]

/-- Exact rich `K`-sparse reconstruction identifies the source atom lines
at arbitrary learned width. Source independence through `K+1` columns and
learned independence through `K+2` columns suffice; the encoder need not
be continuous. This conclusion concerns directions, not pointwise equality
of two sparse codes at exceptional input vectors. -/
theorem source_columns_embed_of_openRich_and_adjacent_independence
    {X : Type*} {d M M' K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hKltM : K < M)
    (hsource : ∀ s : Finset (Fin M), s.card ≤ K + 1 →
      LinearIndependent ℝ (selectedColumns matrix s))
    (hlearned : ∀ t : Finset (Fin M'), t.card ≤ K + 2 →
      LinearIndependent ℝ (selectedColumns alternative t))
    (hrich : OpenKRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin M', ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      ∀ i, matrix.col i = scale i • alternative.col (matching i) := by
  classical
  apply family_columns_embed_of_adjacent_independence
    (R := ℝ) matrix.col alternative.col K hKpos (by simpa using hKltM)
    hsource hlearned
  intro s hs
  obtain ⟨t, hcontain⟩ := exists_sparse_alternative_subspace_of_openKRich
    matrix z f alternative alternativeCode hrich hfactors halternativeSparse
    halternativeFactors s hs
  rw [map_mulVecLin_coordinateSpan_eq_columnSpan] at hcontain
  have hsourceRank := finrank_columnSpan_eq_card matrix s (hsource s (by omega))
  have htargetRank := finrank_columnSpan_le_card alternative t.1
  have hdim := Submodule.finrank_mono hcontain
  have htcard : t.1.card = K := by
    have hle := t.2
    omega
  refine ⟨t.1, htcard, ?_⟩
  change columnSpan matrix s = columnSpan alternative t.1
  exact Submodule.eq_of_le_of_finrank_le hcontain (by omega)

/-- The same direction-identification theorem for density in every complete
source coordinate space. -/
theorem source_columns_embed_of_kRich_and_adjacent_independence
    {X : Type*} {d M M' K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hKltM : K < M)
    (hsource : ∀ s : Finset (Fin M), s.card ≤ K + 1 →
      LinearIndependent ℝ (selectedColumns matrix s))
    (hlearned : ∀ t : Finset (Fin M'), t.card ≤ K + 2 →
      LinearIndependent ℝ (selectedColumns alternative t))
    (hrich : KRich (K := K) z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin M', ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      ∀ i, matrix.col i = scale i • alternative.col (matching i) := by
  exact source_columns_embed_of_openRich_and_adjacent_independence matrix z f
    alternative alternativeCode hKpos hKltM hsource hlearned hrich.openKRich
    hfactors halternativeSparse halternativeFactors

/-- Source-faithful positive-cube form of exact atom identification with
`K+2`-column learned independence. All alternative widths are allowed. -/
theorem source_columns_embed_of_sparse_unit_cube_and_adjacent_independence
    {X : Type*} {d M M' K : ℕ}
    (matrix : Matrix (Fin d) (Fin M) ℝ)
    (z : X → FeatureVector M) (f : X → RepresentationVector d)
    (alternative : Matrix (Fin d) (Fin M') ℝ)
    (alternativeCode : X → FeatureVector M')
    (hKpos : 0 < K) (hKltM : K < M)
    (hsource : ∀ s : Finset (Fin M), s.card ≤ K + 1 →
      LinearIndependent ℝ (selectedColumns matrix s))
    (hlearned : ∀ t : Finset (Fin M'), t.card ≤ K + 2 →
      LinearIndependent ℝ (selectedColumns alternative t))
    (hcube : ∀ v : FeatureVector M, (nonzeroSupport v).card ≤ K →
      (∀ i, 0 ≤ v i ∧ v i ≤ 1) → v ∈ Set.range z)
    (hfactors : ∀ x, f x = matrix.mulVec (z x))
    (halternativeSparse : KSparse (K := K) alternativeCode)
    (halternativeFactors : ∀ x, f x = alternative.mulVec (alternativeCode x)) :
    ∃ matching : Fin M ↪ Fin M', ∃ scale : Fin M → ℝ,
      (∀ i, scale i ≠ 0) ∧
      ∀ i, matrix.col i = scale i • alternative.col (matching i) := by
  exact source_columns_embed_of_openRich_and_adjacent_independence matrix z f
    alternative alternativeCode hKpos hKltM hsource hlearned
    (openKRich_of_sparse_unit_cube_range z hcube)
    hfactors halternativeSparse halternativeFactors

end PKG26AtomicFeatures
