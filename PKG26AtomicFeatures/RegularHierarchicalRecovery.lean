import PKG26AtomicFeatures.RegularHierarchicalPopulation
import PKG26AtomicFeatures.ModulusPopulationRecovery
import PKG26AtomicFeatures.HierarchicalTailComparator

/-!
# Activation recovery for hierarchical regular populations

The whole-family comparator uses only the identity that the two child
prevalences sum to the parent prevalence. The conditional joint upper density
bound provides a common vanishing slab modulus. Population activation
recovery then gives a single injective matching for all qualifying families,
without requiring independent child choices or independent coefficients.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- An entire family's atomic prevalence is twice its parent prevalence.
Only the sum of the two child marginals is needed. -/
theorem sum_wholeFamilyAtoms_of_child_sum {N : ℕ}
    (p : Fin (N * 3) → ℝ) (q : Fin N → ℝ)
    (hparent : ∀ i, p (hierarchicalParent i) = q i)
    (hchild : ∀ i, p (hierarchicalChild i 0) + p (hierarchicalChild i 1) = q i)
    (P : Finset (Fin N)) :
    ∑ a ∈ wholeFamilyAtoms P, p a = 2 * ∑ i ∈ P, q i := by
  rw [wholeFamilyAtoms, Finset.sum_image]
  · rw [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change p (hierarchicalParent i) +
      (p (hierarchicalChild i 0) + p (hierarchicalChild i 1)) = 2 * q i
    rw [hparent, hchild]
    ring
  · exact fun _ _ _ _ h => finProdFinEquiv.injective h

/-- Filling the residual width slots after whole families can only reduce
omitted prevalence. Child balance and independence are unnecessary here. -/
theorem exists_whole_family_comparator_of_child_sum {N m : ℕ}
    (p : Fin (N * 3) → ℝ) (q : Fin N → ℝ)
    (hp : ∀ a, 0 ≤ p a)
    (hparent : ∀ i, p (hierarchicalParent i) = q i)
    (hchild : ∀ i, p (hierarchicalChild i 0) + p (hierarchicalChild i 1) = q i)
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
      rw [wholeFamilyAtoms_complement,
        sum_wholeFamilyAtoms_of_child_sum p q hparent hchild]
    _ = _ := by rw [sum_outside_rankedPrefix_eq_rankedFeatureTail q σ hn]

/-- The actual infimum comparator bound for an arbitrary correlated hierarchy. -/
theorem RegularHierarchicalPopulation.loss_le_parent_tail
    {Ω : Type*} [MeasurableSpace Ω] {d N m L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {w : HierarchicalJointSample N L → ℝ} {ρ κ cLower cUpper : ℝ}
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper)
    (A : Matrix (Fin d) (Fin (N * 3)) ℝ)
    (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m)
    (σ : Equiv.Perm (Fin N)) (γ C₀ : ℝ)
    (hopt : IsApproximatelyOptimalRecoveryPair μ A z B code γ C₀ (2 * L))
    (hA : HasUnitEuclideanColumns A)
    (hstable : SparseLowerStable A γ (2 * (2 * L)))
    (hC₀ : 0 ≤ C₀) (hm : m ≤ N * 3) :
    actualPopulationSquaredLoss μ A z B code ≤
      ENNReal.ofReal (2 * C₀ * (2 * L) *
        rankedFeatureTail (fun i => featurePrevalence μ z (hierarchicalParent i)) σ (m / 3)) := by
  letI := hmodel.isProbabilityMeasure
  obtain ⟨e, he⟩ := exists_whole_family_comparator_of_child_sum
    (featurePrevalence μ z) (fun i => featurePrevalence μ z (hierarchicalParent i))
    (fun _ => measureReal_nonneg) (fun _ => rfl) hmodel.child_prevalence_sum σ hm
  have h := hopt.loss_le_omitted_prevalence_ae μ A z B code e γ C₀
    hA hstable hmodel.measurable (hmodel.ae_support_card.mono fun _ h => h.le)
    hmodel.boundedSparsePopulation.ae_coefficient_bounds hC₀
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  change C₀ * (2 * L : ℕ) *
    (∑ a ∈ Finset.univ \ Finset.univ.image e, featurePrevalence μ z a) ≤ _
  calc
    _ ≤ C₀ * (2 * L : ℕ) * (2 * rankedFeatureTail
        (fun i => featurePrevalence μ z (hierarchicalParent i)) σ (m / 3)) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hC₀ (Nat.cast_nonneg _))
    _ = _ := by push_cast; ring

/-- Uniform activation recovery from the parent tail. Constants precede the
population, dimension, number of families and learned width. A single positive
threshold and a single injective matching recover all three roles of every
positive-prevalence family meeting the tail threshold. The hypothesis is the
actual infimum formulation, including when no minimizer exists. -/
theorem exists_regular_hierarchical_tail_recovery_constants
    (L : ℕ) (γ ρ κ cLower cUpper C₀ η : ℝ)
    (hL : 0 < L) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hcUpper : 0 < cUpper) (hC₀ : 0 < C₀) (hηone : η < 1) :
    ∃ t C : ℝ, 0 < t ∧ 1 < C ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
        (d N m : ℕ) (w : HierarchicalJointSample N L → ℝ)
        (A : Matrix (Fin d) (Fin (N * 3)) ℝ) (z : Ω → FeatureVector (N * 3)),
        RegularHierarchicalPopulation μ z w ρ κ cLower cUpper →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * (2 * L)) →
        ∀ (σ : Equiv.Perm (Fin N)), m ≤ N * 3 →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ (2 * L) →
          actualPopulationSquaredLoss μ A z B code ≤
            ENNReal.ofReal C₀ * optimalRecoveryLoss μ A z γ (2 * L) m →
          ∃ e : (tailRecoverableFeatures
              (fun i => featurePrevalence μ z (hierarchicalParent i)) σ C (m / 3) × Fin 3) ↪ Fin m,
            ∀ i, η < populationF1 μ {x | 0 < z x (finProdFinEquiv (i.1.1, i.2))}
              {x | t < code x (e i)} := by
  classical
  let η' := max η (1 / 2)
  have hη' : 0 < η' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hη'one : η' < 1 := max_lt hηone (by norm_num)
  have hK : 0 < 2 * L := by omega
  obtain ⟨t, D, ht, hD, hrecovery⟩ :=
    exists_modulus_population_feature_presence_recovery_constants (2 * L) γ
      (fun s => cUpper * uniformCubeSlabModulus (2 * L) s) η'
      hK hγ hγone (upperDensitySlabModulus_tendsto_zero (2 * L) cUpper) hη' hη'one
  let C := 2 * D * C₀ * ((2 * L : ℕ) : ℝ) / κ + 2
  have hC : 1 < C := by
    have hp : 0 < 2 * D * C₀ * ((2 * L : ℕ) : ℝ) / κ := by positivity
    dsimp [C]
    linarith
  refine ⟨t, C, ht, hC, ?_⟩
  intro Ω _ μ d N m w A z hmodel hA hstable σ hm B code hfeas hoptinf
  letI := hmodel.isProbabilityMeasure
  have hopt := (isApproximatelyOptimalRecoveryPair_iff_loss_le_infimum
    μ A z B code γ C₀ hC₀).mpr ⟨hfeas, hoptinf⟩
  let q := fun i => featurePrevalence μ z (hierarchicalParent i)
  let tail := rankedFeatureTail q σ (m / 3)
  have htail : 0 ≤ tail := rankedFeatureTail_nonneg q (fun _ => measureReal_nonneg) σ (m / 3)
  let lossCap := 2 * C₀ * ((2 * L : ℕ) : ℝ) * tail
  have hlossCap : 0 ≤ lossCap := by dsimp [lossCap]; positivity
  have hloss : actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal lossCap := by
    simpa only [lossCap, tail, q, Nat.cast_mul, Nat.cast_ofNat] using
      hmodel.loss_le_parent_tail A B code σ γ C₀ hopt hA hstable hC₀.le hm
  obtain ⟨global, hF1⟩ := hrecovery Ω μ d (N * 3) m A z
    (hmodel.modulusSparsePopulation hcUpper.le) hA hstable B code hfeas
    lossCap hlossCap hloss
  let R := tailRecoverableFeatures q σ C (m / 3)
  have hbudget (i : R) : 0 < q i.1 ∧ D * lossCap ≤ κ * q i.1 := by
    obtain ⟨hi, hibound⟩ := (mem_tailRecoverableFeatures q σ C (m / 3) i.1).mp i.2
    refine ⟨hi, ?_⟩
    change C * tail ≤ q i.1 at hibound
    have hcompare : D * lossCap ≤ κ * (C * tail) := by
      have heq : κ * C = 2 * D * C₀ * ((2 * L : ℕ) : ℝ) + 2 * κ := by
        dsimp [C]
        field_simp
      calc
        _ ≤ (2 * D * C₀ * ((2 * L : ℕ) : ℝ) + 2 * κ) * tail := by
          dsimp [lossCap]
          nlinarith
        _ = _ := by rw [← heq]; ring
    exact hcompare.trans (mul_le_mul_of_nonneg_left hibound hκ.le)
  let inclusion : (R × Fin 3) ↪
      {a : Fin (N * 3) // 0 < featurePrevalence μ z a ∧
        D * lossCap ≤ featurePrevalence μ z a} :=
    { toFun := fun ik => ⟨finProdFinEquiv (ik.1.1, ik.2), by
        have hi := hbudget ik.1
        have hrole := hmodel.role_prevalence_ge (by linarith) ik.1.1 ik.2
        exact ⟨(mul_pos hκ hi.1).trans_le hrole, hi.2.trans hrole⟩⟩
      inj' := by
        intro ik jl h
        have hval := congrArg (fun a : {a : Fin (N * 3) //
          0 < featurePrevalence μ z a ∧ D * lossCap ≤ featurePrevalence μ z a} => a.1) h
        have hpair := finProdFinEquiv.injective hval
        apply Prod.ext
        · exact Subtype.ext (congrArg Prod.fst hpair)
        · exact congrArg (fun a : Fin N × Fin 3 => a.2) hpair }
  exact ⟨inclusion.trans global, fun i => (le_max_left _ _).trans_lt (hF1 (inclusion i))⟩

end PKG26AtomicFeatures
