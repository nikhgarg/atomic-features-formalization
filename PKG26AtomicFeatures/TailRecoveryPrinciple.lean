import PKG26AtomicFeatures.SignedRecoveryExtensions
import PKG26AtomicFeatures.AETailComparator
import PKG26AtomicFeatures.RankedFeatureTail

/-!
# Recovery from a prevalence tail

The actual-loss recovery theorem and a feasible source truncation give the
paper's prevalence-tail guarantee. One injective matching and one positive
activation threshold serve every recovered feature. The comparison works
for any fixed ranking; sorting by prevalence chooses the smallest tail.
Zero-prevalence features are excluded, including at width M.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

/-- Recovery for constant-factor optimal dictionaries from the actual
prevalence tail. Constants precede all dimensions, widths, populations and
rankings. The source need only be bounded, sparse, normalized and decodable;
the coefficient bounds are needed only almost surely and follow from regularity.
Surjectivity onto the entire sparse cube is unnecessary. -/
theorem exists_tail_recovery_constants
    (K : ℕ) (γ ρ cLower cUpper C₀ η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hρ : 0 < ρ)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper) (hC₀ : 0 < C₀)
    (hη : 0 < η) (hηone : η < 1) :
    ∃ t C : ℝ, 0 < t ∧ 1 < C ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        RegularSparsePopulation (K := K) μ z ρ cLower cUpper →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (σ : Equiv.Perm (Fin M)), m ≤ M →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsApproximatelyOptimalRecoveryPair μ A z B code γ C₀ K →
          ∃ e : tailRecoverableFeatures (featurePrevalence μ z) σ C m ↪ Fin m,
            ∀ i,
              η < inner ℝ (representationToEuclidean d (A.col i.1))
                (representationToEuclidean d (B.col (e i))) ∧
              η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  classical
  obtain ⟨t, D, ht, hD, hrecovery⟩ := exists_signed_regular_population_recovery_constants
    K γ (min ρ 1) cUpper η hK hγ hγone (lt_min hρ zero_lt_one)
      (min_le_right _ _) hcUpper.le hη hηone
  let C := D * C₀ * (K : ℝ) + 2
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hC : 1 < C := by
    have hprod : 0 < D * C₀ * (K : ℝ) := by positivity
    dsimp [C]
    linarith
  refine ⟨t, C, ht, hC, ?_⟩
  intro Ω _ μ _ d M m A z hreg hAunit hAstable σ hm B code hopt
  let tail := rankedFeatureTail (featurePrevalence μ z) σ m
  have htail : 0 ≤ tail := rankedFeatureTail_nonneg _ (fun _ => measureReal_nonneg) σ m
  let L := C₀ * (K : ℝ) * tail
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hloss : actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L := by
    have h := IsApproximatelyOptimalRecoveryPair.loss_le_omitted_prevalence_ae
      μ A z B code (rankedPrefixEmbedding σ hm) γ C₀ hopt
      hAunit hAstable hreg.1 (hreg.2.1.mono fun _ h => h.le)
      hreg.boundedSparsePopulation.ae_coefficient_bounds hC₀.le
    simpa only [omittedFeaturePrevalence_rankedPrefix_eq] using h
  obtain ⟨e, he⟩ := hrecovery Ω μ d M m A z cLower
    (hreg.mono_separation (min_le_left _ _)) hAunit hAstable B code
    hopt.1.1 hopt.1.2.1 hopt.1.2.2.1
    (Filter.Eventually.of_forall hopt.1.2.2.2.1)
    (Filter.Eventually.of_forall hopt.1.2.2.2.2) L hL hloss
  let restrict : tailRecoverableFeatures (featurePrevalence μ z) σ C m ↪
      {i : Fin M // 0 < featurePrevalence μ z i ∧ D * L ≤ featurePrevalence μ z i} :=
    { toFun := fun i => ⟨i.1, by
        obtain ⟨hpos, hbound⟩ := (mem_tailRecoverableFeatures _ σ C m i.1).mp i.2
        refine ⟨hpos, ?_⟩
        have hcompare : D * L ≤ C * tail := by dsimp [L, C]; nlinarith
        exact hcompare.trans hbound⟩
      inj' := by
        intro i j h
        apply Subtype.ext
        exact congrArg (fun k : {i : Fin M // 0 < featurePrevalence μ z i ∧
          D * L ≤ featurePrevalence μ z i} => k.1) h }
  exact ⟨restrict.trans e, fun i => he (restrict i)⟩

end PKG26AtomicFeatures
