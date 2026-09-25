import PKG26AtomicFeatures.RegularSupportRecovery
import PKG26AtomicFeatures.GoodSupportMatching
import PKG26AtomicFeatures.MatchedFeatureRecovery

/-!
# Population recovery with unavoidable companion features

Actual conditional laws and losses yield one matching of all good source and
learned supports. Feature-presence recovery uses only this common membership
pattern, and imposes no pairwise source separation. If nonzero separation
masses have a positive relative lower bound, the same matching also recovers
the span of the selected feature's unavoidable companions.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- Actual probabilities of the exact-K source support events. -/
noncomputable def actualSourceSupportWeights
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) : ExactSourceSupport M K → ℝ :=
  fun s => μ.real (sourceSupportEvent z s.1)

/-- Actual conditional squared reconstruction losses on source supports.
Finiteness on positive-weight supports is derived from the global loss bound. -/
noncomputable def actualConditionalSupportLoss
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m) :
    ExactSourceSupport M K → ℝ :=
  fun s => (actualPopulationSquaredLoss (sourceSupportConditionalLaw μ z s.1)
    A z B code).toReal

/-- Source features which cannot be absent when the selected feature is
present, up to an event of probability zero under the actual population. -/
noncomputable def populationForcedCompanionSet
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (i : Fin M) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter fun j => μ.real {x | 0 < z x i ∧ z x j = 0} = 0

@[simp] theorem mem_populationForcedCompanionSet
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (i j : Fin M) :
    j ∈ populationForcedCompanionSet μ z i ↔ μ.real {x | 0 < z x i ∧ z x j = 0} = 0 := by
  classical
  simp [populationForcedCompanionSet]

/-- The finite support-mass companion set equals the actual population
companion set; no conditional separation witnesses are assumed. -/
theorem populationForcedCompanionSet_eq_forcedCompanionSet
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → FeatureVector M)
    (hz : Measurable z) (hK : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i) (i : Fin M) :
    populationForcedCompanionSet μ z i =
      forcedCompanionSet (fun s : ExactSourceSupport M K => s.1)
        (actualSourceSupportWeights μ z) i := by
  classical
  ext j
  rw [mem_populationForcedCompanionSet, mem_forcedCompanionSet,
    featureSeparation_eq_supportSeparationWeight μ z hz hK hnonneg i j]
  rfl

/-- One dimension-independent threshold and loss budget give a single
injective feature-presence matching, without pairwise separation. The actual
good-support family and its full membership bijection are returned as well.
Under a zero-or-separated probability dichotomy, that same matched coordinate
also identifies the span of all unavoidable companions. Requested positive
caps bound the actual conditional projector error and strictly bound the
good-support loss threshold; local orientation bounds are retained. -/
theorem exists_correlated_population_recovery_constants_with_caps
    (K : ℕ) (γ ρ cLower cUpper η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper)
    (hη : 0 < η) (hηone : η < 1)
    (δcap τcap : ℝ) (hδcap : 0 < δcap) (hτcap : 0 < τcap) :
    ∃ t δ τ D : ℝ, 0 < t ∧ 0 < δ ∧ δ ≤ δcap ∧ 0 < τ ∧ τ < τcap ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        RegularSparsePopulation (K := K) μ z 0 cLower cUpper →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        (∀ x i, 0 ≤ z x i) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ T : goodSupportIndices (actualSourceSupportWeights (K := K) μ z)
              (actualConditionalSupportLoss μ A z B code) τ → Finset (Fin m),
          ∃ e : {i : Fin M // ∃ s : goodSupportIndices (actualSourceSupportWeights (K := K) μ z)
                (actualConditionalSupportLoss μ A z B code) τ, i ∈ s.1.1} ≃
              {j : Fin m // ∃ s, j ∈ T s},
          ∃ embedding : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            (∀ s, (T s).card = K) ∧
            (∀ s, ‖(euclideanColumnSpan A s.1.1).starProjection -
              (euclideanColumnSpan B (T s)).starProjection‖ ≤ δ) ∧
            (∀ s : goodSupportIndices (actualSourceSupportWeights (K := K) μ z)
                (actualConditionalSupportLoss μ A z B code) τ, actualPopulationSquaredLoss
              (sourceSupportConditionalLaw μ z s.1.1) A z B code ≤ ENNReal.ofReal τ) ∧
            (∀ s, ∀ i ∈ s.1.1, ∀ j ∈ T s,
              γ / 2 < ‖representationToEuclidean d (A.col i) +
                representationToEuclidean d (B.col j)‖) ∧
            (∀ i s, i.1 ∈ s.1.1 ↔ (e i).1 ∈ T s) ∧
            (∀ i, ∃ hi, embedding i = (e ⟨i.1, hi⟩).1) ∧
            ∀ i,
              η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (embedding i)} ∧
              ((∀ j : Fin M, μ.real {x | 0 < z x i.1 ∧ z x j = 0} = 0 ∨
                  ρ * featurePrevalence μ z i.1 ≤ μ.real {x | 0 < z x i.1 ∧ z x j = 0}) →
                supportFamilyIntersection
                    (fun s : goodSupportIndices (actualSourceSupportWeights (K := K) μ z)
                      (actualConditionalSupportLoss μ A z B code) τ => s.1.1)
                    (supportMembershipPattern T (embedding i)) = populationForcedCompanionSet μ z i.1 ∧
                ‖(euclideanColumnSpan A (populationForcedCompanionSet μ z i.1)).starProjection -
                  (euclideanColumnSpan B (supportFamilyIntersection T
                    (supportMembershipPattern T (embedding i)))).starProjection‖ ≤ (1 - η) / 4) := by
  classical
  let ε := 1 - η
  have hε : 0 < ε := sub_pos.mpr hηone
  have hεone : ε < 1 := by dsimp [ε]; linarith
  let q := ε / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hqone : q < 1 := by dsimp [q]; linarith
  let δ₀ := min (q / (2 * (1 + 2 * (K : ℝ) / γ))) δcap
  have hδ₀ : 0 < δ₀ := lt_min (by positivity) hδcap
  obtain ⟨t, δ, τraw, ht, hδ, hδle, hτraw, hconditional⟩ :=
    exists_regular_support_recovery_scales K γ cLower cUpper (ε / 4) δ₀
      hK hγ hγone hcLower hcUpper (by positivity) hδ₀
  let τ := min τraw (τcap / 2)
  have hτ : 0 < τ := lt_min hτraw (by positivity)
  have hτle : τ ≤ τraw := min_le_left _ _
  have hτcap' : τ < τcap := (min_le_right _ _).trans_lt (by linarith)
  have hδcap' : δ ≤ δcap := hδle.trans (min_le_right _ _)
  let Aerr := 4 / (γ ^ 2 * t ^ 2)
  have hAerr : 0 ≤ Aerr := by dsimp [Aerr]; positivity
  let D := 2 / (ρ * τ) + 4 * (Aerr + 1 / τ) / ε + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hDsep : 2 / (ρ * τ) ≤ D := by
    have hrest : 0 ≤ 4 * (Aerr + 1 / τ) / ε := by positivity
    dsimp [D]
    linarith
  have hDerr : 4 * (Aerr + 1 / τ) / ε ≤ D := by
    have hrest : 0 ≤ 2 / (ρ * τ) := by positivity
    dsimp [D]
    linarith
  refine ⟨t, δ, τ, D, ht, hδ, hδcap', hτ, hτcap', hD, ?_⟩
  intro Ω _ μ _ d M m A z hreg hAunit hAstable hznonneg B code hfeas L hL hactualloss
  let S : ExactSourceSupport M K → Finset (Fin M) := Subtype.val
  let w : ExactSourceSupport M K → ℝ := actualSourceSupportWeights μ z
  let ν : ExactSourceSupport M K → Measure Ω := fun s => sourceSupportConditionalLaw μ z s.1
  let residual : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
    (‖representationToEuclidean d (A.mulVec (z x)) -
      representationToEuclidean d (B.mulVec (code x))‖ ^ 2)
  let loss : ExactSourceSupport M K → ℝ := actualConditionalSupportLoss μ A z B code
  have hw : ∀ s, 0 ≤ w s := fun _ => measureReal_nonneg
  have hloss : ∀ s, 0 ≤ loss s := fun _ => ENNReal.toReal_nonneg
  have hsum : ∑ s, w s = 1 :=
    (sourceSupportWeights_nonneg_sum_one μ z hreg.1 hreg.2.1).2
  have hmix : μ = finiteSupportMixture w ν :=
    measure_eq_sum_sourceSupportConditionalLaw μ z hreg.1 hreg.2.1
  have hbound : (∫⁻ x, residual x ∂finiteSupportMixture w ν) ≤ ENNReal.ofReal L := by
    rw [← hmix]
    exact hactualloss
  obtain ⟨hfinite, hweighted⟩ := weightedConditionalLoss_le_of_lintegral_mixture_le
    w ν residual hw L hL hbound
  change weightedConditionalLoss w loss ≤ L at hweighted
  have hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i := Filter.Eventually.of_forall hznonneg
  have hmarg (i : Fin M) : featurePrevalence μ z i = supportMarginalWeight S w i :=
    featurePrevalence_eq_supportMarginalWeight μ z hreg.1 hreg.2.1 hnonneg i
  have hseparationMass (i j : Fin M) : μ.real {x | 0 < z x i ∧ z x j = 0} =
      supportSeparationWeight S w i j :=
    featureSeparation_eq_supportSeparationWeight μ z hreg.1 hreg.2.1 hnonneg i j
  have hsmall (i : Fin M) (hi : 0 < featurePrevalence μ z i)
      (hibudget : D * L ≤ featurePrevalence μ z i) :
      weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i := by
    have hcap : 2 * L / (ρ * τ) ≤ featurePrevalence μ z i := by
      calc
        _ = (2 / (ρ * τ)) * L := by ring_nf
        _ ≤ D * L := mul_le_mul_of_nonneg_right hDsep hL
        _ ≤ _ := hibudget
    have hcap' := (div_le_iff₀ (mul_pos hρ hτ)).mp hcap
    have hpositive := mul_pos (mul_pos hρ hτ) hi
    rw [hmarg i] at hcap' hpositive
    nlinarith
  have hlocal (s : goodSupportIndices w loss τ) :
      ∃ T : Finset (Fin m), T.card = K ∧
        ‖(euclideanColumnSpan A (S s.1)).starProjection -
          (euclideanColumnSpan B T).starProjection‖ ≤ δ ∧
        (∀ j ∉ T, (ν s.1).real {x | t < code x j} ≤ Aerr * loss s.1) ∧
        (∀ j ∈ T, (ν s.1).real {x | code x j ≤ t} ≤ Aerr * loss s.1 + ε / 4) ∧
        ∀ i ∈ S s.1, ∀ j ∈ T,
          γ / 2 < ‖representationToEuclidean d (A.col i) +
            representationToEuclidean d (B.col j)‖ := by
    have hs := (mem_goodSupportIndices w loss τ s.1).mp s.property
    have hmass : μ (sourceSupportEvent z s.1.1) ≠ 0 := by
      intro hzero
      have hpos := hs.1
      simp only [w, actualSourceSupportWeights, Measure.real, hzero, ENNReal.toReal_zero, lt_self_iff_false] at hpos
    have hconditionalLoss : actualPopulationSquaredLoss (ν s.1) A z B code ≤
        ENNReal.ofReal (loss s.1) := by
      change (∫⁻ x, residual x ∂ν s.1) ≤
        ENNReal.ofReal ((∫⁻ x, residual x ∂ν s.1).toReal)
      rw [ENNReal.ofReal_toReal (hfinite s.1 hs.1)]
    obtain ⟨T, hT, hgap, hfp, hfn, horient⟩ := hconditional Ω μ d M m A z 0
      hreg hAunit hAstable B code hfeas s.1 hmass (loss s.1) (hloss s.1) (hs.2.trans hτle)
      hconditionalLoss
    have hfactor : 4 * loss s.1 / (γ ^ 2 * t ^ 2) = Aerr * loss s.1 := by
      dsimp [Aerr]
      ring_nf
    refine ⟨T, hT, hgap, ?_, ?_, horient⟩
    · simpa only [hfactor] using hfp
    · simpa only [hfactor] using hfn
  choose T hT hgap hfp hfn horient using hlocal
  have hScard : ∀ s, (S s).card ≤ K := fun s => s.property.le
  have hgap' (s : goodSupportIndices w loss τ) :
      ‖(euclideanColumnSpan A (S s.1)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          q / (2 * (1 + 2 * (K : ℝ) / min γ γ)) := by
    simpa only [min_self] using (hgap s).trans (hδle.trans (min_le_left _ _))
  obtain ⟨e, hmem⟩ := exists_support_membership_equiv_of_projector_bounds A B γ γ q
    (fun i => (hAunit i).le) (fun j => (hfeas.1 j).le)
    hAstable hfeas.2.1 hγ hγ hq hqone
    (fun s : goodSupportIndices w loss τ => S s.1) T
    (fun s => hScard s.1) (fun s => (hT s).le) hgap'
  let inclusion : {i : Fin M // 0 < featurePrevalence μ z i ∧
      D * L ≤ featurePrevalence μ z i} →
      {i : Fin M // ∃ s : goodSupportIndices w loss τ, i ∈ S s.1} :=
    fun i => ⟨i.1, mem_good_support_union_of_separation_scale S w loss τ ρ
      hw hloss hτ hρ hρone i.1 (hsmall i.1 i.2.1 i.2.2)⟩
  let embedding : {i : Fin M // 0 < featurePrevalence μ z i ∧
      D * L ≤ featurePrevalence μ z i} ↪ Fin m :=
    { toFun := fun i => (e (inclusion i)).1
      inj' := by
        intro i j hij
        have heq : e (inclusion i) = e (inclusion j) := Subtype.ext hij
        apply Subtype.ext
        change (inclusion i).1 = (inclusion j).1
        exact congrArg Subtype.val (e.injective heq) }
  have hgoodloss (s : goodSupportIndices w loss τ) :
      actualPopulationSquaredLoss (ν s.1) A z B code ≤ ENNReal.ofReal τ := by
    have hs := (mem_goodSupportIndices w loss τ s.1).mp s.property
    have hfinite' : actualPopulationSquaredLoss (ν s.1) A z B code ≠ ∞ :=
      hfinite s.1 hs.1
    calc
      _ = ENNReal.ofReal (loss s.1) := (ENNReal.ofReal_toReal hfinite').symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hs.2
  refine ⟨T, e, embedding, hT, hgap, hgoodloss, horient, hmem, ?_, ?_⟩
  · intro i
    exact ⟨(inclusion i).property, rfl⟩
  intro i
  have hmatched (s : goodSupportIndices w loss τ) :
      i.1 ∈ S s.1 ↔ embedding i ∈ T s := hmem (inclusion i) s
  constructor
  · have hbudget : 2 * (Aerr + 1 / τ) * weightedConditionalLoss w loss / (ε / 2) ≤
        supportMarginalWeight S w i.1 := by
      rw [← hmarg i.1]
      calc
        _ = (4 * (Aerr + 1 / τ) / ε) * weightedConditionalLoss w loss := by ring_nf
        _ ≤ (4 * (Aerr + 1 / τ) / ε) * L :=
          mul_le_mul_of_nonneg_left hweighted (by positivity)
        _ ≤ D * L := mul_le_mul_of_nonneg_right hDerr hL
        _ ≤ _ := i.2.2
    have hF1 := matched_feature_populationF1_ge S w loss ν hw hsum hloss
      τ (ε / 4) Aerr (ε / 2) hτ (by positivity) hAerr (by positivity) (by linarith)
      T i.1 (embedding i) {x | 0 < z x i.1}
      (measurableSet_lt measurable_const ((measurable_pi_apply i.1).comp hreg.1))
      code hfeas.2.2.1 t
      (fun s hs => sourceSupportConditionalLaw_feature_truth μ z hreg.1 hznonneg s.1 hs i.1)
      hmatched (fun s hj => hfp s (embedding i) hj)
      (fun s hj => hfn s (embedding i) hj)
      (by rw [← hmarg i.1]; exact i.2.1) hbudget
    rw [← hmix] at hF1
    have heq : ε = 1 - η := rfl
    linarith
  · intro hseparation
    have hseparation' : ∀ j, j ∉ forcedCompanionSet S w i.1 →
        ρ * supportMarginalWeight S w i.1 ≤ supportSeparationWeight S w i.1 j := by
      intro j hj
      have hnonzero : μ.real {x | 0 < z x i.1 ∧ z x j = 0} ≠ 0 := by
        intro hzero
        apply hj
        apply (mem_forcedCompanionSet S w i.1 j).mpr
        rw [← hseparationMass i.1 j]
        exact hzero
      have h := (hseparation j).resolve_left hnonzero
      rw [hmarg i.1, hseparationMass i.1 j] at h
      exact h
    have hcompanion := matched_good_support_companion_projector_bound S w loss τ ρ
      hw hloss hτ hρ hρone A B γ γ q (fun i => (hAunit i).le)
      (fun j => (hfeas.1 j).le) hAstable hfeas.2.1 hγ hγ hq hqone T hScard
      (fun s => (hT s).le) hgap' e hmem (inclusion i) hseparation'
      (hsmall i.1 i.2.1 i.2.2)
    constructor
    · have hsource := (good_support_intersection_eq_forcedCompanionSet S w loss τ ρ
        hw hloss hτ hρ hρone i.1 hseparation' (hsmall i.1 i.2.1 i.2.2)).2
      have hpattern := supportMembershipPattern_eq_of_membership_equiv
        (fun s : goodSupportIndices w loss τ => S s.1) T e hmem (inclusion i)
      change supportFamilyIntersection (fun s : goodSupportIndices w loss τ => S s.1)
        (supportMembershipPattern T (e (inclusion i)).1) = _
      rw [← hpattern, supportFamilyIntersection_good_membership_pattern, hsource]
      exact (populationForcedCompanionSet_eq_forcedCompanionSet μ z hreg.1 hreg.2.1
        hnonneg i.1).symm
    · rw [populationForcedCompanionSet_eq_forcedCompanionSet μ z hreg.1 hreg.2.1 hnonneg]
      have hscale : q / 2 = (1 - η) / 4 := by dsimp [q, ε]; ring_nf
      rw [hscale] at hcompanion
      exact hcompanion

/-- The original correlated recovery endpoint follows by imposing arbitrary
positive auxiliary caps and forgetting the additional conditional bounds. -/
theorem exists_correlated_population_recovery_constants
    (K : ℕ) (γ ρ cLower cUpper η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper)
    (hη : 0 < η) (hηone : η < 1) :
    ∃ t τ D : ℝ, 0 < t ∧ 0 < τ ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        RegularSparsePopulation (K := K) μ z 0 cLower cUpper →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        (∀ x i, 0 ≤ z x i) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ T : goodSupportIndices (actualSourceSupportWeights (K := K) μ z)
              (actualConditionalSupportLoss μ A z B code) τ → Finset (Fin m),
          ∃ e : {i : Fin M // ∃ s : goodSupportIndices (actualSourceSupportWeights (K := K) μ z)
                (actualConditionalSupportLoss μ A z B code) τ, i ∈ s.1.1} ≃
              {j : Fin m // ∃ s, j ∈ T s},
          ∃ embedding : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            (∀ s, (T s).card = K) ∧
            (∀ i s, i.1 ∈ s.1.1 ↔ (e i).1 ∈ T s) ∧
            (∀ i, ∃ hi, embedding i = (e ⟨i.1, hi⟩).1) ∧
            ∀ i,
              η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (embedding i)} ∧
              ((∀ j : Fin M, μ.real {x | 0 < z x i.1 ∧ z x j = 0} = 0 ∨
                  ρ * featurePrevalence μ z i.1 ≤ μ.real {x | 0 < z x i.1 ∧ z x j = 0}) →
                supportFamilyIntersection
                    (fun s : goodSupportIndices (actualSourceSupportWeights (K := K) μ z)
                      (actualConditionalSupportLoss μ A z B code) τ => s.1.1)
                    (supportMembershipPattern T (embedding i)) = populationForcedCompanionSet μ z i.1 ∧
                ‖(euclideanColumnSpan A (populationForcedCompanionSet μ z i.1)).starProjection -
                  (euclideanColumnSpan B (supportFamilyIntersection T
                    (supportMembershipPattern T (embedding i)))).starProjection‖ ≤ (1 - η) / 4) := by
  obtain ⟨t, δ, τ, D, ht, _hδ, _hδcap, hτ, _hτcap, hD, hmain⟩ :=
    exists_correlated_population_recovery_constants_with_caps K γ ρ cLower cUpper η
      hK hγ hγone hρ hρone hcLower hcUpper hη hηone 1 1 zero_lt_one zero_lt_one
  refine ⟨t, τ, D, ht, hτ, hD, ?_⟩
  intro Ω _ μ _ d M m A z hreg hAunit hAstable hznonneg B code hfeas L hL hloss
  obtain ⟨T, e, embedding, hT, _hgap, _hloss, _horient, hmem, hembedding, hfeatures⟩ :=
    hmain Ω μ d M m A z hreg hAunit hAstable hznonneg B code hfeas L hL hloss
  exact ⟨T, e, embedding, hT, hmem, hembedding, hfeatures⟩

/-- Feature-presence recovery alone needs no positive separation parameter:
one learned-coordinate injection works for every sufficiently prevalent
feature in a population with arbitrarily correlated supports. -/
theorem exists_population_feature_presence_recovery_constants
    (K : ℕ) (γ cLower cUpper η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper)
    (hη : 0 < η) (hηone : η < 1) :
    ∃ t D : ℝ, 0 < t ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        RegularSparsePopulation (K := K) μ z 0 cLower cUpper →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        (∀ x i, 0 ≤ z x i) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ e : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            ∀ i, η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  obtain ⟨t, τ, D, ht, _, hD, hmain⟩ :=
    exists_correlated_population_recovery_constants K γ 1 cLower cUpper η
      hK hγ hγone zero_lt_one le_rfl hcLower hcUpper hη hηone
  refine ⟨t, D, ht, hD, ?_⟩
  intro Ω _ μ _ d M m A z hreg hAunit hAstable hznonneg B code hfeas L hL hloss
  obtain ⟨T, e, embedding, _, _, _, hfeatures⟩ :=
    hmain Ω μ d M m A z hreg hAunit hAstable hznonneg B code hfeas L hL hloss
  exact ⟨embedding, fun i => (hfeatures i).1⟩

end PKG26AtomicFeatures
