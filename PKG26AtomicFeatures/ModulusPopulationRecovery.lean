import PKG26AtomicFeatures.ModulusSupportRecovery
import PKG26AtomicFeatures.GoodSupportMatching
import PKG26AtomicFeatures.MatchedFeatureRecovery
import PKG26AtomicFeatures.CorrelatedPopulationRecovery

/-!
# Population feature-presence recovery from a homogeneous small-ball modulus

A common modulus tending to zero gives uniform conditional recovery on the
actual positive-mass source supports. The low-loss supports admit one common
membership-preserving matching. Aggregating their activation bounds gives
one injective population F1 matching for all sufficiently prevalent features.
No pairwise separation, density, or orientation assumption is imposed.

The actual support weights and conditional losses are the existing population
quantities. Their finiteness and mixture identities are proved from the global
loss bound and the exact-support law, including all zero-weight cases.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

/-- Almost-everywhere nonnegative source coefficients suffice for the exact
zero-or-one truth probability on a positive-mass conditional support. -/
theorem sourceSupportConditionalLaw_feature_truth_of_ae_nonnegative
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i) (S : Finset (Fin M))
    (hpos : 0 < μ.real (sourceSupportEvent z S)) (i : Fin M) :
    (sourceSupportConditionalLaw μ z S).real {x | 0 < z x i} =
      if i ∈ S then 1 else 0 := by
  classical
  have hmass : μ (sourceSupportEvent z S) ≠ 0 := by
    intro hzero
    simp only [Measure.real, hzero, ENNReal.toReal_zero, lt_self_iff_false] at hpos
  have htruth : ∀ᵐ x ∂sourceSupportConditionalLaw μ z S, 0 < z x i ↔ i ∈ S := by
    filter_upwards [sourceSupportConditionalLaw_ae_support_eq μ z hz S hmass,
      sourceSupportConditionalLaw_ae_of_ae μ z S hnonneg] with x hx hn
    rw [← hx, mem_nonzeroSupport_iff]
    exact ⟨ne_of_gt, fun hne => lt_of_le_of_ne (hn i) (Ne.symm hne)⟩
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    calc
      _ = (sourceSupportConditionalLaw μ z S).real Set.univ := by
        apply measureReal_congr
        filter_upwards [htruth] with x hx
        exact propext (iff_true_intro (hx.mpr hi))
      _ = 1 := probReal_univ
  · rw [if_neg hi]
    calc
      _ = (sourceSupportConditionalLaw μ z S).real ∅ := by
        apply measureReal_congr
        filter_upwards [htruth] with x hx
        exact propext (iff_false_intro fun hp => hi (hx.mp hp))
      _ = 0 := measureReal_empty

/-- Uniform population F1 recovery, retaining the full good-support matching
and its conditional span and loss bounds. Positive requested caps control the
actual projector accuracy and strictly bound the good-support loss threshold.
The single returned injection is the restriction of the full membership
bijection to all positive prevalences above the same global loss budget. -/
theorem exists_modulus_population_recovery_constants_with_caps
    (K : ℕ) (γ : ℝ) (ψ : ℝ → ℝ) (η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hη : 0 < η) (hηone : η < 1)
    (δcap τcap : ℝ) (hδcap : 0 < δcap) (hτcap : 0 < τcap) :
    ∃ t δ τ D : ℝ, 0 < t ∧ 0 < δ ∧ δ ≤ δcap ∧ 0 < τ ∧ τ < τcap ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        ModulusSparsePopulation (K := K) μ z ψ →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
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
            (∀ i s, i.1 ∈ s.1.1 ↔ (e i).1 ∈ T s) ∧
            (∀ i, ∃ hi, embedding i = (e ⟨i.1, hi⟩).1) ∧
            ∀ i, η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (embedding i)} := by
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
    exists_modulus_support_recovery_scales K γ ψ (ε / 4) δ₀
      hK hγ hγone hψ (by positivity) hδ₀
  let τ := min τraw (τcap / 2)
  have hτ : 0 < τ := lt_min hτraw (by positivity)
  have hτle : τ ≤ τraw := min_le_left _ _
  have hτcap' : τ < τcap := (min_le_right _ _).trans_lt (by linarith)
  have hδcap' : δ ≤ δcap := hδle.trans (min_le_right _ _)
  let Aerr := 4 / (γ ^ 2 * t ^ 2)
  have hAerr : 0 ≤ Aerr := by dsimp [Aerr]; positivity
  let D := 2 / τ + 4 * (Aerr + 1 / τ) / ε + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hDmass : 2 / τ ≤ D := by
    have hrest : 0 ≤ 4 * (Aerr + 1 / τ) / ε := by positivity
    dsimp [D]
    linarith
  have hDerr : 4 * (Aerr + 1 / τ) / ε ≤ D := by
    have hrest : 0 ≤ 2 / τ := by positivity
    dsimp [D]
    linarith
  refine ⟨t, δ, τ, D, ht, hδ, hδcap', hτ, hτcap', hD, ?_⟩
  intro Ω _ μ _ d M m A z hreg hAunit hAstable B code hfeas L hL hactualloss
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
    (sourceSupportWeights_nonneg_sum_one μ z hreg.measurable hreg.ae_support_card).2
  have hmix : μ = finiteSupportMixture w ν :=
    measure_eq_sum_sourceSupportConditionalLaw μ z hreg.measurable hreg.ae_support_card
  have hbound : (∫⁻ x, residual x ∂finiteSupportMixture w ν) ≤ ENNReal.ofReal L := by
    rw [← hmix]
    exact hactualloss
  obtain ⟨hfinite, hweighted⟩ := weightedConditionalLoss_le_of_lintegral_mixture_le
    w ν residual hw L hL hbound
  change weightedConditionalLoss w loss ≤ L at hweighted
  have hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i :=
    hreg.ae_coefficient_bounds.mono (fun _ hx i => (hx i).1)
  have hmarg (i : Fin M) : featurePrevalence μ z i = supportMarginalWeight S w i :=
    featurePrevalence_eq_supportMarginalWeight μ z hreg.measurable hreg.ae_support_card hnonneg i
  have hsmall (i : Fin M) (hi : 0 < featurePrevalence μ z i)
      (hibudget : D * L ≤ featurePrevalence μ z i) :
      weightedConditionalLoss w loss < τ * supportMarginalWeight S w i := by
    have hcap : 2 * L / τ ≤ featurePrevalence μ z i := by
      calc
        _ = (2 / τ) * L := by ring_nf
        _ ≤ D * L := mul_le_mul_of_nonneg_right hDmass hL
        _ ≤ _ := hibudget
    have hcap' := (div_le_iff₀ hτ).mp hcap
    have hpositive := mul_pos hτ hi
    rw [hmarg i] at hcap' hpositive
    nlinarith
  have hlocal (s : goodSupportIndices w loss τ) :
      ∃ T : Finset (Fin m), T.card = K ∧
        ‖(euclideanColumnSpan A (S s.1)).starProjection -
          (euclideanColumnSpan B T).starProjection‖ ≤ δ ∧
        (∀ j ∉ T, (ν s.1).real {x | t < code x j} ≤ Aerr * loss s.1) ∧
        (∀ j ∈ T, (ν s.1).real {x | code x j ≤ t} ≤ Aerr * loss s.1 + ε / 4) := by
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
    obtain ⟨T, hT, hgap, hfp, hfn⟩ := hconditional Ω μ d M m A z
      hreg hAunit hAstable B code hfeas s.1 hmass (loss s.1) (hloss s.1) (hs.2.trans hτle)
      hconditionalLoss
    have hfactor : 4 * loss s.1 / (γ ^ 2 * t ^ 2) = Aerr * loss s.1 := by
      dsimp [Aerr]
      ring_nf
    refine ⟨T, hT, hgap, ?_, ?_⟩
    · simpa only [hfactor] using hfp
    · simpa only [hfactor] using hfn
  choose T hT hgap hfp hfn using hlocal
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
    fun i => ⟨i.1, mem_good_support_union_of_separation_scale S w loss τ 1
      hw hloss hτ zero_lt_one le_rfl i.1 (by simpa using hsmall i.1 i.2.1 i.2.2)⟩
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
  refine ⟨T, e, embedding, hT, hgap, hgoodloss, hmem, ?_, ?_⟩
  · intro i
    exact ⟨(inclusion i).property, rfl⟩
  intro i
  have hmatched (s : goodSupportIndices w loss τ) :
      i.1 ∈ S s.1 ↔ embedding i ∈ T s := hmem (inclusion i) s
  have hbudget : 2 * (Aerr + 1 / τ) * weightedConditionalLoss w loss / (ε / 2) ≤
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
    (measurableSet_lt measurable_const ((measurable_pi_apply i.1).comp hreg.measurable))
    code hfeas.2.2.1 t
    (fun s hs => sourceSupportConditionalLaw_feature_truth_of_ae_nonnegative μ z hreg.measurable hnonneg s.1 hs i.1)
    hmatched (fun s hj => hfp s (embedding i) hj)
    (fun s hj => hfn s (embedding i) hj)
    (by rw [← hmarg i.1]; exact i.2.1) hbudget
  rw [← hmix] at hF1
  have heq : ε = 1 - η := rfl
  linarith

/-- One threshold and one loss-to-prevalence constant recover every sufficiently
prevalent source feature by a single injective matching at any learned width.
Only the actual bounded support laws and a common vanishing homogeneous
small-ball modulus are assumed; no feature-separation parameter is needed. -/
theorem exists_modulus_population_feature_presence_recovery_constants
    (K : ℕ) (γ : ℝ) (ψ : ℝ → ℝ) (η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hη : 0 < η) (hηone : η < 1) :
    ∃ t D : ℝ, 0 < t ∧ 0 < D ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        ModulusSparsePopulation (K := K) μ z ψ →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
          ∃ e : {i : Fin M // 0 < featurePrevalence μ z i ∧
              D * L ≤ featurePrevalence μ z i} ↪ Fin m,
            ∀ i, η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  obtain ⟨t, δ, τ, D, ht, _, _, _, _, hD, hmain⟩ :=
    exists_modulus_population_recovery_constants_with_caps K γ ψ η
      hK hγ hγone hψ hη hηone 1 1 zero_lt_one zero_lt_one
  refine ⟨t, D, ht, hD, ?_⟩
  intro Ω _ μ _ d M m A z hreg hAunit hAstable B code hfeas L hL hloss
  obtain ⟨T, e, embedding, _, _, _, _, _, hfeatures⟩ :=
    hmain Ω μ d M m A z hreg hAunit hAstable B code hfeas L hL hloss
  exact ⟨embedding, hfeatures⟩

end PKG26AtomicFeatures
