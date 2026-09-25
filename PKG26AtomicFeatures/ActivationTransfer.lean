import PKG26AtomicFeatures.ModulusPopulationRecovery
import PKG26AtomicFeatures.ExceptionalMixtureBounds

/-!
# Activation recovery from support-span matches

Any selected family of positive-mass supports can be used. A source and
learned coordinate with the same membership pattern in that family inherit
the conditional activation estimates. Averaging charges its complement
once and gives a common threshold with constants depending only on sparsity,
stability, the upper coefficient-density bound, and the requested F1 score.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff

/-- The probability of leaving a selected exact-support family is its
complementary sum of actual support weights. -/
theorem sourceSupportFamily_complement_probability
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : Ω → FeatureVector M)
    (hz : Measurable z) (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (G : Finset (ExactSourceSupport M K)) :
    μ.real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} =
      supportFamilyWeight (actualSourceSupportWeights (K := K) μ z) (Finset.univ \ G) := by
  classical
  let w : ExactSourceSupport M K → ℝ := actualSourceSupportWeights μ z
  let ν : ExactSourceSupport M K → Measure Ω := fun s => sourceSupportConditionalLaw μ z s.1
  have hmix : μ = finiteSupportMixture w ν :=
    measure_eq_sum_sourceSupportConditionalLaw μ z hz hexact
  change μ.real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} =
    supportFamilyWeight w (Finset.univ \ G)
  rw [hmix, finiteSupportMixture_real_apply w ν (fun _ => measureReal_nonneg)]
  have hpoint (s : ExactSourceSupport M K) :
      w s * (ν s).real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} =
        if s ∈ G then 0 else w s := by
    by_cases hw : w s = 0
    · simp [hw]
    have hmass : μ (sourceSupportEvent z s.1) ≠ 0 := by
      intro hzero
      exact hw (by simp only [w, actualSourceSupportWeights, Measure.real, hzero,
        ENNReal.toReal_zero])
    have hsupport := sourceSupportConditionalLaw_ae_support_eq μ z hz s.1 hmass
    have hmem : s.1 ∈ G.image Subtype.val ↔ s ∈ G := by
      simp only [Finset.mem_image]
      exact ⟨fun ⟨t, ht, heq⟩ => (Subtype.ext heq : t = s) ▸ ht,
        fun hs => ⟨s, hs, rfl⟩⟩
    by_cases hs : s ∈ G
    · have hzero : (ν s).real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} = 0 := by
        calc
          _ = (ν s).real ∅ := by
            apply measureReal_congr
            filter_upwards [hsupport] with x hx
            change (nonzeroSupport (z x) ∉ G.image Subtype.val) = False
            apply propext
            simp only [hx, hmem, hs, not_true_eq_false]
          _ = 0 := measureReal_empty
      simp only [hs, if_true, hzero, mul_zero]
    · have hone : (ν s).real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} = 1 := by
        calc
          _ = (ν s).real Set.univ := by
            apply measureReal_congr
            filter_upwards [hsupport] with x hx
            change (nonzeroSupport (z x) ∉ G.image Subtype.val) = True
            apply propext
            simp only [hx, hmem, hs, not_false_eq_true]
          _ = 1 := probReal_univ
      simp only [hs, if_false, hone, mul_one]
  simp only [hpoint, supportFamilyWeight]
  rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ G <;> simp [ha]


/-- Uniform activation recovery for a prescribed membership-preserving
pair on any selected family of positive-probability source supports. The
small-loss budget includes exactly the probability of leaving that family. -/
theorem exists_activation_transfer_constants
    (K : ℕ) (γ cUpper η : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hcUpper : 0 < cUpper)
    (_hη : 0 < η) (hηone : η < 1) :
    ∃ r c t : ℝ, 0 < r ∧ 0 < c ∧ 0 < t ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        BoundedSparsePopulation (K := K) μ z →
        HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ (G : Finset (ExactSourceSupport M K))
            (T : {s // s ∈ G} → Finset (Fin m)),
            (∀ s ∈ G, μ (sourceSupportEvent z s.1) ≠ 0) →
            (∀ s ∈ G, Measure.map (sourceSupportCoordinates z s)
              (sourceSupportConditionalLaw μ z s.1) ≤
                ENNReal.ofReal cUpper • uniformCubeCoefficientLaw K) →
            (∀ s, (T s).card = K) →
            (∀ s, ‖(euclideanColumnSpan A s.1.1).starProjection -
              (euclideanColumnSpan B (T s)).starProjection‖ ≤ r) →
            ∀ (i : Fin M) (j : Fin m),
              (∀ s, i ∈ s.1.1 ↔ j ∈ T s) →
              0 < featurePrevalence μ z i →
              ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
                L + μ.real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} ≤
                  c * featurePrevalence μ z i →
                η < populationF1 μ {x | 0 < z x i} {x | t < code x j} := by
  classical
  let ε := (1 - η) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  obtain ⟨s, hs, hslab⟩ := densityBoundedCube_random_slab_threshold K cUpper ε hcUpper hε
  let t := (γ / (2 * (K : ℝ))) * s / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hts : 2 * t / (γ / (2 * (K : ℝ))) = s := by dsimp [t]; field_simp
  let r := min (γ / (2 * (K : ℝ)))
    (γ * t / (2 * (K : ℝ) * ((K : ℝ) + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsmall : r * (K : ℝ) ≤ γ / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (K : ℝ))).mp (min_le_left _ _ : r ≤ _)
    nlinarith
  have hrproj : r * (K : ℝ) * ((K : ℝ) + 1) ≤ γ * t / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (K : ℝ) * ((K : ℝ) + 1))).mp
      (min_le_right _ _ : r ≤ _)
    nlinarith
  let Aerr := 4 / (γ ^ 2 * t ^ 2)
  have hAerr : 0 ≤ Aerr := by dsimp [Aerr]; positivity
  let c := ε / (Aerr + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcscale : (Aerr + 1) * c = ε := by dsimp [c]; field_simp
  refine ⟨r, c, t, hr, hc, ht, ?_⟩
  intro Ω _ μ _ d M m A z hpop hAunit hAstable B code hfeas G T hG hdom hT hgap
    i j hmatch hpi L hL hloss hbudget
  let S : ExactSourceSupport M K → Finset (Fin M) := Subtype.val
  let w : ExactSourceSupport M K → ℝ := actualSourceSupportWeights μ z
  let ν : ExactSourceSupport M K → Measure Ω := fun s => sourceSupportConditionalLaw μ z s.1
  let loss : ExactSourceSupport M K → ℝ := actualConditionalSupportLoss μ A z B code
  let Q := Finset.univ \ G
  have hw : ∀ s, 0 ≤ w s := fun _ => measureReal_nonneg
  have hlossnonneg : ∀ s, 0 ≤ loss s := fun _ => ENNReal.toReal_nonneg
  have hmix : μ = finiteSupportMixture w ν :=
    measure_eq_sum_sourceSupportConditionalLaw μ z hpop.measurable hpop.ae_support_card
  have hweighted : weightedConditionalLoss w loss ≤ L := by
    have hbound : actualPopulationSquaredLoss (finiteSupportMixture w ν) A z B code ≤
        ENNReal.ofReal L := by rw [← hmix]; exact hloss
    exact (weightedConditionalLoss_le_of_lintegral_mixture_le w ν _ hw L hL hbound).2
  have hnonneg : ∀ᵐ x ∂μ, ∀ k, 0 ≤ z x k :=
    hpop.ae_coefficient_bounds.mono fun _ hx k => (hx k).1
  have hmarg : featurePrevalence μ z i = supportMarginalWeight S w i :=
    featurePrevalence_eq_supportMarginalWeight μ z hpop.measurable hpop.ae_support_card hnonneg i
  have hQ : μ.real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} =
      supportFamilyWeight w Q :=
    sourceSupportFamily_complement_probability μ z hpop.measurable hpop.ae_support_card G
  have htruth : MeasurableSet {x | 0 < z x i} :=
    measurableSet_lt measurable_const ((measurable_pi_apply i).comp hpop.measurable)
  have hconditional (a : ExactSourceSupport M K) (ha : a ∉ Q) :
      (ν a).real ({x | 0 < z x i} ∆ {x | t < code x j}) ≤
        ε * (if i ∈ S a then 1 else 0) + Aerr * loss a := by
    have haG : a ∈ G := by simpa only [Q, Finset.mem_sdiff, Finset.mem_univ,
      true_and, not_not] using ha
    let ag : {s // s ∈ G} := ⟨a, haG⟩
    have hmass := hG a haG
    have hZ := measurable_sourceSupportCoordinates z hpop.measurable a
    have hsynth := sourceSupportConditionalLaw_ae_synthesis_eq μ A z hpop.measurable a hmass
    have hfinite : actualPopulationSquaredLoss (ν a) A z B code ≠ ∞ :=
      lintegral_sourceSupportConditionalLaw_ne_top μ z a.1 _
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hloss)
    have hlocalLoss : (∫⁻ x, ENNReal.ofReal
        (‖selectedSourceSynthesis A (sourceSupportEnumeration a) (sourceSupportCoordinates z a x) -
          representationToEuclidean d (B.mulVec (code x))‖ ^ 2) ∂ν a) ≤ ENNReal.ofReal (loss a) := by
      have heq : actualPopulationSquaredLoss (ν a) A z B code = ENNReal.ofReal (loss a) :=
        (ENNReal.ofReal_toReal hfinite).symm
      rw [← heq]
      apply le_of_eq (lintegral_congr_ae ?_)
      filter_upwards [hsynth] with x hx
      rw [hx]
    have hslab' : ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
        (ν a).real {x | |inner ℝ v (sourceSupportCoordinates z a x)| ≤
          2 * t / (γ / (2 * (K : ℝ)))} ≤ ε := by
      rw [hts]
      exact hslab Ω (ν a) _ hZ (hdom a haG)
    obtain ⟨hfp, hfn⟩ := thresholded_feature_error_probabilities_of_projector_bound (ν a)
      (sourceSupportCoordinates z a) hZ code hfeas.2.2.1
      (selectedSourceSynthesis A (sourceSupportEnumeration a)) B (T ag)
      γ (K : ℝ) γ r ((K : ℝ) + 1) t ε (loss a)
      hK hγ hγ hr.le ht (hlossnonneg a) (hT ag) hfeas.2.1
      (fun k => (hfeas.1 k).le) (selectedSourceSynthesis_lower A _ γ hAstable)
      (selectedSourceSynthesis_upper A _ (fun k => (hAunit k).le)) hrsmall
      (by simpa only [range_selectedSourceSynthesis, sourceSupportEnumeration_image] using hgap ag)
      (hpop.conditional_norm_le a) hrproj hfeas.2.2.2.2 hfeas.2.2.2.1 hslab' hlocalLoss
    have hpositive : 0 < w a := ENNReal.toReal_pos hmass (measure_ne_top _ _)
    apply classification_error_le_of_activation_bounds (ν a) _ htruth
      (fun x => code x j) ((measurable_pi_apply j).comp hfeas.2.2.1) t ε (Aerr * loss a)
      (i ∈ S a)
      (sourceSupportConditionalLaw_feature_truth_of_ae_nonnegative μ z hpop.measurable hnonneg a.1 hpositive i)
    · intro hi
      have hout := hfp j (fun hj => hi ((hmatch ag).mpr hj))
      convert hout using 1
      dsimp [Aerr]
      ring
    · intro hi
      have hin := hfn j ((hmatch ag).mp hi)
      convert hin using 1
      dsimp [Aerr]
      ring
  have herror := finiteSupportMixture_error_le_of_excludedFamily S w loss ν hw hlossnonneg
    Q ε Aerr hε.le hAerr i ({x | 0 < z x i} ∆ {x | t < code x j}) hconditional
  rw [← hmix, ← hmarg, ← hQ] at herror
  have hbeta : 0 ≤ μ.real {x | nonzeroSupport (z x) ∉ G.image Subtype.val} := measureReal_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ Aerr + 1)
  rw [← mul_assoc, hcscale] at hscaled
  have hweighted' := mul_le_mul_of_nonneg_left hweighted hAerr
  have hF1 : 1 - 2 * ε ≤ populationF1 μ {x | 0 < z x i} {x | t < code x j} := by
    apply populationF1_ge_of_error_le μ htruth
      (measurableSet_lt measurable_const ((measurable_pi_apply j).comp hfeas.2.2.1)) hpi (by positivity)
    change μ.real ({x | 0 < z x i} ∆ {x | t < code x j}) ≤ 2 * ε * featurePrevalence μ z i
    nlinarith [mul_nonneg hAerr hbeta]
  have hstrict : η < 1 - 2 * ε := by dsimp [ε]; linarith
  exact hstrict.trans_le hF1

end PKG26AtomicFeatures
