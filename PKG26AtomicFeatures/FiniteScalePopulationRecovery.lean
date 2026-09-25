import PKG26AtomicFeatures.FiniteScaleSupportRecovery
import PKG26AtomicFeatures.EligibleSupportRecovery
import PKG26AtomicFeatures.CoordinateTailRecoveryBounds
import PKG26AtomicFeatures.ExceptionalMixtureBounds
import PKG26AtomicFeatures.ModulusPopulationRecovery
import PKG26AtomicFeatures.SignedLineGeometry

/-!
# Signed population recovery from finite coefficient richness

One homogeneous small-ball scale supplies accurate support spans. A separate
source-coordinate lower-tail bound orients the globally matched atoms and
controls their activation errors. Reverse separation charges exceptional
companions to actual reconstruction loss. All constants precede the input
space, population, dictionary dimensions, and learned width.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace symmDiff

set_option maxHeartbeats 800000 in
-- The finite-mixture, orientation, and F1 bounds are assembled in one uniform endpoint.
/-- A single incidence count, chosen before the coefficient scales and
confidence, gives one injective signed and F1 recovery for every sufficiently
prevalent source atom. The input is actual finite squared reconstruction loss;
no density, independence, or minimum support probability is required. -/
theorem exists_finite_scale_population_recovery_constants
    (K : ℕ) (γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) :
    ∃ N : ℕ, ∀ ρ η s₀ a : ℝ,
      0 < ρ → ρ ≤ 1 → 0 < η → η < 1 → 0 < s₀ → 0 < a → a ≤ 1 →
      ∃ t D : ℝ, 0 < t ∧ 0 < D ∧ t = a / 2 ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
          FiniteScaleSparsePopulation (K := K) μ z N s₀ a ((1 - η) / 4) →
          (∀ i j : Fin M, i ≠ j → 0 < featurePrevalence μ z i →
            ρ * featurePrevalence μ z i ≤ μ.real {x | 0 < z x i ∧ z x j = 0}) →
          HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
          ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
            IsFeasibleRecoveryPair B code γ K →
            ∀ L : ℝ, 0 ≤ L → actualPopulationSquaredLoss μ A z B code ≤ ENNReal.ofReal L →
            ∃ e : {i : Fin M // 0 < featurePrevalence μ z i ∧
                D * L ≤ featurePrevalence μ z i} ↪ Fin m,
              ∀ i,
                η < inner ℝ (representationToEuclidean d (A.col i.1))
                  (representationToEuclidean d (B.col (e i))) ∧
                η < populationF1 μ {x | 0 < z x i.1} {x | t < code x (e i)} := by
  classical
  obtain ⟨N, hincidence⟩ := exists_finite_scale_support_incidence_threshold K γ hK hγ hγone
  refine ⟨N, ?_⟩
  intro ρ η s₀ a hρ hρone hη hηone hs₀ ha _haone
  let ξ := 1 - η
  have hξ : 0 < ξ := sub_pos.mpr hηone
  have hξone : ξ < 1 := by dsimp [ξ]; linarith
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
  let q := min (γ / 2) (min (ξ / 2) (γ ^ 2 * a / (8 * (K : ℝ))))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqγ : q ≤ γ / 2 := min_le_left _ _
  have hqξ : q ≤ ξ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hqa : q ≤ γ ^ 2 * a / (8 * (K : ℝ)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqone : q < 1 := by linarith only [hqγ, hγone]
  let δ := min (1 / 2 : ℝ) (min (q / (2 * (1 + 2 * (K : ℝ) / γ)))
    (γ ^ 2 * a / (32 * (K : ℝ) ^ 2)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδgap : δ ≤ q / (2 * (1 + 2 * (K : ℝ) / γ)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ ≤ γ ^ 2 * a / (32 * (K : ℝ) ^ 2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqprod : 8 * q * (K : ℝ) ≤ γ ^ 2 * a := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * (K : ℝ))).mp hqa
    nlinarith only [h]
  have hδprod : 32 * δ * (K : ℝ) ^ 2 ≤ γ ^ 2 * a := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * (K : ℝ) ^ 2)).mp hδa
    nlinarith only [h]
  have hnegativeError : 4 * δ * (K : ℝ) ^ 2 / γ ^ 2 ≤ a / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hγ)).mpr
    nlinarith only [hδprod, mul_nonneg (sq_nonneg γ) ha.le]
  have hpositiveError : (q * (K : ℝ) + 4 * δ * (K : ℝ) ^ 2) / γ ^ 2 ≤ a / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hγ)).mpr
    nlinarith only [hqprod, hδprod]
  have hprojectionError : δ * (K : ℝ) ≤ γ * a / 4 := by
    have hstep : δ * (K : ℝ) ≤ δ * (K : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hKone (mul_nonneg hδ.le hKr.le)
      nlinarith only [h]
    have hγsq : γ ^ 2 ≤ γ := by nlinarith only [hγ, hγone]
    have hγa := mul_le_mul_of_nonneg_right hγsq ha.le
    have hδK : 32 * (δ * (K : ℝ)) ≤ γ * a := by
      calc
        _ ≤ 32 * (δ * (K : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ ≤ γ ^ 2 * a := by nlinarith only [hδprod]
        _ ≤ γ * a := hγa
    nlinarith only [hδK, mul_nonneg hγ.le ha.le]
  -- Incidence chooses its loss threshold only after the two coefficient scales.
  obtain ⟨τ, hτ, hconditional⟩ := hincidence s₀ δ hs₀ hδ (by linarith only [hδhalf])
  let H := 1 + (K : ℝ) / ρ
  let rO := γ ^ 2 * a / 2
  let rF := γ * a / 4
  let Q := 1 / rF ^ 2
  let Aerr := Q + H / τ
  let D := 1 + 4 * H / τ + 4 / rO ^ 2 + 4 * Aerr / ξ
  have hH : 0 < H := by dsimp [H]; positivity
  have hrO : 0 < rO := by dsimp [rO]; positivity
  have hrF : 0 < rF := by dsimp [rF]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hAerr : 0 ≤ Aerr := by dsimp [Aerr]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hDcomp : 4 * H / τ ≤ D := by
    have h₁ : 0 ≤ 4 / rO ^ 2 := by positivity
    have h₂ : 0 ≤ 4 * Aerr / ξ := by positivity
    dsimp [D]
    linarith
  have hDorient : 4 / rO ^ 2 ≤ D := by
    have h₁ : 0 ≤ 4 * H / τ := by positivity
    have h₂ : 0 ≤ 4 * Aerr / ξ := by positivity
    dsimp [D]
    linarith
  have hDerr : 4 * Aerr / ξ ≤ D := by
    have h₁ : 0 ≤ 4 * H / τ := by positivity
    have h₂ : 0 ≤ 4 / rO ^ 2 := by positivity
    dsimp [D]
    linarith
  have hHρ : 1 ≤ ρ * H := by
    have heq : ρ * H = ρ + (K : ℝ) := by dsimp [H]; field_simp
    rw [heq]
    linarith
  have hDsep : 2 / (ρ * τ) ≤ D := by
    apply le_trans _ hDcomp
    apply (div_le_div_iff₀ (mul_pos hρ hτ) hτ).mpr
    have h := mul_le_mul_of_nonneg_right hHρ hτ.le
    nlinarith only [h, hτ]
  refine ⟨a / 2, D, by positivity, hD, rfl, ?_⟩
  intro Ω _ μ _ d M m A z hpop hseparation hAunit hAstable B code hfeas L hL hactualloss
  let S : ExactSourceSupport M K → Finset (Fin M) := Subtype.val
  let w : ExactSourceSupport M K → ℝ := actualSourceSupportWeights μ z
  let ν : ExactSourceSupport M K → Measure Ω := fun s => sourceSupportConditionalLaw μ z s.1
  let residual : Ω → ℝ := fun x => ‖representationToEuclidean d (A.mulVec (z x)) -
    representationToEuclidean d (B.mulVec (code x))‖
  let loss : ExactSourceSupport M K → ℝ := actualConditionalSupportLoss μ A z B code
  have hresidual : Measurable residual :=
    (((representationToEuclidean d).continuous.measurable.comp
      (A.mulVecLin.continuous_of_finiteDimensional.measurable.comp hpop.measurable)).sub
      ((representationToEuclidean d).continuous.measurable.comp
        (B.mulVecLin.continuous_of_finiteDimensional.measurable.comp hfeas.2.2.1))).norm
  have hw : ∀ s, 0 ≤ w s := fun _ => measureReal_nonneg
  have hloss : ∀ s, 0 ≤ loss s := fun _ => ENNReal.toReal_nonneg
  have hsum : ∑ s, w s = 1 :=
    (sourceSupportWeights_nonneg_sum_one μ z hpop.measurable hpop.ae_support_card).2
  have hmix : μ = finiteSupportMixture w ν :=
    measure_eq_sum_sourceSupportConditionalLaw μ z hpop.measurable hpop.ae_support_card
  have hbound : (∫⁻ x, ENNReal.ofReal (residual x ^ 2) ∂finiteSupportMixture w ν) ≤
      ENNReal.ofReal L := by rw [← hmix]; exact hactualloss
  obtain ⟨hfinite, hweighted⟩ := weightedConditionalLoss_le_of_lintegral_mixture_le
    w ν (fun x => ENNReal.ofReal (residual x ^ 2)) hw L hL hbound
  change weightedConditionalLoss w loss ≤ L at hweighted
  have hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i :=
    hpop.ae_coefficient_bounds.mono (fun _ hx i => (hx i).1)
  have hmarg (i : Fin M) : featurePrevalence μ z i = supportMarginalWeight S w i :=
    featurePrevalence_eq_supportMarginalWeight μ z hpop.measurable hpop.ae_support_card hnonneg i
  have hsep (i j : Fin M) (hij : i ≠ j) (hi : 0 < supportMarginalWeight S w i) :
      ρ * supportMarginalWeight S w i ≤ supportSeparationWeight S w i j := by
    have heq : μ.real {x | 0 < z x i ∧ z x j = 0} =
        supportSeparationWeight S w i j :=
      featureSeparation_eq_supportSeparationWeight μ z
        hpop.measurable hpop.ae_support_card hnonneg i j
    rw [← hmarg i, ← heq]
    exact hseparation i j hij (by rwa [hmarg i])
  have hmass (s : ExactSourceSupport M K) (hs : 0 < w s) :
      μ (sourceSupportEvent z s.1) ≠ 0 := by
    intro hzero
    simp only [w, actualSourceSupportWeights, Measure.real, hzero,
      ENNReal.toReal_zero, lt_self_iff_false] at hs
  have hconditionalLoss (s : ExactSourceSupport M K) (hs : 0 < w s) :
      (∫⁻ x, ENNReal.ofReal (residual x ^ 2) ∂ν s) ≤ ENNReal.ofReal (loss s) := by
    change (∫⁻ x, ENNReal.ofReal (residual x ^ 2) ∂ν s) ≤
      ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (residual x ^ 2) ∂ν s).toReal)
    rw [ENNReal.ofReal_toReal (hfinite s hs)]
  have hsourceae (s : ExactSourceSupport M K) (hs : 0 < w s) :
      ∀ᵐ x ∂ν s, (∀ j, 0 ≤ z x j ∧ z x j ≤ 1) ∧ nonzeroSupport (z x) ⊆ S s := by
    filter_upwards [sourceSupportConditionalLaw_ae_of_ae μ z s.1 hpop.ae_coefficient_bounds,
      sourceSupportConditionalLaw_ae_support_eq μ z hpop.measurable s.1 (hmass s hs)] with x hx hsupport
    exact ⟨hx, hsupport.le⟩
  have htruth (i : Fin M) (s : ExactSourceSupport M K) (hs : 0 < w s) :
      (ν s).real {x | 0 < z x i} = if i ∈ S s then 1 else 0 :=
    sourceSupportConditionalLaw_feature_truth_of_ae_nonnegative μ z hpop.measurable hnonneg s.1 hs i
  have hsmall (i : Fin M) (hi : 0 < featurePrevalence μ z i)
      (hibudget : D * L ≤ featurePrevalence μ z i) :
      weightedConditionalLoss w loss < ρ * τ * supportMarginalWeight S w i := by
    have hcap : 2 * L / (ρ * τ) ≤ featurePrevalence μ z i := by
      calc
        _ = (2 / (ρ * τ)) * L := by ring
        _ ≤ D * L := mul_le_mul_of_nonneg_right hDsep hL
        _ ≤ _ := hibudget
    have hcap' := (div_le_iff₀ (mul_pos hρ hτ)).mp hcap
    have hpositive := mul_pos (mul_pos hρ hτ) hi
    rw [hmarg i] at hcap' hpositive
    nlinarith only [hcap', hpositive, hweighted]
  -- Match every good support at once, retaining its entire membership pattern.
  have hlocal (s : goodSupportIndices w loss τ) :
      ∃ T : Finset (Fin m), T.card = K ∧
        ‖(euclideanColumnSpan A (S s.1)).starProjection -
          (euclideanColumnSpan B T).starProjection‖ ≤ δ := by
    have hs := (mem_goodSupportIndices w loss τ s.1).mp s.2
    exact hconditional Ω μ d M m A z hpop.toBoundedSparsePopulation
      hpop.conditional_incidence hAunit hAstable B code hfeas s.1 (hmass s.1 hs.1)
      ((hconditionalLoss s.1 hs.1).trans (ENNReal.ofReal_le_ofReal hs.2))
  choose T hT hgap using hlocal
  have hScard : ∀ s, (S s).card ≤ K := fun s => s.property.le
  have hgap' (s : goodSupportIndices w loss τ) :
      ‖(euclideanColumnSpan A (S s.1)).starProjection -
        (euclideanColumnSpan B (T s)).starProjection‖ ≤
          q / (2 * (1 + 2 * (K : ℝ) / min γ γ)) := by
    simpa only [min_self] using (hgap s).trans hδgap
  obtain ⟨e, hmem⟩ := exists_support_membership_equiv_of_projector_bounds A B γ γ q
    (fun i => (hAunit i).le) (fun j => (hfeas.1 j).le)
    hAstable hfeas.2.1 hγ hγ hq hqone
    (fun s : goodSupportIndices w loss τ => S s.1) T
    (fun s => hScard s.1) (fun s => (hT s).le) hgap'
  let inclusion : {i : Fin M // 0 < featurePrevalence μ z i ∧ D * L ≤ featurePrevalence μ z i} →
      {i : Fin M // ∃ s : goodSupportIndices w loss τ, i ∈ S s.1} :=
    fun i => ⟨i.1, mem_good_support_union_of_separation_scale S w loss τ ρ
      hw hloss hτ hρ hρone i.1 (hsmall i.1 i.2.1 i.2.2)⟩
  let embedding : {i : Fin M // 0 < featurePrevalence μ z i ∧ D * L ≤ featurePrevalence μ z i} ↪ Fin m :=
    { toFun := fun i => (e (inclusion i)).1
      inj' := by
        intro i j hij
        apply Subtype.ext
        change (inclusion i).1 = (inclusion j).1
        exact congrArg Subtype.val (e.injective (Subtype.ext hij)) }
  refine ⟨embedding, ?_⟩
  intro i
  have hprevalence : 0 < supportMarginalWeight S w i.1 := by rw [← hmarg]; exact i.2.1
  have hreverse : ∀ j ∈ exceptionalCompanionSet S (goodSupportIndices w loss τ) i.1,
      ρ * supportMarginalWeight S w j ≤ supportSeparationWeight S w j i.1 := by
    intro j hj
    exact hsep j i.1 ((mem_exceptionalCompanionSet S _ i.1 j).mp hj).1
      (supportMarginalWeight_pos_of_exceptional S w _ i.1 j hw
        (fun s hs => ((mem_goodSupportIndices w loss τ s).mp hs).1) hj)
  have hcompBudget : H / τ * L ≤ supportMarginalWeight S w i.1 / 4 := by
    have h := (mul_le_mul_of_nonneg_right hDcomp hL).trans i.2.2
    rw [hmarg] at h
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    convert h using 1
    ring
  have horientBudget : L / rO ^ 2 ≤ supportMarginalWeight S w i.1 / 4 := by
    have h := (mul_le_mul_of_nonneg_right hDorient hL).trans i.2.2
    rw [hmarg] at h
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    convert h using 1
    ring
  have herrorBudget : Aerr * L ≤ (ξ / 4) * supportMarginalWeight S w i.1 := by
    have h : 4 * Aerr * L / ξ ≤ supportMarginalWeight S w i.1 := by
      rw [← hmarg]
      calc
        _ = (4 * Aerr / ξ) * L := by ring
        _ ≤ D * L := mul_le_mul_of_nonneg_right hDerr hL
        _ ≤ _ := i.2.2
    have h' := (div_le_iff₀ hξ).mp h
    nlinarith only [h']
  have houtside (s : ExactSourceSupport M K)
      (hs : s ∉ exceptionalSupportIndices S (goodSupportIndices w loss τ) i.1) :
      s ∈ goodSupportIndices w loss τ ∧
        Disjoint (S s) (exceptionalCompanionSet S (goodSupportIndices w loss τ) i.1) := by
    simpa only [mem_exceptionalSupportIndices, not_or, not_not] using hs
  -- A negative atom would force small residual samples into the coordinate lower tail.
  have hnotnegative : ¬ ‖representationToEuclidean d (A.col i.1) +
      representationToEuclidean d (B.col (embedding i))‖ ≤ q := by
    intro hnegative
    have hcond (s : ExactSourceSupport M K)
        (hs : s ∉ exceptionalSupportIndices S (goodSupportIndices w loss τ) i.1) :
        (ν s).real ({x | 0 < z x i.1} \ {x | rO < residual x}) ≤
          (ξ / 4) * (if i.1 ∈ S s then 1 else 0) := by
      have hsG := houtside s hs
      have hpos := ((mem_goodSupportIndices w loss τ s).mp hsG.1).1
      by_cases hi : i.1 ∈ S s
      · have helig : s ∈ eligibleSupportIndices S (goodSupportIndices w loss τ) i.1 :=
          (mem_eligibleSupportIndices S _ i.1 s).mpr ⟨hsG.1, hi, hsG.2⟩
        have hcoord : ∀ᵐ x ∂ν s,
            z x i.1 ≤ residual x / γ ^ 2 + 4 * δ * (K : ℝ) ^ 2 / γ ^ 2 := by
          filter_upwards [hsourceae s hpos] with x hx
          exact eligible_support_negative_orientation_bound A B S (goodSupportIndices w loss τ)
            T e hmem γ δ q hK hγ hγone hδ.le hqγ
            (fun j => (hAunit j).le) (fun j => (hfeas.1 j).le) hAstable hfeas.2.1
            (fun s _ => hScard s) (fun s => (hT s).le) hgap (inclusion i) ⟨s, hsG.1⟩
            helig hnegative (z x) hx.1 hx.2 (code x) (hfeas.2.2.2.1 x) (hfeas.2.2.2.2 x)
        have htail := hpop.conditional_coordinate_tail s (hmass s hpos) i.1 hi
        have hsmallres := small_residual_probability_le_of_negative_orientation (ν s)
          (fun x => z x i.1) residual γ a (4 * δ * (K : ℝ) ^ 2 / γ ^ 2) (ξ / 4)
          hγ hnegativeError hcoord htail
        rw [if_pos hi, mul_one]
        exact (measureReal_mono (show {x | 0 < z x i.1} \ {x | rO < residual x} ⊆
          {x | residual x ≤ rO} from by
            intro x hx
            change residual x ≤ rO
            exact le_of_not_gt hx.2)).trans hsmallres
      · have hzero : (ν s).real {x | 0 < z x i.1} = 0 := by
          simpa only [if_neg hi] using htruth i.1 s hpos
        rw [measureReal_mono_null Set.diff_subset hzero, if_neg hi, mul_zero]
    have hprev := finiteSupportMixture_prevalence_bound_of_small_residuals S w loss ν
      hw hsum hloss hScard τ ρ (ξ / 4) rO L hτ hρ (by positivity) hrO hL i.1
      {x | 0 < z x i.1} residual hresidual (htruth i.1) hreverse hcond hbound
    have hweightBudget : H / τ * weightedConditionalLoss w loss ≤ supportMarginalWeight S w i.1 / 4 :=
      (mul_le_mul_of_nonneg_left hweighted (by positivity)).trans hcompBudget
    have hstrict := mul_lt_mul_of_pos_right (show (1 / 2 : ℝ) < 1 - ξ / 4 by linarith only [hξone]) hprevalence
    change (1 - ξ / 4) * supportMarginalWeight S w i.1 ≤
      H / τ * weightedConditionalLoss w loss + L / rO ^ 2 at hprev
    linarith only [hprev, hweightBudget, horientBudget, hstrict]
  -- The same membership bijection isolates the source line and fixes its positive sign.
  have hline := (matched_good_support_line_projector_bound S w loss τ ρ hw hloss hτ hρ hρone
    A B γ γ q (fun j => (hAunit j).le) (fun j => (hfeas.1 j).le) hAstable hfeas.2.1
    hγ hγ hq hqone T hScard (fun s => (hT s).le) hgap' e hmem (inclusion i)
    (fun j hji => hsep i.1 j hji.symm hprevalence)
    (hsmall i.1 i.2.1 i.2.2)).2
  have hdichotomy := dictionary_atom_signed_distance_dichotomy A B i.1 (embedding i)
    (hAunit i.1) (hfeas.1 _) (q / 2) hline
  have htwice : 2 * (q / 2) = q := by ring
  rw [htwice] at hdichotomy
  have hpositive := hdichotomy.resolve_right hnotnegative
  constructor
  · have hsq := norm_sub_sq_real (representationToEuclidean d (A.col i.1))
      (representationToEuclidean d (B.col (embedding i)))
    rw [hAunit i.1, hfeas.1 (embedding i)] at hsq
    have hdist := (sq_le_sq₀ (norm_nonneg _) hq.le).mpr hpositive
    have hqsmall : q ^ 2 ≤ q := by nlinarith only [hq.le, hqone]
    have hξeq : ξ = 1 - η := rfl
    nlinarith only [hsq, hdist, hqsmall, hqξ, hξeq, hηone]
  · have hconditionalError (s : ExactSourceSupport M K)
        (hs : s ∉ exceptionalSupportIndices S (goodSupportIndices w loss τ) i.1) :
        (ν s).real ({x | 0 < z x i.1} ∆ {x | a / 2 < code x (embedding i)}) ≤
          (ξ / 4) * (if i.1 ∈ S s then 1 else 0) + Q * loss s := by
      have hsG := houtside s hs
      have hpos := ((mem_goodSupportIndices w loss τ s).mp hsG.1).1
      have hscale : loss s / (γ * a / 4) ^ 2 = Q * loss s := by dsimp [Q, rF]; ring
      apply classification_error_le_of_activation_bounds (ν s) {x | 0 < z x i.1}
        (measurableSet_lt measurable_const ((measurable_pi_apply i.1).comp hpop.measurable))
        (fun x => code x (embedding i)) ((measurable_pi_apply _).comp hfeas.2.2.1)
        (a / 2) (ξ / 4) (Q * loss s) (i.1 ∈ S s) (htruth i.1 s hpos)
      · intro hi
        have hj : embedding i ∉ T ⟨s, hsG.1⟩ :=
          fun hj => hi ((hmem (inclusion i) ⟨s, hsG.1⟩).mpr hj)
        have hcomparison : ∀ᵐ x ∂ν s,
            code x (embedding i) ≤ (residual x + δ * (K : ℝ)) / γ := by
          filter_upwards [hsourceae s hpos] with x hx
          exact absent_matched_coordinate_le_actual_residual (K := K) A B (S s) (T ⟨s, hsG.1⟩)
            γ δ hγ hδ.le (fun j => (hAunit j).le) hfeas.2.1 (hScard s) (hT ⟨s, hsG.1⟩).le (hgap ⟨s, hsG.1⟩)
            (z x) hx.1 hx.2 (code x) (hfeas.2.2.2.1 x) (embedding i) hj
        have hfp := coordinate_threshold_false_positive_le (ν s) (fun x => code x (embedding i))
          residual hresidual γ a (δ * (K : ℝ)) (loss s) hγ ha (hloss s)
          hcomparison hprojectionError (hconditionalLoss s hpos)
        simpa only [hscale] using hfp
      · intro hi
        have helig : s ∈ eligibleSupportIndices S (goodSupportIndices w loss τ) i.1 :=
          (mem_eligibleSupportIndices S _ i.1 s).mpr ⟨hsG.1, hi, hsG.2⟩
        have hcomparison : ∀ᵐ x ∂ν s,
            |code x (embedding i) - z x i.1| ≤ residual x / γ + a / 4 := by
          filter_upwards [hsourceae s hpos] with x hx
          have h := eligible_support_positive_orientation_bound A B S (goodSupportIndices w loss τ)
            T e hmem γ δ q hK hγ hγone hδ.le (fun j => (hAunit j).le) (fun j => (hfeas.1 j).le)
            hAstable hfeas.2.1 (fun s _ => hScard s) (fun s => (hT s).le) hgap
            (inclusion i) ⟨s, hsG.1⟩ helig hpositive (z x) hx.1 hx.2 (code x) (hfeas.2.2.2.1 x)
          exact h.trans (add_le_add le_rfl hpositiveError)
        have hfn := coordinate_threshold_false_negative_le (ν s) (fun x => z x i.1)
          (fun x => code x (embedding i)) residual hresidual γ a (ξ / 4) (loss s)
          hγ ha (hloss s) hcomparison
          (hpop.conditional_coordinate_tail s (hmass s hpos) i.1 hi) (hconditionalLoss s hpos)
        simpa only [hscale] using hfn
    have hbudget : (Q + (1 + (K : ℝ) / ρ) / τ) * weightedConditionalLoss w loss ≤
        (ξ / 2) / 2 * supportMarginalWeight S w i.1 := by
      change Aerr * weightedConditionalLoss w loss ≤ _
      have h := (mul_le_mul_of_nonneg_left hweighted hAerr).trans herrorBudget
      convert h using 1
      ring
    -- Sum activation errors and the loss-charged exceptional mass under that same matching.
    have hF1 := finiteSupportMixture_populationF1_ge_of_exceptional_supports S w loss ν
      hw hsum hloss hScard τ ρ (ξ / 4) Q (ξ / 2) hτ hρ (by positivity) hQ
      (by positivity) (by linarith only) i.1 {x | 0 < z x i.1} {x | a / 2 < code x (embedding i)}
      (measurableSet_lt measurable_const ((measurable_pi_apply i.1).comp hpop.measurable))
      (measurableSet_lt measurable_const ((measurable_pi_apply _).comp hfeas.2.2.1))
      (htruth i.1) hreverse hconditionalError hprevalence hbudget
    rw [← hmix] at hF1
    have hξeq : ξ = 1 - η := rfl
    linarith only [hF1, hξeq, hηone]

end PKG26AtomicFeatures
