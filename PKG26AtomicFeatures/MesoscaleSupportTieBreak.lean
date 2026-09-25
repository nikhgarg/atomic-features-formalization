import PKG26AtomicFeatures.FeatureSupportExpectation
import PKG26AtomicFeatures.MesoscaleWidthTwoRecovery
import PKG26AtomicFeatures.HierarchicalPopulationModel
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Attainment of the expected-support tie-break at width two

The number of nonzero coordinates is lower semicontinuous under continuous
code perturbations. Fatou's lemma preserves lower semicontinuity after
expectation. Thus actual canonical NNLS support size attains its minimum on
the compact set of primary risk-minimizing dictionaries. Almost-everywhere
uniqueness of every actual primary-optimal encoder extends the comparison
to all feasible primary optima, not just to canonical encoders.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set Filter
open scoped ENNReal Topology


theorem measurable_nonzeroSupport_card
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (u : Ω → FeatureVector m) (hu : Measurable u) :
    Measurable (fun x => ((nonzeroSupport (u x)).card : ℝ≥0∞)) :=
  (measurable_of_countable (fun S : Finset (Fin m) => (S.card : ℝ≥0∞))).comp
    (measurable_nonzeroSupport_comp u hu)

theorem expectedCodeSupportSize_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) {u v : Ω → FeatureVector m} (huv : u =ᵐ[μ] v) :
    expectedCodeSupportSize μ u = expectedCodeSupportSize μ v :=
  lintegral_congr_ae (huv.mono (fun _ h =>
    congrArg (fun v => ((nonzeroSupport v).card : ℝ≥0∞)) h))

/-- Finite width bounds the true expected support, with no integrability
assumption on the encoder. -/
theorem expectedCodeSupportSize_le
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (u : Ω → FeatureVector m) :
    expectedCodeSupportSize μ u ≤ (m : ℝ≥0∞) * μ Set.univ := by
  calc
    _ ≤ ∫⁻ _ : Ω, (m : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro x
      change ((nonzeroSupport (u x)).card : ℝ≥0∞) ≤ (m : ℝ≥0∞)
      exact_mod_cast (show (nonzeroSupport (u x)).card ≤ m by
        simpa only [Fintype.card_fin] using Finset.card_le_univ (nonzeroSupport (u x)))
    _ = _ := lintegral_const _

theorem expectedCodeSupportSize_le_width
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → FeatureVector m) :
    expectedCodeSupportSize μ u ≤ m := by
  simpa using expectedCodeSupportSize_le μ u

/-- Every coordinate nonzero at a limit remains nonzero nearby, so
support cardinality can only decrease at a limit. -/
theorem lowerSemicontinuous_nonzeroSupport_card
    {E : Type*} [TopologicalSpace E] {m : ℕ}
    (u : E → FeatureVector m) (hu : Continuous u) :
    LowerSemicontinuous (fun x => ((nonzeroSupport (u x)).card : ℝ≥0∞)) := by
  classical
  intro x t ht
  have hj (j : Fin m) : ∀ᶠ y in 𝓝 x, u x j ≠ 0 → u y j ≠ 0 := by
    by_cases hx : u x j = 0
    · exact Eventually.of_forall (fun _ h => (h hx).elim)
    · have hopen : IsOpen {y : E | u y j ≠ 0} :=
        isOpen_ne_fun ((continuous_apply j).comp hu) continuous_const
      have hevent : ∀ᶠ y in 𝓝 x, u y j ≠ 0 := hopen.mem_nhds hx
      exact hevent.mono (fun _ hy _ => hy)
  filter_upwards [Filter.eventually_all.mpr hj] with y hy
  apply ht.trans_le
  change ((nonzeroSupport (u x)).card : ℝ≥0∞) ≤ ((nonzeroSupport (u y)).card : ℝ≥0∞)
  exact_mod_cast Finset.card_le_card (show nonzeroSupport (u x) ⊆ nonzeroSupport (u y) from by
    intro j hj
    exact (mem_nonzeroSupport_iff (u y) j).mpr (hy j ((mem_nonzeroSupport_iff (u x) j).mp hj)))

/-- Fatou's lemma turns pointwise lower semicontinuity of finite code
support into lower semicontinuity of its actual expectation. -/
theorem lowerSemicontinuous_expectedCodeSupportSize
    {E Ω : Type*} [TopologicalSpace E] [FirstCountableTopology E] [MeasurableSpace Ω]
    {m : ℕ} (μ : Measure Ω) (u : E → Ω → FeatureVector m)
    (hmeas : ∀ B, Measurable (u B)) (hcont : ∀ x, Continuous (fun B => u B x)) :
    LowerSemicontinuous (fun B => expectedCodeSupportSize μ (u B)) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro B
  calc
    _ ≤ ∫⁻ x, liminf (fun C => ((nonzeroSupport (u C x)).card : ℝ≥0∞)) (𝓝 B) ∂μ := by
      apply lintegral_mono
      intro x
      exact (lowerSemicontinuous_nonzeroSupport_card (fun C => u C x) (hcont x)).le_liminf B
    _ ≤ _ := lintegral_liminf_le (fun C => measurable_nonzeroSupport_card (u C) (hmeas C))

/-- A continuous primary objective and lower semicontinuous secondary
objective have a lexicographic minimizer on a nonempty compact space. -/
theorem exists_primary_minimizer_minimizing_secondary
    {E : Type*} [TopologicalSpace E] [CompactSpace E] [Nonempty E]
    (f : E → ℝ) (g : E → ℝ≥0∞) (hf : Continuous f) (hg : LowerSemicontinuous g) :
    ∃ x, (∀ y, f x ≤ f y) ∧ ∀ y, (∀ z, f y ≤ f z) → g x ≤ g y := by
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set E).Nonempty)
    hf.continuousOn
  let S : Set E := {x | ∀ y, f x ≤ f y}
  have hS : IsClosed S := by
    have heq : S = ⋂ y : E, {x | f x ≤ f y} := by ext x; simp [S]
    rw [heq]
    exact isClosed_iInter (fun y => isClosed_le hf continuous_const)
  have hSne : S.Nonempty := ⟨a, fun y => ha (Set.mem_univ y)⟩
  obtain ⟨x, hx, hxmin⟩ := LowerSemicontinuousOn.exists_isMinOn hSne hS.isCompact
    (hg.lowerSemicontinuousOn S)
  exact ⟨x, hx, fun y hy => hxmin hy⟩

/-- The actual NNLS population risk on the fixed unit, half-stable
width-two class, for any finite-second-moment source law. -/
noncomputable def widthTwoPopulationRisk (μ : Measure (FeatureVector 3))
    (B : MesoscaleReferenceDictionary) : ℝ :=
  nonnegativeLeastSquaresPopulationRisk μ (representationToEuclidean 3) B.1 (1 / 2)
    (by norm_num) (B.2.2.global_bound_of_width_le (by norm_num))

theorem actualPopulationSquaredLoss_widthTwoEncoder
    (μ : Measure (FeatureVector 3))
    (hsecond : Integrable (fun z => ‖representationToEuclidean 3 z‖ ^ 2) μ)
    (B : MesoscaleReferenceDictionary) :
    actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) id B.1
      (mesoscaleWidthTwoEncoder B) = ENNReal.ofReal (widthTwoPopulationRisk μ B) := by
  simpa only [actualPopulationSquaredLoss, euclideanPopulationSquaredLoss, Matrix.one_mulVec,
    id_eq, widthTwoPopulationRisk, mesoscaleWidthTwoEncoder] using
    (ofReal_nonnegativeLeastSquaresPopulationRisk μ
      (representationToEuclidean 3).continuous.measurable hsecond B.1 (1 / 2) (by norm_num)
      (B.2.2.global_bound_of_width_le (by norm_num))).symm

/-- Every actual primary optimum induces a primary minimizing canonical
dictionary. The comparison reaches every feasible dictionary and code. -/
theorem actual_width_two_optimal_pair_minimizes_canonical_risk
    (μ : Measure (FeatureVector 3))
    (hsecond : Integrable (fun z => ‖representationToEuclidean 3 z‖ ^ 2) μ)
    (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2)
    (hopt : IsApproximatelyOptimalRecoveryPair μ
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    ∀ C : MesoscaleReferenceDictionary,
      widthTwoPopulationRisk μ ⟨B, hopt.1.1, hopt.1.2.1⟩ ≤ widthTwoPopulationRisk μ C := by
  let B' : MesoscaleReferenceDictionary := ⟨B, hopt.1.1, hopt.1.2.1⟩
  intro C
  have hcanonical : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) id B
      (mesoscaleWidthTwoEncoder B') ≤ actualPopulationSquaredLoss μ 1 id B u := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    simpa only [Matrix.one_mulVec, id_eq] using
      (nonnegativeLeastSquaresCode_isMinimizer B (1 / 2) (by norm_num)
        (hopt.1.2.1.global_bound_of_width_le (by norm_num)) (representationToEuclidean 3 z)).2
        (u z) (hopt.1.2.2.2.2 z)
  have hcomp := hopt.2 C.1 (mesoscaleWidthTwoEncoder C) (mesoscaleWidthTwoEncoder_feasible C)
  simp only [ENNReal.ofReal_one, one_mul] at hcomp
  have hle := hcanonical.trans hcomp
  change actualPopulationSquaredLoss _ _ _ B'.1 _ ≤ _ at hle
  rw [actualPopulationSquaredLoss_widthTwoEncoder μ hsecond,
    actualPopulationSquaredLoss_widthTwoEncoder μ hsecond] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))).mp hle

/-- A primary-minimizing canonical dictionary is an actual joint optimum
against every measurable nonnegative two-sparse competitor. -/
theorem widthTwoEncoder_optimal_of_minimizes_risk
    (μ : Measure (FeatureVector 3))
    (hsecond : Integrable (fun z => ‖representationToEuclidean 3 z‖ ^ 2) μ)
    (B : MesoscaleReferenceDictionary)
    (hmin : ∀ C, widthTwoPopulationRisk μ B ≤ widthTwoPopulationRisk μ C) :
    IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin 3) (Fin 3) ℝ)
      id B.1 (mesoscaleWidthTwoEncoder B) (1 / 2) 1 2 := by
  refine ⟨mesoscaleWidthTwoEncoder_feasible B, ?_⟩
  intro C v hC
  simp only [ENNReal.ofReal_one, one_mul]
  let C' : MesoscaleReferenceDictionary := ⟨C, hC.1, hC.2.1⟩
  have hcanonical : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) id C
      (mesoscaleWidthTwoEncoder C') ≤ actualPopulationSquaredLoss μ 1 id C v := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    simpa only [Matrix.one_mulVec, id_eq] using
      (nonnegativeLeastSquaresCode_isMinimizer C (1 / 2) (by norm_num)
        (hC.2.1.global_bound_of_width_le (by norm_num)) (representationToEuclidean 3 z)).2
        (v z) (hC.2.2.2.2 z)
  apply le_trans _ hcanonical
  change actualPopulationSquaredLoss _ _ _ B.1 _ ≤ actualPopulationSquaredLoss _ _ _ C'.1 _
  rw [actualPopulationSquaredLoss_widthTwoEncoder μ hsecond,
    actualPopulationSquaredLoss_widthTwoEncoder μ hsecond]
  exact ENNReal.ofReal_le_ofReal (hmin C')

/-- The actual width-two primary optimization has an attained
expected-support tie-break. The secondary comparison includes every actual
primary-optimal encoder, through almost-everywhere NNLS uniqueness. -/
theorem exists_width_two_optimal_pair_minimizing_expected_support
    (μ : Measure (FeatureVector 3))
    (hsecond : Integrable (fun z => ‖representationToEuclidean 3 z‖ ^ 2) μ) :
    ∃ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
      IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 ∧
      ∀ (C : Matrix (Fin 3) (Fin 2) ℝ) (v : FeatureVector 3 → FeatureVector 2),
        IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v (1 / 2) 1 2 →
        expectedCodeSupportSize μ u ≤ expectedCodeSupportSize μ v := by
  letI : CompactSpace MesoscaleReferenceDictionary :=
    isCompact_iff_compactSpace.mp (isCompact_unitSparseLowerStable 3 2 4 (1 / 2))
  letI : Nonempty MesoscaleReferenceDictionary := ⟨⟨mesoscaleBenchmarkDictionary,
    mesoscaleBenchmarkDictionary_unit, mesoscaleBenchmarkDictionary_stable⟩⟩
  letI : FirstCountableTopology (Matrix (Fin 3) (Fin 2) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 2 → ℝ))
  letI : FirstCountableTopology MesoscaleReferenceDictionary :=
    TopologicalSpace.Subtype.firstCountableTopology _
  have hdict : Continuous (fun B : MesoscaleReferenceDictionary =>
      (⟨B.1, B.2.2.global_bound_of_width_le (by norm_num)⟩ :
        GlobalStableDictionary 3 2 (1 / 2))) := continuous_subtype_val.subtype_mk _
  have hrisk : Continuous (widthTwoPopulationRisk μ) := by
    simpa only [widthTwoPopulationRisk] using
      (continuous_nonnegativeLeastSquaresPopulationRisk μ
        (representationToEuclidean 3).continuous.measurable hsecond (1 / 2) (by norm_num)).comp hdict
  have hcode (z : FeatureVector 3) : Continuous (fun B : MesoscaleReferenceDictionary =>
      mesoscaleWidthTwoEncoder B z) := by
    simpa only [mesoscaleWidthTwoEncoder, nonnegativeLeastSquaresEncoder, Function.comp_apply,
      stableDictionaryNNLSCode] using
      (continuous_stableDictionaryNNLSCode (1 / 2) (by norm_num)).comp
        (hdict.prodMk (continuous_const (y := representationToEuclidean 3 z)))
  have hsupport := lowerSemicontinuous_expectedCodeSupportSize μ mesoscaleWidthTwoEncoder
    (fun B => (mesoscaleWidthTwoEncoder_feasible B).2.2.1) hcode
  obtain ⟨B, hB, hsupportmin⟩ := exists_primary_minimizer_minimizing_secondary
    (widthTwoPopulationRisk μ) (fun B => expectedCodeSupportSize μ (mesoscaleWidthTwoEncoder B))
    hrisk hsupport
  refine ⟨B.1, mesoscaleWidthTwoEncoder B, widthTwoEncoder_optimal_of_minimizes_risk μ hsecond B hB, ?_⟩
  intro C v hopt
  let C' : MesoscaleReferenceDictionary := ⟨C, hopt.1.1, hopt.1.2.1⟩
  have hC : ∀ D, widthTwoPopulationRisk μ C' ≤ widthTwoPopulationRisk μ D :=
    actual_width_two_optimal_pair_minimizes_canonical_risk μ hsecond C v hopt
  have hae := hopt.ae_eq_nonnegativeLeastSquaresEncoder (by norm_num) (by norm_num)
    (by simpa only [Matrix.one_mulVec, id_eq] using (representationToEuclidean 3).continuous.measurable)
    (by simpa only [Matrix.one_mulVec, id_eq] using hsecond.lintegral_lt_top)
  have hae' : v =ᵐ[μ] mesoscaleWidthTwoEncoder C' := by
    simpa only [mesoscaleWidthTwoEncoder, nonnegativeLeastSquaresEncoder, Function.comp_def,
      Matrix.one_mulVec, id_eq] using hae
  exact (hsupportmin C' hC).trans_eq (expectedCodeSupportSize_congr_ae μ hae').symm

/-- The actual normalized mesoscale law has a finite second moment;
common scaling preserves the finite-moment calculation for the primitive law. -/
theorem integrable_mesoscaleScaledPopulation_secondMoment (δ θ H η : ℝ) :
    Integrable (fun z => ‖representationToEuclidean 3 z‖ ^ 2)
      (mesoscaleScaledPopulationLaw δ θ H η) := by
  apply (integrable_map_measure
    ((representationToEuclidean 3).continuous.measurable.norm.pow_const 2).aestronglyMeasurable
    (measurable_mesoscaleCoefficientScaling H).aemeasurable).mpr
  have h := (integrable_mesoscalePopulation_secondMoment δ θ H η).const_mul ((1 / (H + 1)) ^ 2)
  simpa only [Function.comp_def, mesoscaleCoefficientScaling, map_smul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] using h

/-- The literal scaled mesoscale population admits an actual primary
optimum with least expected support among all actual primary optima. The
objective is finite and at most two because the law is a probability measure.
No selected optimizer or secondary-minimum certificate is assumed. -/
theorem exists_mesoscale_scaled_width_two_support_tie_optimum
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    ∃ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
      IsApproximatelyOptimalRecoveryPair (mesoscaleScaledPopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 ∧
      expectedCodeSupportSize (mesoscaleScaledPopulationLaw δ θ H η) u ≤ 2 ∧
      ∀ (C : Matrix (Fin 3) (Fin 2) ℝ) (v : FeatureVector 3 → FeatureVector 2),
        IsApproximatelyOptimalRecoveryPair (mesoscaleScaledPopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v (1 / 2) 1 2 →
        expectedCodeSupportSize (mesoscaleScaledPopulationLaw δ θ H η) u ≤
          expectedCodeSupportSize (mesoscaleScaledPopulationLaw δ θ H η) v := by
  letI := mesoscaleScaledPopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  obtain ⟨B, u, hopt, htie⟩ := exists_width_two_optimal_pair_minimizing_expected_support
    (mesoscaleScaledPopulationLaw δ θ H η)
    (integrable_mesoscaleScaledPopulation_secondMoment δ θ H η)
  refine ⟨B, u, hopt, ?_, htie⟩
  exact expectedCodeSupportSize_le_width (mesoscaleScaledPopulationLaw δ θ H η) u

end PKG26AtomicFeatures
