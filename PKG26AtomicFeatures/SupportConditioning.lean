import PKG26AtomicFeatures.RegularPopulationModel
import PKG26AtomicFeatures.WeightedGoodSupports

/-!
# Conditioning the actual population on its source support

The conditional laws here are the model's normalized restrictions on the
original input space. Exact sparsity gives a finite measurable partition up
to a null set, hence an exact mixture decomposition of the population.
Zero-mass supports retain the model's original-measure branch and contribute
zero mixture weight.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The actual support event is measurable whenever the source feature map
is measurable. This does not assume a discrete topology on feature values. -/
theorem measurableSet_sourceSupportEvent
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (z : Ω → FeatureVector M) (hz : Measurable z) (S : Finset (Fin M)) :
    MeasurableSet (sourceSupportEvent z S) := by
  classical
  have heq : sourceSupportEvent z S =
      ⋂ i : Fin M, {x | z x i ≠ 0 ↔ i ∈ S} := by
    ext x
    simp only [sourceSupportEvent, Set.mem_setOf_eq, Set.mem_iInter,
      Finset.ext_iff, mem_nonzeroSupport_iff]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  have hzero : MeasurableSet {x | z x i = 0} :=
    measurableSet_eq_fun ((measurable_pi_apply i).comp hz) measurable_const
  by_cases hi : i ∈ S
  · simpa only [hi, iff_true] using hzero.compl
  · simpa only [hi, iff_false, not_not] using hzero

/-- Every conditional law in the model is a probability law, including
the specified original-measure branch for a null support event. -/
instance sourceSupportConditionalLaw_isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → FeatureVector M) (S : Finset (Fin M)) :
    IsProbabilityMeasure (sourceSupportConditionalLaw μ z S) := by
  constructor
  by_cases hzero : μ (sourceSupportEvent z S) = 0
  · simp only [sourceSupportConditionalLaw, if_pos hzero, measure_univ]
  · rw [sourceSupportConditionalLaw, if_neg hzero, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ, ENNReal.inv_mul_cancel hzero (by finiteness)]

/-- Normalizing a support restriction and multiplying by its actual mass
recovers that restriction exactly, including at zero mass. -/
theorem sourceSupportWeight_smul_conditionalLaw
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (S : Finset (Fin M)) :
    ENNReal.ofReal (μ.real (sourceSupportEvent z S)) • sourceSupportConditionalLaw μ z S =
      μ.restrict (sourceSupportEvent z S) := by
  rw [ofReal_measureReal]
  by_cases hzero : μ (sourceSupportEvent z S) = 0
  · rw [hzero, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hzero).symm
  · rw [sourceSupportConditionalLaw, if_neg hzero, smul_smul,
      ENNReal.mul_inv_cancel hzero (by finiteness), one_smul]

/-- Distinct exact support events are disjoint as subsets of the actual
input domain. -/
theorem sourceSupportEvent_pairwise_disjoint
    {Ω : Type*} {M K : ℕ} (z : Ω → FeatureVector M) :
    Pairwise fun S T : ExactSourceSupport M K =>
      Disjoint (sourceSupportEvent z S.1) (sourceSupportEvent z T.1) := by
  intro S T hST
  apply Set.disjoint_left.mpr
  intro x hxS hxT
  exact hST (Subtype.ext (hxS.symm.trans hxT))

/-- Almost-sure exact sparsity says that the exact-support events cover
almost every input, without requiring every possible support to have mass. -/
theorem ae_mem_iUnion_sourceSupportEvent
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K) :
    ∀ᵐ x ∂μ, x ∈ ⋃ S : ExactSourceSupport M K, sourceSupportEvent z S.1 := by
  filter_upwards [hexact] with x hx
  exact Set.mem_iUnion.mpr ⟨⟨nonzeroSupport (z x), hx⟩, rfl⟩

/-- The original measure is the finite sum of its actual support
restrictions. No conditional witnesses are postulated. -/
theorem measure_eq_sum_sourceSupport_restrict
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K) :
    μ = ∑ S : ExactSourceSupport M K, μ.restrict (sourceSupportEvent z S.1) := by
  classical
  have hcover := Measure.restrict_eq_self_of_ae_mem (ae_mem_iUnion_sourceSupportEvent μ z hexact)
  have hsplit := Measure.restrict_iUnion (μ := μ) (sourceSupportEvent_pairwise_disjoint z)
    (fun S : ExactSourceSupport M K => measurableSet_sourceSupportEvent z hz S.1)
  rw [hcover, Measure.sum_fintype] at hsplit
  exact hsplit

/-- The support weights are nonnegative real numbers summing to one. -/
theorem sourceSupportWeights_nonneg_sum_one
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K) :
    (∀ S : ExactSourceSupport M K, 0 ≤ μ.real (sourceSupportEvent z S.1)) ∧
      ∑ S : ExactSourceSupport M K, μ.real (sourceSupportEvent z S.1) = 1 := by
  classical
  refine ⟨fun _ => measureReal_nonneg, ?_⟩
  have htotal := congrArg (fun ν : Measure Ω => ν Set.univ)
    (measure_eq_sum_sourceSupport_restrict μ z hz hexact)
  simp only [measure_univ, Measure.finset_sum_apply, Measure.restrict_apply_univ] at htotal
  have hreal := congrArg ENNReal.toReal htotal.symm
  rw [ENNReal.toReal_sum (by
    intro S _
    exact measure_ne_top μ (sourceSupportEvent z S.1)), ENNReal.toReal_one] at hreal
  exact hreal

/-- Exact support conditioning recovers the original population as a finite
mixture, with weights equal to the actual probabilities of support events. -/
theorem measure_eq_sum_sourceSupportConditionalLaw
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K) :
    μ = ∑ S : ExactSourceSupport M K,
      ENNReal.ofReal (μ.real (sourceSupportEvent z S.1)) • sourceSupportConditionalLaw μ z S.1 := by
  simpa only [sourceSupportWeight_smul_conditionalLaw] using
    measure_eq_sum_sourceSupport_restrict μ z hz hexact

/-- Conditional almost-sure support is exact whenever its mixture weight
is positive. No such assertion is made for the null-event branch. -/
theorem sourceSupportConditionalLaw_ae_support_eq
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (hz : Measurable z)
    (S : Finset (Fin M)) (hpos : μ (sourceSupportEvent z S) ≠ 0) :
    ∀ᵐ x ∂sourceSupportConditionalLaw μ z S, nonzeroSupport (z x) = S := by
  rw [sourceSupportConditionalLaw, if_neg hpos]
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_sourceSupportEvent z hz S)) _

/-- Reading selected coordinates and transporting to Euclidean space is
measurable on the original input domain. -/
theorem measurable_sourceSupportCoordinates
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (z : Ω → FeatureVector M) (hz : Measurable z) (S : ExactSourceSupport M K) :
    Measurable (sourceSupportCoordinates z S) := by
  apply (representationToEuclidean K).continuous.measurable.comp
  exact measurable_pi_lambda _ fun j => (measurable_pi_apply (sourceSupportEnumeration S j)).comp hz

/-- On its actual support event, the selected source map applied to the
selected coefficients equals the original matrix-vector representation. -/
theorem selectedSourceSynthesis_sourceSupportCoordinates
    {Ω : Type*} {d M K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (S : ExactSourceSupport M K) (x : Ω) (hx : x ∈ sourceSupportEvent z S.1) :
    selectedSourceSynthesis A (sourceSupportEnumeration S) (sourceSupportCoordinates z S x) =
      representationToEuclidean d (A.mulVec (z x)) := by
  rw [selectedSourceSynthesis_apply]
  change representationToEuclidean d (A.mulVec (insertSupportCode (sourceSupportEnumeration S)
    ((representationToEuclidean K).symm (representationToEuclidean K
      (fun j => z x (sourceSupportEnumeration S j)))))) = _
  rw [(representationToEuclidean K).symm_apply_apply, insertSupportCode_restrict]
  rw [sourceSupportEnumeration_image]
  exact hx.le

/-- The exact reconstruction identity holds almost surely under every
positive-mass conditional source law. -/
theorem sourceSupportConditionalLaw_ae_synthesis_eq
    {Ω : Type*} [MeasurableSpace Ω] {d M K : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin d) (Fin M) ℝ)
    (z : Ω → FeatureVector M) (hz : Measurable z) (S : ExactSourceSupport M K)
    (hpos : μ (sourceSupportEvent z S.1) ≠ 0) :
    ∀ᵐ x ∂sourceSupportConditionalLaw μ z S.1,
      selectedSourceSynthesis A (sourceSupportEnumeration S) (sourceSupportCoordinates z S x) =
        representationToEuclidean d (A.mulVec (z x)) := by
  filter_upwards [sourceSupportConditionalLaw_ae_support_eq μ z hz S.1 hpos] with x hx
  exact selectedSourceSynthesis_sourceSupportCoordinates A z S x hx

/-- Every nonnegative extended integral decomposes over the actual support
mixture. In particular, this applies directly to squared reconstruction loss. -/
theorem lintegral_eq_sum_sourceSupportConditionalLaw
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K) (f : Ω → ℝ≥0∞) :
    (∫⁻ x, f x ∂μ) = ∑ S : ExactSourceSupport M K,
      ENNReal.ofReal (μ.real (sourceSupportEvent z S.1)) *
        ∫⁻ x, f x ∂sourceSupportConditionalLaw μ z S.1 := by
  conv_lhs => rw [measure_eq_sum_sourceSupportConditionalLaw μ z hz hexact]
  rw [lintegral_finset_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

/-- Finite population loss makes every actual conditional loss finite.
For a null support this follows from the specified original-law branch. -/
theorem lintegral_sourceSupportConditionalLaw_ne_top
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (S : Finset (Fin M))
    (f : Ω → ℝ≥0∞) (hfinite : (∫⁻ x, f x ∂μ) ≠ ∞) :
    (∫⁻ x, f x ∂sourceSupportConditionalLaw μ z S) ≠ ∞ := by
  by_cases hzero : μ (sourceSupportEvent z S) = 0
  · simpa only [sourceSupportConditionalLaw, if_pos hzero] using hfinite
  · rw [sourceSupportConditionalLaw, if_neg hzero, lintegral_smul_measure, smul_eq_mul]
    apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hzero)
    exact ne_top_of_le_ne_top hfinite (setLIntegral_le_lintegral _ _)

/-- Taking real values of a finite population loss gives precisely the
finite weighted sum consumed by the good-support selection lemmas. -/
theorem lintegral_toReal_eq_sum_sourceSupportConditionalLaw
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (f : Ω → ℝ≥0∞) (hfinite : (∫⁻ x, f x ∂μ) ≠ ∞) :
    (∫⁻ x, f x ∂μ).toReal = ∑ S : ExactSourceSupport M K,
      μ.real (sourceSupportEvent z S.1) *
        (∫⁻ x, f x ∂sourceSupportConditionalLaw μ z S.1).toReal := by
  have hsum := congrArg ENNReal.toReal
    (lintegral_eq_sum_sourceSupportConditionalLaw μ z hz hexact f)
  rw [ENNReal.toReal_sum (by
    intro S _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lintegral_sourceSupportConditionalLaw_ne_top μ z S.1 f hfinite))] at hsum
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal measureReal_nonneg] using hsum

/-- Every event determined by the source support has the expected finite
weighted probability. The predicate is evaluated on actual support sets. -/
theorem measureReal_support_predicate_eq_sum
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (P : Finset (Fin M) → Prop) [DecidablePred P] :
    μ.real {x | P (nonzeroSupport (z x))} =
      ∑ S : ExactSourceSupport M K, if P S.1 then μ.real (sourceSupportEvent z S.1) else 0 := by
  classical
  have heval (S : ExactSourceSupport M K) :
      (μ.restrict (sourceSupportEvent z S.1)) {x | P (nonzeroSupport (z x))} =
        if P S.1 then μ (sourceSupportEvent z S.1) else 0 := by
    rw [Measure.restrict_apply' (measurableSet_sourceSupportEvent z hz S.1)]
    have hinter : {x | P (nonzeroSupport (z x))} ∩ sourceSupportEvent z S.1 =
        if P S.1 then sourceSupportEvent z S.1 else ∅ := by
      ext x
      by_cases hp : P S.1
      · simp only [if_pos hp, Set.mem_inter_iff, Set.mem_setOf_eq]
        exact ⟨And.right, fun hx => ⟨hx.symm ▸ hp, hx⟩⟩
      · simp only [if_neg hp, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hx hxS
        exact hp (hxS ▸ hx)
    rw [hinter]
    split_ifs <;> simp
  have hsum := congrArg (fun ν : Measure Ω => ν {x | P (nonzeroSupport (z x))})
    (measure_eq_sum_sourceSupport_restrict μ z hz hexact)
  simp only [Measure.finset_sum_apply, heval] at hsum
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (by
    intro S _
    split_ifs
    · exact measure_ne_top μ _
    · exact ENNReal.zero_ne_top)] at hreal
  simpa only [ENNReal.toReal_zero, apply_ite ENNReal.toReal] using hreal

/-- Under nonnegative source coefficients, actual positive prevalence is
the weighted incidence marginal of the exact support family. -/
theorem featurePrevalence_eq_sum_sourceSupportWeights
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i) (i : Fin M) :
    featurePrevalence μ z i = ∑ S : ExactSourceSupport M K,
      if i ∈ S.1 then μ.real (sourceSupportEvent z S.1) else 0 := by
  have hevent : {x | 0 < z x i} =ᵐ[μ] {x | i ∈ nonzeroSupport (z x)} := by
    filter_upwards [hnonneg] with x hx
    simp only [mem_nonzeroSupport_iff]
    exact propext ⟨ne_of_gt, fun hne => lt_of_le_of_ne (hx i) (Ne.symm hne)⟩
  exact (measureReal_congr hevent).trans (measureReal_support_predicate_eq_sum μ z hz hexact
    (fun S => i ∈ S))

/-- Pairwise separation probability is exactly the finite weighted mass of
supports containing the first feature and excluding the second. -/
theorem featureSeparation_eq_sum_sourceSupportWeights
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i) (i j : Fin M) :
    μ.real {x | 0 < z x i ∧ z x j = 0} = ∑ S : ExactSourceSupport M K,
      if i ∈ S.1 ∧ j ∉ S.1 then μ.real (sourceSupportEvent z S.1) else 0 := by
  have hevent : {x | 0 < z x i ∧ z x j = 0} =ᵐ[μ]
      {x | i ∈ nonzeroSupport (z x) ∧ j ∉ nonzeroSupport (z x)} := by
    filter_upwards [hnonneg] with x hx
    simp only [mem_nonzeroSupport_iff, not_not]
    apply propext
    exact and_congr ⟨ne_of_gt, fun hne => lt_of_le_of_ne (hx i) (Ne.symm hne)⟩ Iff.rfl
  exact (measureReal_congr hevent).trans
    (measureReal_support_predicate_eq_sum μ z hz hexact (fun S => i ∈ S ∧ j ∉ S))

/-- On a positive-weight conditional support law, actual source-feature
truth has probability one precisely for the atoms in that support. -/
theorem sourceSupportConditionalLaw_feature_truth
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hnonneg : ∀ x i, 0 ≤ z x i) (S : Finset (Fin M))
    (hpos : 0 < μ.real (sourceSupportEvent z S)) (i : Fin M) :
    (sourceSupportConditionalLaw μ z S).real {x | 0 < z x i} =
      if i ∈ S then 1 else 0 := by
  classical
  have hmass : μ (sourceSupportEvent z S) ≠ 0 := by
    intro hzero
    simp only [Measure.real, hzero, ENNReal.toReal_zero, lt_self_iff_false] at hpos
  have htruth : ∀ᵐ x ∂sourceSupportConditionalLaw μ z S, 0 < z x i ↔ i ∈ S := by
    filter_upwards [sourceSupportConditionalLaw_ae_support_eq μ z hz S hmass] with x hx
    rw [← hx, mem_nonzeroSupport_iff]
    exact ⟨ne_of_gt, fun hne => lt_of_le_of_ne (hnonneg x i) (Ne.symm hne)⟩
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

/-- The actual prevalence is the marginal used by finite weighted
good-support selection, with the actual support-event probabilities. -/
theorem featurePrevalence_eq_supportMarginalWeight
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i) (i : Fin M) :
    featurePrevalence μ z i =
      supportMarginalWeight (fun S : ExactSourceSupport M K => S.1)
        (fun S => μ.real (sourceSupportEvent z S.1)) i := by
  classical
  simpa only [supportMarginalWeight, supportFamilyWeight, Finset.sum_filter] using
    featurePrevalence_eq_sum_sourceSupportWeights μ z hz hexact hnonneg i

/-- The actual separation probability is the separation mass used by the
finite weighted singleton-intersection theorem. -/
theorem featureSeparation_eq_supportSeparationWeight
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : Ω → FeatureVector M) (hz : Measurable z)
    (hexact : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = K)
    (hnonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i) (i j : Fin M) :
    μ.real {x | 0 < z x i ∧ z x j = 0} =
      supportSeparationWeight (fun S : ExactSourceSupport M K => S.1)
        (fun S => μ.real (sourceSupportEvent z S.1)) i j := by
  classical
  simpa only [supportSeparationWeight, supportFamilyWeight, Finset.sum_filter] using
    featureSeparation_eq_sum_sourceSupportWeights μ z hz hexact hnonneg i j

end PKG26AtomicFeatures
