import PKG26AtomicFeatures.HierarchicalSupportLaw
import PKG26AtomicFeatures.SupportConditioning
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# The actual hierarchical population law

The primitive support law is the pushforward of the actual input measure
under its observed source support. It equals the finite parent-law mixture
with independent fair full child choices. Conditional active coefficients
have exactly the uniform cube law. Marginals, separation probabilities, and
regularity are consequences of these sampling statements, not model fields.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- Finite source supports carry their discrete sigma algebra. -/
instance sourceSupportMeasurableSpace {M : ℕ} : MeasurableSpace (Finset (Fin M)) := ⊤

instance sourceSupportMeasurableSingletonClass {M : ℕ} :
    MeasurableSingletonClass (Finset (Fin M)) := ⟨fun _ => trivial⟩

/-- The observed support map is measurable for any measurable source code. -/
theorem measurable_nonzeroSupport_comp
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (z : Ω → FeatureVector M) (hz : Measurable z) :
    Measurable (fun x => nonzeroSupport (z x)) := by
  apply measurable_to_countable
  intro x
  exact measurableSet_sourceSupportEvent z hz (nonzeroSupport (z x))

/-- Actual discrete distribution of the hierarchy's finite support sampler. -/
noncomputable def hierarchicalDiscreteSupportLaw
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ) : Measure (Finset (Fin (N * 3))) :=
  ∑ sample : ι × (Fin N → Fin 2),
    ENNReal.ofReal (hierarchicalSupportWeight w sample) •
      Measure.dirac (hierarchicalSupportFamily P sample)

/-- The exact finite weighted probability of any support predicate. -/
theorem hierarchicalDiscreteSupportLaw_apply
    {ι : Type*} [Fintype ι] {N : ℕ}
    (P : ι → Finset (Fin N)) (w : ι → ℝ)
    (E : Finset (Fin (N * 3)) → Prop) [DecidablePred E] :
    hierarchicalDiscreteSupportLaw P w {S | E S} =
      ∑ sample : ι × (Fin N → Fin 2),
        if E (hierarchicalSupportFamily P sample) then
          ENNReal.ofReal (hierarchicalSupportWeight w sample) else 0 := by
  classical
  simp only [hierarchicalDiscreteSupportLaw, Measure.finset_sum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    Set.mem_setOf_eq, Pi.one_apply]
  apply Finset.sum_congr rfl
  intro sample _
  split_ifs <;> simp

/-- Sampling primitives for the paper's hierarchy. The parent law has exact
L-parent supports; children are sampled by the actual finite support law;
active values have the exact independent uniform coefficient law.
Nonnegative source values are retained on the original input domain. -/
structure HierarchicalPopulationModel
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector (N * 3))
    (P : ι → Finset (Fin N)) (w : ι → ℝ) (L : ℕ) (ρ : ℝ) : Prop where
  measurable : Measurable z
  nonnegative : ∀ᵐ x ∂μ, ∀ i, 0 ≤ z x i
  weight_nonnegative : ∀ s, 0 ≤ w s
  weight_sum : ∑ s, w s = 1
  parent_card : ∀ s, (P s).card = L
  parent_separation : ∀ i j, i ≠ j →
    ρ * supportMarginalWeight P w i ≤ supportSeparationWeight P w i j
  support_distribution : Measure.map (fun x => nonzeroSupport (z x)) μ =
    hierarchicalDiscreteSupportLaw P w
  conditional_uniform : ∀ S : ExactSourceSupport (N * 3) (2 * L),
    μ (sourceSupportEvent z S.1) ≠ 0 →
    Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) =
      uniformCubeCoefficientLaw (2 * L)

/-- The primitive pushforward law determines every actual support event. -/
theorem HierarchicalPopulationModel.support_event_probability
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ)
    (E : Finset (Fin (N * 3)) → Prop) [DecidablePred E] :
    μ {x | E (nonzeroSupport (z x))} =
      ∑ sample : ι × (Fin N → Fin 2),
        if E (hierarchicalSupportFamily P sample) then
          ENNReal.ofReal (hierarchicalSupportWeight w sample) else 0 := by
  calc
    _ = (Measure.map (fun x => nonzeroSupport (z x)) μ) {S | E S} :=
      (Measure.map_apply (measurable_nonzeroSupport_comp z hmodel.measurable)
        (Set.to_countable {S | E S}).measurableSet).symm
    _ = _ := by
      rw [hmodel.support_distribution]
      exact hierarchicalDiscreteSupportLaw_apply P w E

/-- The real-valued support probabilities are the actual finite real sums. -/
theorem HierarchicalPopulationModel.support_event_probability_real
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ)
    (E : Finset (Fin (N * 3)) → Prop) [DecidablePred E] :
    μ.real {x | E (nonzeroSupport (z x))} =
      ∑ sample : ι × (Fin N → Fin 2),
        if E (hierarchicalSupportFamily P sample) then hierarchicalSupportWeight w sample else 0 := by
  have hreal := congrArg ENNReal.toReal (hmodel.support_event_probability E)
  rw [ENNReal.toReal_sum (by
    intro sample _
    split_ifs <;> simp)] at hreal
  simpa only [apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_ofReal (hierarchicalSupportWeight_nonneg w hmodel.weight_nonnegative _)] using hreal

/-- Normalized parent weights and fair child choices make the actual input
measure a probability measure; this is not a separate model assumption. -/
theorem HierarchicalPopulationModel.isProbabilityMeasure
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) : IsProbabilityMeasure μ := by
  constructor
  have h := hmodel.support_event_probability (fun _ => True)
  simp only [if_true, Set.setOf_true] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ =>
      hierarchicalSupportWeight_nonneg w hmodel.weight_nonnegative s),
    hierarchicalSupportWeight_sum_one w hmodel.weight_sum, ENNReal.ofReal_one] at h
  exact h

/-- Every actual input has exactly 2L active atoms almost surely. -/
theorem HierarchicalPopulationModel.ae_support_card
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) :
    ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = 2 * L := by
  classical
  rw [ae_iff, hmodel.support_event_probability (fun S => ¬ S.card = 2 * L)]
  apply Finset.sum_eq_zero
  intro sample _
  have hcard := hierarchicalSupport_card_of_parent_card (P sample.1) sample.2
    (hmodel.parent_card sample.1)
  simp only [hierarchicalSupportFamily, hcard, not_true_eq_false, if_false]

/-- Actual feature prevalence equals the expanded hierarchy's weighted
support marginal, including for zero-prevalence features. -/
theorem HierarchicalPopulationModel.featurePrevalence_eq
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) (a : Fin (N * 3)) :
    featurePrevalence μ z a = supportMarginalWeight
      (hierarchicalSupportFamily P) (hierarchicalSupportWeight w) a := by
  classical
  have hevent : {x | 0 < z x a} =ᵐ[μ] {x | a ∈ nonzeroSupport (z x)} := by
    filter_upwards [hmodel.nonnegative] with x hx
    simp only [mem_nonzeroSupport_iff]
    exact propext ⟨ne_of_gt, fun hne => lt_of_le_of_ne (hx a) (Ne.symm hne)⟩
  have h := (measureReal_congr hevent).trans
    (hmodel.support_event_probability_real (fun S => a ∈ S))
  simpa only [featurePrevalence, supportMarginalWeight, supportFamilyWeight,
    Finset.sum_filter] using h

/-- Actual positive-versus-zero separation equals the finite support sum. -/
theorem HierarchicalPopulationModel.featureSeparation_eq
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) (a b : Fin (N * 3)) :
    μ.real {x | 0 < z x a ∧ z x b = 0} = supportSeparationWeight
      (hierarchicalSupportFamily P) (hierarchicalSupportWeight w) a b := by
  classical
  have hevent : {x | 0 < z x a ∧ z x b = 0} =ᵐ[μ]
      {x | a ∈ nonzeroSupport (z x) ∧ b ∉ nonzeroSupport (z x)} := by
    filter_upwards [hmodel.nonnegative] with x hx
    simp only [mem_nonzeroSupport_iff, not_not]
    apply propext
    exact and_congr ⟨ne_of_gt, fun hne => lt_of_le_of_ne (hx a) (Ne.symm hne)⟩ Iff.rfl
  have h := (measureReal_congr hevent).trans
    (hmodel.support_event_probability_real (fun S => a ∈ S ∧ b ∉ S))
  simpa only [supportSeparationWeight, supportFamilyWeight, Finset.sum_filter] using h

/-- The original parent marginal is the actual parent's prevalence. -/
theorem HierarchicalPopulationModel.parent_prevalence
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) (i : Fin N) :
    featurePrevalence μ z (hierarchicalParent i) = supportMarginalWeight P w i := by
  rw [hmodel.featurePrevalence_eq, hierarchical_parent_marginal]

/-- Each actual child has exactly half its parent's prevalence. -/
theorem HierarchicalPopulationModel.child_prevalence
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) (i : Fin N) (k : Fin 2) :
    featurePrevalence μ z (hierarchicalChild i k) = supportMarginalWeight P w i / 2 := by
  rw [hmodel.featurePrevalence_eq, hierarchical_child_marginal]

/-- The actual law quantitatively separates any target outside the source
atom's own family implications. -/
theorem HierarchicalPopulationModel.quantitative_separation
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ)
    (a b : Fin (N * 3)) (hb : b ∉ hierarchicalForcedAtoms a) :
    min ρ (1 / 2) * featurePrevalence μ z a ≤ μ.real {x | 0 < z x a ∧ z x b = 0} := by
  rw [hmodel.featurePrevalence_eq, hmodel.featureSeparation_eq]
  exact hierarchical_quantitative_separation P w hmodel.weight_nonnegative ρ
    hmodel.parent_separation a b hb

/-- An atom's parent and itself have zero actual separation probability. -/
theorem HierarchicalPopulationModel.separation_zero_of_forced
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ)
    (a b : Fin (N * 3)) (hb : b ∈ hierarchicalForcedAtoms a) :
    μ.real {x | 0 < z x a ∧ z x b = 0} = 0 := by
  rw [hmodel.featureSeparation_eq]
  apply (mem_forcedCompanionSet _ _ _ _).mp
  apply (mem_forcedCompanionSet_iff_positive_weight_occurrence
    (hierarchicalSupportFamily P) (hierarchicalSupportWeight w)
    (hierarchicalSupportWeight_nonneg w hmodel.weight_nonnegative) a b).mpr
  intro sample _ hsample
  exact hierarchicalForcedAtoms_subset_support (P sample.1) sample.2 a hsample hb

/-- Every actual pair either has zero separation or satisfies the uniform
positive separation alternative, without an assumption of positive prevalence. -/
theorem HierarchicalPopulationModel.zero_or_quantitative_separation
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) (a b : Fin (N * 3)) :
    μ.real {x | 0 < z x a ∧ z x b = 0} = 0 ∨
      min ρ (1 / 2) * featurePrevalence μ z a ≤ μ.real {x | 0 < z x a ∧ z x b = 0} := by
  classical
  by_cases hb : b ∈ hierarchicalForcedAtoms a
  · exact Or.inl (hmodel.separation_zero_of_forced a b hb)
  · exact Or.inr (hmodel.quantitative_separation a b hb)

/-- The forced companions computed from actual support-event probabilities
are exactly the explicit hierarchy, on every positive-prevalence atom. -/
theorem HierarchicalPopulationModel.forcedCompanionSet_eq
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) (hρ : 0 < ρ)
    (a : Fin (N * 3)) (ha : 0 < featurePrevalence μ z a) :
    forcedCompanionSet (fun S : ExactSourceSupport (N * 3) (2 * L) => S.1)
      (fun S => μ.real (sourceSupportEvent z S.1)) a = hierarchicalForcedAtoms a := by
  classical
  letI := hmodel.isProbabilityMeasure
  calc
    _ = forcedCompanionSet (hierarchicalSupportFamily P) (hierarchicalSupportWeight w) a := by
      ext b
      rw [mem_forcedCompanionSet, mem_forcedCompanionSet,
        ← featureSeparation_eq_supportSeparationWeight μ z hmodel.measurable
          hmodel.ae_support_card hmodel.nonnegative,
        hmodel.featureSeparation_eq]
    _ = _ := hierarchical_forcedCompanionSet P w hmodel.weight_nonnegative ρ hρ
      hmodel.parent_separation a (by simpa only [hmodel.featurePrevalence_eq] using ha)

/-- Exact uniform conditional coefficients provide bounded densities h=1.
The regular model's separation parameter is zero because parent-child
implications intentionally prevent positive separation for all distinct pairs. -/
theorem HierarchicalPopulationModel.regularSparsePopulation
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N L : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
    {P : ι → Finset (Fin N)} {w : ι → ℝ} {ρ : ℝ}
    (hmodel : HierarchicalPopulationModel μ z P w L ρ) :
    RegularSparsePopulation (K := 2 * L) μ z 0 (1 / 2) 2 := by
  refine ⟨hmodel.measurable, hmodel.ae_support_card, ?_, ?_⟩
  · intro a b _ _
    simp only [zero_mul]
    exact measureReal_nonneg
  · intro S hS
    refine ⟨fun _ => 1, measurable_const, ?_, ?_⟩
    · change Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) =
        (uniformCubeCoefficientLaw (2 * L)).withDensity 1
      rw [withDensity_one]
      exact hmodel.conditional_uniform S hS
    · apply Filter.Eventually.of_forall
      intro _
      norm_num

end PKG26AtomicFeatures
