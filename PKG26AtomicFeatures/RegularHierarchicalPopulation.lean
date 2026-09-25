import PKG26AtomicFeatures.HierarchicalPopulationModel
import PKG26AtomicFeatures.RegularPopulationModulus

/-!
# Hierarchical populations with correlated child choices

A sample consists of an exact-L family set and a full vector of binary child
choices. Its probability weight is arbitrary: neither choices across families
nor active coefficients are required to be independent. Choices on inactive
families do not affect the atomic support. Child balance is imposed conditional
on each family set, by its equivalent undivided finite-probability inequality.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The finite outcomes of the family and child sampler. -/
abbrev HierarchicalJointSample (N L : ℕ) :=
  ExactSourceSupport N L × (Fin N → Fin 2)

/-- Marginal probability of an exact-L active family set. -/
noncomputable def hierarchicalFamilyWeight {N L : ℕ}
    (w : HierarchicalJointSample N L → ℝ) (F : ExactSourceSupport N L) : ℝ :=
  ∑ choice, w (F, choice)

/-- The atomic support induced by an arbitrary joint family and child sample. -/
def hierarchicalJointSupport {N L : ℕ} (s : HierarchicalJointSample N L) :
    Finset (Fin (N * 3)) := hierarchicalSupport s.1.1 s.2

/-- Pushforward of the finite joint sampler to its actual atomic supports. -/
noncomputable def hierarchicalJointSupportLaw {N L : ℕ}
    (w : HierarchicalJointSample N L → ℝ) : Measure (Finset (Fin (N * 3))) :=
  ∑ s, ENNReal.ofReal (w s) • Measure.dirac (hierarchicalJointSupport s)

/-- The authored hierarchical regularity primitives. The arbitrary joint
weights specify the full support law. Child balance conditions on the unique
family set, not on a more informative latent sample. Null family sets satisfy
the undivided balance inequality automatically. The conditional density is a
joint density on all 2L active coordinates. -/
structure RegularHierarchicalPopulation
    {Ω : Type*} [MeasurableSpace Ω] {N L : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector (N * 3))
    (w : HierarchicalJointSample N L → ℝ) (ρ κ cLower cUpper : ℝ) : Prop where
  measurable : Measurable z
  weight_nonnegative : ∀ s, 0 ≤ w s
  weight_sum : ∑ s, w s = 1
  parent_separation : ∀ i j, i ≠ j →
    ρ * supportMarginalWeight (fun F : ExactSourceSupport N L => F.1)
      (hierarchicalFamilyWeight w) i ≤
    supportSeparationWeight (fun F : ExactSourceSupport N L => F.1)
      (hierarchicalFamilyWeight w) i j
  child_balance : ∀ (F : ExactSourceSupport N L) (i : Fin N), i ∈ F.1 → ∀ k : Fin 2,
    κ * hierarchicalFamilyWeight w F ≤ ∑ choice, if choice i = k then w (F, choice) else 0
  support_distribution : Measure.map (fun x => nonzeroSupport (z x)) μ =
    hierarchicalJointSupportLaw w
  conditional_density : ∀ S : ExactSourceSupport (N * 3) (2 * L),
    μ (sourceSupportEvent z S.1) ≠ 0 →
    ∃ h : EuclideanRepresentation (2 * L) → ℝ≥0∞, Measurable h ∧
      Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) =
        (uniformCubeCoefficientLaw (2 * L)).withDensity h ∧
      (∀ᵐ a ∂uniformCubeCoefficientLaw (2 * L),
        ENNReal.ofReal cLower ≤ h a ∧ h a ≤ ENNReal.ofReal cUpper)

variable {Ω : Type*} [MeasurableSpace Ω] {N L : ℕ}
  {μ : Measure Ω} {z : Ω → FeatureVector (N * 3)}
  {w : HierarchicalJointSample N L → ℝ} {ρ κ cLower cUpper : ℝ}

/-- Every support event is evaluated under the actual joint sampler. -/
theorem RegularHierarchicalPopulation.support_event_probability
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper)
    (E : Finset (Fin (N * 3)) → Prop) [DecidablePred E] :
    μ {x | E (nonzeroSupport (z x))} =
      ∑ s, if E (hierarchicalJointSupport s) then ENNReal.ofReal (w s) else 0 := by
  classical
  calc
    _ = (Measure.map (fun x => nonzeroSupport (z x)) μ) {S | E S} :=
      (Measure.map_apply (measurable_nonzeroSupport_comp z hmodel.measurable)
        (Set.to_countable {S | E S}).measurableSet).symm
    _ = _ := by
      rw [hmodel.support_distribution]
      simp only [hierarchicalJointSupportLaw, Measure.finset_sum_apply,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
        Set.mem_setOf_eq, Pi.one_apply]
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp

/-- Actual real support probabilities are finite sums of joint weights. -/
theorem RegularHierarchicalPopulation.support_event_probability_real
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper)
    (E : Finset (Fin (N * 3)) → Prop) [DecidablePred E] :
    μ.real {x | E (nonzeroSupport (z x))} =
      ∑ s, if E (hierarchicalJointSupport s) then w s else 0 := by
  have h := congrArg ENNReal.toReal (hmodel.support_event_probability E)
  rw [ENNReal.toReal_sum (by intro s _; split_ifs <;> simp)] at h
  simpa only [apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_ofReal (hmodel.weight_nonnegative _)] using h

/-- Normalized joint weights make the original population a probability law. -/
theorem RegularHierarchicalPopulation.isProbabilityMeasure
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper) :
    IsProbabilityMeasure μ := by
  constructor
  have h := hmodel.support_event_probability (fun _ => True)
  simp only [if_true, Set.setOf_true] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hmodel.weight_nonnegative s),
    hmodel.weight_sum, ENNReal.ofReal_one] at h
  exact h

/-- Exactly L families, each with a parent and one child, give exact 2L sparsity. -/
theorem RegularHierarchicalPopulation.ae_support_card
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper) :
    ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card = 2 * L := by
  classical
  rw [ae_iff, hmodel.support_event_probability (fun S => ¬ S.card = 2 * L)]
  apply Finset.sum_eq_zero
  intro s _
  have hcard := hierarchicalSupport_card_of_parent_card s.1.1 s.2 s.1.2
  simp only [hierarchicalJointSupport, hcard, not_true_eq_false, if_false]

/-- Conditional densities instantiate the regular model with separation zero.
No positive separation between a child and its forced parent is assumed. -/
theorem RegularHierarchicalPopulation.regularSparsePopulation
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper) :
    RegularSparsePopulation (K := 2 * L) μ z 0 cLower cUpper := by
  refine ⟨hmodel.measurable, hmodel.ae_support_card, ?_, hmodel.conditional_density⟩
  intro i j _ _
  simpa only [zero_mul] using (measureReal_nonneg : 0 ≤ μ.real {x | 0 < z x i ∧ z x j = 0})

/-- Cube density bounds imply the source coefficient bounds almost surely. -/
theorem RegularHierarchicalPopulation.boundedSparsePopulation
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper) :
    BoundedSparsePopulation (K := 2 * L) μ z := by
  letI := hmodel.isProbabilityMeasure
  exact hmodel.regularSparsePopulation.boundedSparsePopulation

/-- A common upper density bound gives the dimension-independent slab modulus. -/
theorem RegularHierarchicalPopulation.modulusSparsePopulation
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper)
    (hcUpper : 0 ≤ cUpper) :
    ModulusSparsePopulation (K := 2 * L) μ z
      (fun s => cUpper * uniformCubeSlabModulus (2 * L) s) := by
  letI := hmodel.isProbabilityMeasure
  exact hmodel.regularSparsePopulation.modulusSparsePopulation hcUpper

/-- Positive-coordinate prevalence agrees with the actual support marginal. -/
theorem RegularHierarchicalPopulation.featurePrevalence_eq
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper)
    (a : Fin (N * 3)) :
    featurePrevalence μ z a = ∑ s, if a ∈ hierarchicalJointSupport s then w s else 0 := by
  classical
  have hevent : {x | 0 < z x a} =ᵐ[μ] {x | a ∈ nonzeroSupport (z x)} := by
    filter_upwards [hmodel.boundedSparsePopulation.ae_coefficient_bounds] with x hx
    simp only [mem_nonzeroSupport_iff]
    exact propext ⟨ne_of_gt, fun hne => lt_of_le_of_ne (hx a).1 (Ne.symm hne)⟩
  exact (measureReal_congr hevent).trans
    (hmodel.support_event_probability_real (fun S => a ∈ S))

/-- The parent prevalence is the marginal of the active-family law. -/
theorem RegularHierarchicalPopulation.parent_prevalence
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper) (i : Fin N) :
    featurePrevalence μ z (hierarchicalParent i) =
      supportMarginalWeight (fun F : ExactSourceSupport N L => F.1)
        (hierarchicalFamilyWeight w) i := by
  classical
  rw [hmodel.featurePrevalence_eq, Fintype.sum_prod_type]
  simp only [hierarchicalJointSupport, mem_hierarchicalSupport_parent,
    supportMarginalWeight, supportFamilyWeight, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hi : i ∈ F.1 <;> simp [hi, hierarchicalFamilyWeight]

/-- Each child's actual prevalence is at least κ times its parent's. -/
theorem RegularHierarchicalPopulation.child_prevalence_ge
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper)
    (i : Fin N) (k : Fin 2) :
    κ * featurePrevalence μ z (hierarchicalParent i) ≤
      featurePrevalence μ z (hierarchicalChild i k) := by
  classical
  rw [hmodel.parent_prevalence, hmodel.featurePrevalence_eq, Fintype.sum_prod_type]
  simp only [supportMarginalWeight, supportFamilyWeight, Finset.sum_filter,
    hierarchicalJointSupport, mem_hierarchicalSupport_child, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro F _
  by_cases hi : i ∈ F.1
  · simpa only [hi, if_true, true_and] using hmodel.child_balance F i hi k
  · simp only [hi, if_false, false_and, mul_zero, Finset.sum_const_zero, le_refl]

/-- Exactly one child in every active family makes the two child prevalences
sum to the parent prevalence, independently of their joint choice law. -/
theorem RegularHierarchicalPopulation.child_prevalence_sum
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper) (i : Fin N) :
    featurePrevalence μ z (hierarchicalChild i 0) +
      featurePrevalence μ z (hierarchicalChild i 1) =
        featurePrevalence μ z (hierarchicalParent i) := by
  classical
  rw [hmodel.featurePrevalence_eq, hmodel.featurePrevalence_eq,
    hmodel.featurePrevalence_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [hierarchicalJointSupport, mem_hierarchicalSupport_child,
    mem_hierarchicalSupport_parent]
  have hchoice : s.2 i = 0 ∨ s.2 i = 1 := by omega
  rcases hchoice with h | h <;> by_cases hi : i ∈ s.1.1 <;> simp [h, hi]

/-- Every role, including the parent, has prevalence at least κ times the
parent prevalence when κ≤1. -/
theorem RegularHierarchicalPopulation.role_prevalence_ge
    (hmodel : RegularHierarchicalPopulation μ z w ρ κ cLower cUpper)
    (hκ : κ ≤ 1) (i : Fin N) (k : Fin 3) :
    κ * featurePrevalence μ z (hierarchicalParent i) ≤
      featurePrevalence μ z (finProdFinEquiv (i, k)) := by
  refine Fin.cases ?_ (fun k => hmodel.child_prevalence_ge i k) k
  change κ * featurePrevalence μ z (hierarchicalParent i) ≤
    featurePrevalence μ z (hierarchicalParent i)
  exact mul_le_of_le_one_left measureReal_nonneg hκ


/-- Every event of an arbitrary finite joint law is the sum of its singleton probabilities. -/
theorem hierarchicalJointMeasure_event {N L : ℕ}
    (ν : Measure (HierarchicalJointSample N L)) [IsFiniteMeasure ν]
    (E : HierarchicalJointSample N L → Prop) [DecidablePred E] :
    ν.real {s | E s} = ∑ s, if E s then ν.real {s} else 0 := by
  have hset : ((Finset.univ.filter E : Finset (HierarchicalJointSample N L)) : Set _) =
      {s | E s} := by ext s; simp
  rw [← hset, ← sum_measureReal_singleton, Finset.sum_filter]

/-- The family-set probability is exactly the marginal of the joint weights. -/
theorem hierarchicalJointMeasure_family {N L : ℕ}
    (ν : Measure (HierarchicalJointSample N L)) [IsFiniteMeasure ν]
    (F : ExactSourceSupport N L) :
    ν.real {s | s.1 = F} = hierarchicalFamilyWeight (fun s => ν.real {s}) F := by
  classical
  rw [hierarchicalJointMeasure_event, Fintype.sum_prod_type, Finset.sum_comm]
  simp [hierarchicalFamilyWeight]

/-- The joint probability of a family set and one child choice uses the full, potentially correlated law. -/
theorem hierarchicalJointMeasure_family_child {N L : ℕ}
    (ν : Measure (HierarchicalJointSample N L)) [IsFiniteMeasure ν]
    (F : ExactSourceSupport N L) (i : Fin N) (k : Fin 2) :
    ν.real {s | s.1 = F ∧ s.2 i = k} =
      ∑ choice, if choice i = k then ν.real {(F, choice)} else 0 := by
  classical
  rw [hierarchicalJointMeasure_event, Fintype.sum_prod_type, Finset.sum_comm]
  simp [ite_and]

/-- Every probability law on family sets and child vectors is represented by normalized nonnegative singleton weights, with the same atomic-support pushforward. Thus the finite-weight model imposes no factorization restriction. -/
theorem hierarchicalJointMeasure_weights {N L : ℕ}
    (ν : Measure (HierarchicalJointSample N L)) [IsProbabilityMeasure ν] :
    (∑ s, ν.real {s} = 1) ∧
      Measure.map hierarchicalJointSupport ν =
        hierarchicalJointSupportLaw (fun s => ν.real {s}) := by
  constructor
  · simp
  · have hν : ν = ∑ s, ENNReal.ofReal (ν.real {s}) • Measure.dirac s := by
      calc
        _ = ∑ s, ν {s} • Measure.dirac s :=
          ((Measure.sum_fintype _).symm.trans (Measure.sum_smul_dirac ν)).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s _
          rw [ofReal_measureReal]
    conv_lhs => rw [hν]
    rw [Measure.map_finset_sum' (measurable_of_countable _).aemeasurable]
    simp only [Measure.map_smul, Measure.map_dirac, hierarchicalJointSupportLaw]

/-- On positive-mass family sets, the weight inequality is exactly the authored conditional child-probability lower bound. -/
theorem hierarchicalJointMeasure_child_balance_iff {N L : ℕ}
    (ν : Measure (HierarchicalJointSample N L)) [IsFiniteMeasure ν]
    (F : ExactSourceSupport N L) (i : Fin N) (k : Fin 2) (κ : ℝ)
    (hF : 0 < ν.real {s | s.1 = F}) :
    κ ≤ ν.real {s | s.1 = F ∧ s.2 i = k} / ν.real {s | s.1 = F} ↔
      κ * hierarchicalFamilyWeight (fun s => ν.real {s}) F ≤
        ∑ choice, if choice i = k then ν.real {(F, choice)} else 0 := by
  rw [le_div_iff₀ hF, hierarchicalJointMeasure_family, hierarchicalJointMeasure_family_child]

/-- Events determined only by the active family set have their marginal-law probabilities. -/
theorem hierarchicalJointMeasure_family_event {N L : ℕ}
    (ν : Measure (HierarchicalJointSample N L)) [IsFiniteMeasure ν]
    (E : ExactSourceSupport N L → Prop) [DecidablePred E] :
    ν.real {s | E s.1} =
      ∑ F, if E F then hierarchicalFamilyWeight (fun s => ν.real {s}) F else 0 := by
  rw [hierarchicalJointMeasure_event, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : E F <;> simp [hF, hierarchicalFamilyWeight]

theorem RegularHierarchicalPopulation.of_joint_probability_law
    {Ω : Type*} [MeasurableSpace Ω] {N L : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector (N * 3))
    (ν : Measure (HierarchicalJointSample N L)) [IsProbabilityMeasure ν]
    (ρ κ cLower cUpper : ℝ)
    (hz : Measurable z)
    (hsep : ∀ i j : Fin N, i ≠ j → 0 < ν.real {s | i ∈ s.1.1} →
      ρ ≤ ν.real {s | i ∈ s.1.1 ∧ j ∉ s.1.1} / ν.real {s | i ∈ s.1.1})
    (hbalance : ∀ (F : ExactSourceSupport N L) (i : Fin N), i ∈ F.1 →
      ∀ k : Fin 2, 0 < ν.real {s | s.1 = F} →
        κ ≤ ν.real {s | s.1 = F ∧ s.2 i = k} / ν.real {s | s.1 = F})
    (hsupport : Measure.map (fun x => nonzeroSupport (z x)) μ =
      Measure.map hierarchicalJointSupport ν)
    (hdensity : ∀ S : ExactSourceSupport (N * 3) (2 * L),
      μ (sourceSupportEvent z S.1) ≠ 0 →
      ∃ h : EuclideanRepresentation (2 * L) → ℝ≥0∞, Measurable h ∧
        Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) =
          (uniformCubeCoefficientLaw (2 * L)).withDensity h ∧
        (∀ᵐ a ∂uniformCubeCoefficientLaw (2 * L),
          ENNReal.ofReal cLower ≤ h a ∧ h a ≤ ENNReal.ofReal cUpper)) :
    RegularHierarchicalPopulation μ z (fun s => ν.real {s}) ρ κ cLower cUpper := by
  classical
  refine ⟨hz, fun _ => measureReal_nonneg, (hierarchicalJointMeasure_weights ν).1,
    ?_, ?_, hsupport.trans (hierarchicalJointMeasure_weights ν).2, hdensity⟩
  · intro i j hij
    have h : ρ * ν.real {s | i ∈ s.1.1} ≤ ν.real {s | i ∈ s.1.1 ∧ j ∉ s.1.1} := by
      by_cases hi : 0 < ν.real {s | i ∈ s.1.1}
      · exact (le_div_iff₀ hi).mp (hsep i j hij hi)
      · have hzero : ν.real {s | i ∈ s.1.1} = 0 :=
          le_antisymm (le_of_not_gt hi) measureReal_nonneg
        rw [hzero, mul_zero]
        exact measureReal_nonneg
    rw [hierarchicalJointMeasure_family_event ν (fun F => i ∈ F.1),
      hierarchicalJointMeasure_family_event ν (fun F => i ∈ F.1 ∧ j ∉ F.1)] at h
    simpa only [supportMarginalWeight, supportSeparationWeight, supportFamilyWeight,
      Finset.sum_filter] using h
  · intro F i hi k
    by_cases hF : 0 < ν.real {s | s.1 = F}
    · exact (hierarchicalJointMeasure_child_balance_iff ν F i k κ hF).mp
        (hbalance F i hi k hF)
    · have hzero : ν.real {s | s.1 = F} = 0 := le_antisymm (le_of_not_gt hF) measureReal_nonneg
      rw [← hierarchicalJointMeasure_family, hzero, mul_zero]
      apply Finset.sum_nonneg
      intro choice _
      split_ifs
      · exact measureReal_nonneg
      · exact le_rfl

end PKG26AtomicFeatures
