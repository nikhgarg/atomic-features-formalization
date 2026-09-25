import PKG26AtomicFeatures.UniformCubeCoefficients
import PKG26AtomicFeatures.SupportConditioning
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# The explicit symmetric mesoscale coefficient population

The two active coefficients first follow an explicit mixture of a dominant
atom, a rare perturbed atom, and the independent uniform square law. An
independent fair choice inserts them in either parent-child plane. Thus the
resulting law has precisely the atom and cube masses in Section 2 of the
written construction. It has atoms and is not asserted to have a density.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal Matrix

/-- The dominant coefficient pair from the reference objective. -/
noncomputable def mesoscaleDominantPair : EuclideanRepresentation 2 :=
  representationToEuclidean 2 ![1 / 20, 1]

/-- The rare parent point perturbed into a genuine parent-child input. -/
noncomputable def mesoscaleRarePair (H η : ℝ) : EuclideanRepresentation 2 :=
  representationToEuclidean 2 ![H, η]

/-- Insert a coefficient pair in the first or second parent-child plane. -/
noncomputable def mesoscalePlaneEmbedding (k : Fin 2)
    (q : EuclideanRepresentation 2) : FeatureVector 3 :=
  ![q 0, if k = 0 then q 1 else 0, if k = 1 then q 1 else 0]

theorem measurable_mesoscalePlaneEmbedding (k : Fin 2) :
    Measurable (mesoscalePlaneEmbedding k) := by
  apply measurable_pi_lambda
  intro j
  fin_cases k <;> fin_cases j <;>
    norm_num [mesoscalePlaneEmbedding, Matrix.cons_val_two] <;> fun_prop

/-- The actual two-coefficient mixture before choosing the child plane. -/
noncomputable def mesoscalePairLaw (δ θ H η : ℝ) : Measure (EuclideanRepresentation 2) :=
  ENNReal.ofReal ((1 - θ) * (1 - δ)) • Measure.dirac mesoscaleDominantPair +
  ENNReal.ofReal ((1 - θ) * δ) • Measure.dirac (mesoscaleRarePair H η) +
  ENNReal.ofReal θ • uniformCubeCoefficientLaw 2

/-- The actual symmetric three-coordinate population. Each plane gets
half the pair law, including its dominant, rare, and uniform components. -/
noncomputable def mesoscalePopulationLaw (δ θ H η : ℝ) : Measure (FeatureVector 3) :=
  (1 / 2 : ℝ≥0∞) • Measure.map (mesoscalePlaneEmbedding 0) (mesoscalePairLaw δ θ H η) +
  (1 / 2 : ℝ≥0∞) • Measure.map (mesoscalePlaneEmbedding 1) (mesoscalePairLaw δ θ H η)

/-- Uniform cube coefficients lie between zero and one almost surely. -/
theorem uniformCubeCoefficientLaw_ae_coordinate_bounds (K : ℕ) :
    ∀ᵐ q ∂uniformCubeCoefficientLaw K, ∀ j, 0 ≤ q j ∧ q j ≤ 1 := by
  have hm : MeasurableSet {q : EuclideanRepresentation K | ∀ j, 0 ≤ q j ∧ q j ≤ 1} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_le measurable_const (PiLp.continuous_apply 2 _ j).measurable).inter
      (measurableSet_le (PiLp.continuous_apply 2 _ j).measurable measurable_const)
  apply (ae_map_iff (representationToEuclidean K).continuous.measurable.aemeasurable hm).mpr
  filter_upwards [ae_restrict_mem (measurableSet_coefficientUnitCube K)] with q hq
  simpa only [coefficientUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Set.mem_Icc] using hq

/-- Coordinate hyperplanes have zero mass under the actual cube law. -/
theorem uniformCubeCoefficientLaw_coordinate_zero (K : ℕ) (j : Fin K) :
    uniformCubeCoefficientLaw K {q | q j = 0} = 0 := by
  have h := uniformCubeCoefficientLaw_hyperplane_null K (EuclideanSpace.single j 1) (by simp)
  have heq (q : EuclideanRepresentation K) : inner ℝ (EuclideanSpace.single j 1) q = q j := by
    simpa using EuclideanSpace.inner_single_left j (1 : ℝ) q
  simpa only [heq] using h

/-- The boundary at zero has no mass, so all active uniform coefficients
are strictly positive almost surely. -/
theorem uniformCubeCoefficientLaw_ae_coordinate_pos (K : ℕ) :
    ∀ᵐ q ∂uniformCubeCoefficientLaw K, ∀ j, 0 < q j := by
  have hne : ∀ᵐ q ∂uniformCubeCoefficientLaw K, ∀ j, q j ≠ 0 := by
    rw [ae_all_iff]
    intro j
    rw [ae_iff]
    simpa only [not_not] using uniformCubeCoefficientLaw_coordinate_zero K j
  filter_upwards [hne, uniformCubeCoefficientLaw_ae_coordinate_bounds K] with q hne hbound
  intro j
  exact lt_of_le_of_ne (hbound j).1 (Ne.symm (hne j))

/-- The three primitive mixture masses sum to one. -/
theorem mesoscalePairLaw_isProbabilityMeasure (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (mesoscalePairLaw δ θ H η) := by
  constructor
  have ha : 0 ≤ (1 - θ) * (1 - δ) := mul_nonneg (sub_nonneg.mpr hθone) (sub_nonneg.mpr hδone)
  have hb : 0 ≤ (1 - θ) * δ := mul_nonneg (sub_nonneg.mpr hθone) hδ
  simp only [mesoscalePairLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (add_nonneg ha hb) hθ]
  convert ENNReal.ofReal_one using 1 <;> congr 1 <;> ring

/-- Fairly choosing either plane preserves total probability. -/
theorem mesoscalePopulationLaw_isProbabilityMeasure (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (mesoscalePopulationLaw δ θ H η) := by
  letI := mesoscalePairLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  constructor
  simp only [mesoscalePopulationLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_mesoscalePlaneEmbedding 0) MeasurableSet.univ,
    Measure.map_apply (measurable_mesoscalePlaneEmbedding 1) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, mul_one]
  exact ENNReal.add_halves 1

/-- Positivity of the perturbed rare point makes both plane coefficients
strictly positive under the entire pair law. -/
theorem mesoscalePairLaw_ae_pos (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ q ∂mesoscalePairLaw δ θ H η, 0 < q 0 ∧ 0 < q 1 := by
  rw [mesoscalePairLaw, ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩,
    Measure.ae_smul_measure ?_ _⟩
  · simp [mesoscaleDominantPair, representationToEuclidean]
  · simpa [mesoscaleRarePair, representationToEuclidean] using And.intro hH hη
  · filter_upwards [uniformCubeCoefficientLaw_ae_coordinate_pos 2] with q hq
    exact ⟨hq 0, hq 1⟩

/-- Almost-sure statements proved on both actual plane pushforwards hold
on the full symmetric population. -/
theorem mesoscalePopulationLaw_ae_of_planes (δ θ H η : ℝ)
    (p : FeatureVector 3 → Prop) (hp : MeasurableSet {z | p z})
    (hplane : ∀ k : Fin 2, ∀ᵐ q ∂mesoscalePairLaw δ θ H η, p (mesoscalePlaneEmbedding k q)) :
    ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, p z := by
  rw [mesoscalePopulationLaw, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure
      ((ae_map_iff (measurable_mesoscalePlaneEmbedding 0).aemeasurable hp).mpr (hplane 0)) _
  · exact Measure.ae_smul_measure
      ((ae_map_iff (measurable_mesoscalePlaneEmbedding 1).aemeasurable hp).mpr (hplane 1)) _

/-- Presence labels in a single hierarchical family. -/
def MesoscaleHierarchicalPresence (z : FeatureVector 3) : Prop :=
  0 < z 0 ∧ ((0 < z 1 ∧ z 2 = 0) ∨ (z 1 = 0 ∧ 0 < z 2))

theorem measurableSet_mesoscaleHierarchicalPresence :
    MeasurableSet {z | MesoscaleHierarchicalPresence z} := by
  unfold MesoscaleHierarchicalPresence
  exact (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
    (((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
      (measurableSet_eq_fun (measurable_pi_apply 2) measurable_const)).union
      ((measurableSet_eq_fun (measurable_pi_apply 1) measurable_const).inter
        (measurableSet_lt measurable_const (measurable_pi_apply 2))))

/-- Every sample has a positive parent and exactly one positive child. -/
theorem mesoscalePopulationLaw_ae_hierarchicalPresence (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, MesoscaleHierarchicalPresence z := by
  apply mesoscalePopulationLaw_ae_of_planes δ θ H η _ measurableSet_mesoscaleHierarchicalPresence
  intro k
  filter_upwards [mesoscalePairLaw_ae_pos δ θ H η hH hη] with q hq
  fin_cases k <;> simpa [MesoscaleHierarchicalPresence, mesoscalePlaneEmbedding,
    Matrix.cons_val_two] using hq

/-- Hierarchical presence gives an exact two-atom support. -/
theorem MesoscaleHierarchicalPresence.support_card {z : FeatureVector 3}
    (hz : MesoscaleHierarchicalPresence z) : (nonzeroSupport z).card = 2 := by
  rcases hz with ⟨hp, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
  · have hs : nonzeroSupport z = {0, 1} := by
      ext j
      fin_cases j <;> simp [mem_nonzeroSupport_iff, hp.ne', h1.ne', h2]
    rw [hs]
    decide
  · have hs : nonzeroSupport z = {0, 2} := by
      ext j
      fin_cases j <;> simp [mem_nonzeroSupport_iff, hp.ne', h1, h2.ne']
    rw [hs]
    decide

/-- The explicit population has exactly two active source coordinates. -/
theorem mesoscalePopulationLaw_ae_support_card (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, (nonzeroSupport z).card = 2 :=
  (mesoscalePopulationLaw_ae_hierarchicalPresence δ θ H η hH hη).mono fun _ hz => hz.support_card

private theorem mesoscalePlaneLaw_present_probability (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η) (k : Fin 2) (j : Fin 3) :
    (Measure.map (mesoscalePlaneEmbedding k) (mesoscalePairLaw δ θ H η)) {z | 0 < z j} =
      if j = 0 ∨ j = k.succ then 1 else 0 := by
  letI := mesoscalePairLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  rw [Measure.map_apply (measurable_mesoscalePlaneEmbedding k)
    (measurableSet_lt measurable_const (measurable_pi_apply j))]
  have hevent : (mesoscalePlaneEmbedding k ⁻¹' {z | 0 < z j}) =ᵐ[mesoscalePairLaw δ θ H η]
      (if j = 0 ∨ j = k.succ then Set.univ else ∅ : Set (EuclideanRepresentation 2)) := by
    filter_upwards [mesoscalePairLaw_ae_pos δ θ H η hH hη] with q hq
    apply propext
    change (0 < mesoscalePlaneEmbedding k q j) ↔
      q ∈ (if j = 0 ∨ j = k.succ then Set.univ else ∅ : Set (EuclideanRepresentation 2))
    fin_cases k <;> fin_cases j <;>
      norm_num [mesoscalePlaneEmbedding, Matrix.cons_val_two, Fin.succ, hq.1, hq.2]
  rw [measure_congr hevent]
  split_ifs <;> simp

/-- The actual parent prevalence is one and both actual child prevalences
are exactly one half, derived from the fair choice of planes. -/
theorem mesoscalePopulationLaw_prevalence (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η) (j : Fin 3) :
    (mesoscalePopulationLaw δ θ H η).real {z | 0 < z j} = if j = 0 then 1 else 1 / 2 := by
  have heval : (mesoscalePopulationLaw δ θ H η) {z | 0 < z j} =
      if j = 0 then 1 else 1 / 2 := by
    simp only [mesoscalePopulationLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      mesoscalePlaneLaw_present_probability δ θ H η hδ hδone hθ hθone hH hη]
    have hhalf : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by simpa using ENNReal.add_halves 1
    fin_cases j <;> norm_num [Fin.succ, hhalf]
  change ((mesoscalePopulationLaw δ θ H η) {z | 0 < z j}).toReal = _
  rw [heval]
  split_ifs <;> norm_num

/-- Swap the child coordinates while fixing the parent. -/
def mesoscaleSwapChildren (z : FeatureVector 3) : FeatureVector 3 := ![z 0, z 2, z 1]

theorem measurable_mesoscaleSwapChildren : Measurable mesoscaleSwapChildren := by
  apply measurable_pi_lambda
  intro j
  fin_cases j <;> norm_num [mesoscaleSwapChildren, Matrix.cons_val_two] <;> fun_prop

@[simp] theorem mesoscaleSwapChildren_plane_zero :
    mesoscaleSwapChildren ∘ mesoscalePlaneEmbedding 0 = mesoscalePlaneEmbedding 1 := by
  funext q j
  fin_cases j <;> norm_num [mesoscaleSwapChildren, mesoscalePlaneEmbedding,
    Function.comp_def, Matrix.cons_val_two]

@[simp] theorem mesoscaleSwapChildren_plane_one :
    mesoscaleSwapChildren ∘ mesoscalePlaneEmbedding 1 = mesoscalePlaneEmbedding 0 := by
  funext q j
  fin_cases j <;> norm_num [mesoscaleSwapChildren, mesoscalePlaneEmbedding,
    Function.comp_def, Matrix.cons_val_two]

/-- The actual measure is invariant under swapping its two children. -/
theorem mesoscalePopulationLaw_swap_children (δ θ H η : ℝ) :
    Measure.map mesoscaleSwapChildren (mesoscalePopulationLaw δ θ H η) =
      mesoscalePopulationLaw δ θ H η := by
  rw [mesoscalePopulationLaw, Measure.map_add _ _ measurable_mesoscaleSwapChildren,
    Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_mesoscaleSwapChildren (measurable_mesoscalePlaneEmbedding 0),
    Measure.map_map measurable_mesoscaleSwapChildren (measurable_mesoscalePlaneEmbedding 1),
    mesoscaleSwapChildren_plane_zero, mesoscaleSwapChildren_plane_one]
  exact add_comm _ _

/-- The dominant Dirac component is a genuine submeasure of the pair law. -/
theorem mesoscalePairLaw_dominant_le (δ θ H η : ℝ) :
    ENNReal.ofReal ((1 - θ) * (1 - δ)) • Measure.dirac mesoscaleDominantPair ≤
      mesoscalePairLaw δ θ H η := by
  unfold mesoscalePairLaw
  exact Measure.le_add_right (Measure.le_add_right le_rfl)

/-- Each dominant atom retains at least its explicitly assigned mass;
possible collisions with other components can only increase that mass. -/
theorem mesoscalePopulationLaw_dominant_mass (δ θ H η : ℝ) (k : Fin 2) :
    ENNReal.ofReal ((1 - θ) * (1 - δ) / 2) ≤
      mesoscalePopulationLaw δ θ H η {mesoscalePlaneEmbedding k mesoscaleDominantPair} := by
  have hmap := Measure.map_mono (mesoscalePairLaw_dominant_le δ θ H η)
    (measurable_mesoscalePlaneEmbedding k)
  rw [Measure.map_smul, Measure.map_dirac' (measurable_mesoscalePlaneEmbedding k)] at hmap
  have hpoint := hmap {mesoscalePlaneEmbedding k mesoscaleDominantPair}
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_singleton _),
    mul_one] at hpoint
  have hhalf := mul_le_mul_left' hpoint (1 / 2 : ℝ≥0∞)
  have hmass : ENNReal.ofReal ((1 - θ) * (1 - δ) / 2) =
      (1 / 2 : ℝ≥0∞) * ENNReal.ofReal ((1 - θ) * (1 - δ)) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num [div_eq_mul_inv, mul_comm]
  rw [hmass]
  apply hhalf.trans
  rw [mesoscalePopulationLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul]
  fin_cases k
  · exact le_add_right le_rfl
  · exact le_add_left le_rfl

/-- The two-dimensional pair coefficients satisfy the bounds used by the
final common scaling, including the continuous cube component. -/
theorem mesoscalePairLaw_ae_bounds (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) (hηone : η ≤ 1) :
    ∀ᵐ q ∂mesoscalePairLaw δ θ H η,
      0 ≤ q 0 ∧ q 0 ≤ H ∧ 0 ≤ q 1 ∧ q 1 ≤ 1 := by
  rw [mesoscalePairLaw, ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩,
    Measure.ae_smul_measure ?_ _⟩
  · simp only [ae_dirac_eq, Filter.eventually_pure]
    norm_num [mesoscaleDominantPair, representationToEuclidean]
    linarith
  · simp only [ae_dirac_eq, Filter.eventually_pure]
    norm_num [mesoscaleRarePair, representationToEuclidean]
    exact ⟨by linarith, hη.le, hηone⟩
  · filter_upwards [uniformCubeCoefficientLaw_ae_coordinate_bounds 2] with q hq
    exact ⟨(hq 0).1, (hq 0).2.trans hH, (hq 1).1, (hq 1).2⟩

/-- All unscaled coefficients are nonnegative and bounded by H+1. -/
theorem mesoscalePopulationLaw_ae_bounds (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) (hηone : η ≤ 1) :
    ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, ∀ j, 0 ≤ z j ∧ z j ≤ H + 1 := by
  have hm : MeasurableSet {z : FeatureVector 3 | ∀ j, 0 ≤ z j ∧ z j ≤ H + 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le measurable_const (measurable_pi_apply j)).inter
        (measurableSet_le (measurable_pi_apply j) measurable_const)
  apply mesoscalePopulationLaw_ae_of_planes δ θ H η _ hm
  intro k
  filter_upwards [mesoscalePairLaw_ae_bounds δ θ H η hH hη hηone] with q hq
  intro j
  fin_cases k <;> fin_cases j <;>
    norm_num [mesoscalePlaneEmbedding, Matrix.cons_val_two] <;> (try constructor) <;> linarith [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2]

/-- The actual common coefficient scaling used to fit the source cube. -/
noncomputable def mesoscaleCoefficientScaling (H : ℝ) (z : FeatureVector 3) : FeatureVector 3 :=
  (1 / (H + 1)) • z

theorem measurable_mesoscaleCoefficientScaling (H : ℝ) :
    Measurable (mesoscaleCoefficientScaling H) := by
  unfold mesoscaleCoefficientScaling
  fun_prop

/-- The scaled population is an explicit pushforward of the constructed
coefficient law, preserving its actual atom and continuous components. -/
noncomputable def mesoscaleScaledPopulationLaw (δ θ H η : ℝ) : Measure (FeatureVector 3) :=
  Measure.map (mesoscaleCoefficientScaling H) (mesoscalePopulationLaw δ θ H η)

/-- With the written construction's parameter bounds, the actual scaled
source coefficients belong to the unit cube almost surely. -/
theorem mesoscaleScaledPopulationLaw_ae_unitCube (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) (hηone : η ≤ 1) :
    ∀ᵐ z ∂mesoscaleScaledPopulationLaw δ θ H η, ∀ j, 0 ≤ z j ∧ z j ≤ 1 := by
  have hm : MeasurableSet {z : FeatureVector 3 | ∀ j, 0 ≤ z j ∧ z j ≤ 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le measurable_const (measurable_pi_apply j)).inter
        (measurableSet_le (measurable_pi_apply j) measurable_const)
  apply (ae_map_iff (measurable_mesoscaleCoefficientScaling H).aemeasurable hm).mpr
  filter_upwards [mesoscalePopulationLaw_ae_bounds δ θ H η hH hη hηone] with z hz
  intro j
  have hHpos : 0 < H + 1 := by linarith
  change 0 ≤ (1 / (H + 1)) * z j ∧ (1 / (H + 1)) * z j ≤ 1
  constructor
  · exact mul_nonneg (by positivity) (hz j).1
  · rw [one_div, ← div_eq_inv_mul]
    exact (div_le_one hHpos).mpr (hz j).2

/-- Scaling preserves the total probability of the constructed law. -/
theorem mesoscaleScaledPopulationLaw_isProbabilityMeasure (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (mesoscaleScaledPopulationLaw δ θ H η) := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  exact Measure.isProbabilityMeasure_map (measurable_mesoscaleCoefficientScaling H).aemeasurable

/-- Positive common scaling leaves all presence events, and hence their
actual marginal probabilities, unchanged. -/
theorem mesoscaleScaledPopulationLaw_prevalence (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 1 ≤ H) (hη : 0 < η) (j : Fin 3) :
    (mesoscaleScaledPopulationLaw δ θ H η).real {z | 0 < z j} =
      if j = 0 then 1 else 1 / 2 := by
  have hscale : 0 < (1 / (H + 1) : ℝ) := by positivity
  have hevent : mesoscaleCoefficientScaling H ⁻¹' {z : FeatureVector 3 | 0 < z j} =
      {z : FeatureVector 3 | 0 < z j} := by
    ext z
    exact mul_pos_iff_of_pos_left hscale
  change ((Measure.map (mesoscaleCoefficientScaling H) (mesoscalePopulationLaw δ θ H η))
    {z | 0 < z j}).toReal = _
  rw [Measure.map_apply (measurable_mesoscaleCoefficientScaling H)
    (measurableSet_lt measurable_const (measurable_pi_apply j)), hevent]
  exact mesoscalePopulationLaw_prevalence δ θ H η hδ hδone hθ hθone (by linarith) hη j

/-- Real-valued form of the dominant-atom mass bound used by F1 estimates. -/
theorem mesoscalePopulationLaw_dominant_mass_real (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (k : Fin 2) :
    (1 - θ) * (1 - δ) / 2 ≤
      (mesoscalePopulationLaw δ θ H η).real {mesoscalePlaneEmbedding k mesoscaleDominantPair} := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  have hnonneg : 0 ≤ (1 - θ) * (1 - δ) / 2 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hθone) (sub_nonneg.mpr hδone)) (by norm_num)
  have h := ENNReal.toReal_mono (measure_ne_top (mesoscalePopulationLaw δ θ H η) _)
    (mesoscalePopulationLaw_dominant_mass δ θ H η k)
  simpa only [ENNReal.toReal_ofReal hnonneg] using h

/-- Positive common scaling preserves the complete hierarchical support
pattern, not merely the individual marginal probabilities. -/
theorem mesoscaleScaledPopulationLaw_ae_hierarchicalPresence (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscaleScaledPopulationLaw δ θ H η, MesoscaleHierarchicalPresence z := by
  have hscale : 0 < (1 / (H + 1) : ℝ) := by positivity
  apply (ae_map_iff (measurable_mesoscaleCoefficientScaling H).aemeasurable
    measurableSet_mesoscaleHierarchicalPresence).mpr
  filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence δ θ H η (by linarith) hη] with z hz
  rcases hz with ⟨hp, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
  · exact ⟨mul_pos hscale hp, Or.inl ⟨mul_pos hscale h1, by
      change (1 / (H + 1)) * z 2 = 0
      rw [h2, mul_zero]⟩⟩
  · exact ⟨mul_pos hscale hp, Or.inr ⟨by
      change (1 / (H + 1)) * z 1 = 0
      rw [h1, mul_zero], mul_pos hscale h2⟩⟩

/-- The actual scaled law still has exactly two active coordinates. -/
theorem mesoscaleScaledPopulationLaw_ae_support_card (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscaleScaledPopulationLaw δ θ H η, (nonzeroSupport z).card = 2 :=
  (mesoscaleScaledPopulationLaw_ae_hierarchicalPresence δ θ H η hH hη).mono
    fun _ hz => hz.support_card

end PKG26AtomicFeatures
