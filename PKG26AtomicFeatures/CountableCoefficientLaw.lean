import PKG26AtomicFeatures.UniformCubeCoefficients
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A countable population with full support on the open coefficient cube

A geometrically weighted dense sequence gives a probability law concentrated
on countably many strictly positive coefficient vectors. Every open-cube
point belongs to its topological support. This sampling primitive can be
lifted through a surjective source map by choosing only countably many input
representatives; it requires no measurable inverse of the source map.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set Topology
open scoped ENNReal

/-- Strictly positive coefficients strictly below one. -/
def coefficientOpenCube (K : ℕ) : Set (FeatureVector K) :=
  {w | ∀ j, w j ∈ Set.Ioo (0 : ℝ) 1}

theorem isOpen_coefficientOpenCube (K : ℕ) : IsOpen (coefficientOpenCube K) := by
  simpa [coefficientOpenCube, Set.setOf_forall] using
    isOpen_iInter_of_finite (fun j : Fin K =>
      isOpen_Ioo.preimage (continuous_apply j))

instance coefficientOpenCube_nonempty (K : ℕ) : Nonempty (coefficientOpenCube K) :=
  ⟨⟨fun _ => 1 / 2, by intro j; constructor <;> norm_num⟩⟩

/-- A sequence lying in, and dense in, the open coefficient cube. -/
noncomputable def denseCountableCubePoint (K : ℕ) (n : ℕ) : FeatureVector K :=
  (TopologicalSpace.denseSeq (coefficientOpenCube K) n).1

theorem denseCountableCubePoint_mem (K n : ℕ) :
    denseCountableCubePoint K n ∈ coefficientOpenCube K :=
  (TopologicalSpace.denseSeq (coefficientOpenCube K) n).2

/-- All atoms have positive geometric weights, whose sum is one. -/
noncomputable def denseCountableCubeCoordinateLaw (K : ℕ) : Measure (FeatureVector K) :=
  Measure.sum fun n : ℕ => ((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) •
    Measure.dirac (denseCountableCubePoint K n)

instance denseCountableCubeCoordinateLaw_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (denseCountableCubeCoordinateLaw K) := by
  constructor
  simp only [denseCountableCubeCoordinateLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.tsum_geometric_add_one]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

theorem denseCountableCubeCoordinateLaw_ae_mem_range (K : ℕ) :
    ∀ᵐ w ∂denseCountableCubeCoordinateLaw K, w ∈ Set.range (denseCountableCubePoint K) := by
  apply Measure.ae_sum_iff.mpr
  intro n
  apply Measure.ae_smul_measure
  simp only [ae_dirac_eq, Filter.eventually_pure]
  exact Set.mem_range_self n

theorem denseCountableCubeCoordinateLaw_countably_supported (K : ℕ) :
    ∃ S : Set (FeatureVector K), S.Countable ∧
      ∀ᵐ w ∂denseCountableCubeCoordinateLaw K, w ∈ S :=
  ⟨Set.range (denseCountableCubePoint K), Set.countable_range _,
    denseCountableCubeCoordinateLaw_ae_mem_range K⟩

theorem denseCountableCubeCoordinateLaw_ae_mem_openCube (K : ℕ) :
    ∀ᵐ w ∂denseCountableCubeCoordinateLaw K, w ∈ coefficientOpenCube K := by
  filter_upwards [denseCountableCubeCoordinateLaw_ae_mem_range K] with w hw
  obtain ⟨n, rfl⟩ := hw
  exact denseCountableCubePoint_mem K n

/-- Every open neighborhood of an open-cube point has positive mass. -/
theorem denseCountableCubeCoordinateLaw_pos_of_isOpen
    (K : ℕ) {U : Set (FeatureVector K)} (hU : IsOpen U)
    {w : FeatureVector K} (hw : w ∈ coefficientOpenCube K) (hwU : w ∈ U) :
    0 < denseCountableCubeCoordinateLaw K U := by
  have hopen : IsOpen (Subtype.val ⁻¹' U : Set (coefficientOpenCube K)) :=
    hU.preimage continuous_subtype_val
  obtain ⟨n, hv⟩ :=
    (TopologicalSpace.denseRange_denseSeq (coefficientOpenCube K)).exists_mem_open
      hopen ⟨⟨w, hw⟩, hwU⟩
  have hn : denseCountableCubePoint K n ∈ U := hv
  have hpos : 0 < (((2 : ℝ≥0∞)⁻¹ ^ (n + 1)) •
      Measure.dirac (denseCountableCubePoint K n)) U := by
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem hn, mul_one]
    exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by simp))
  exact hpos.trans_le (Measure.le_sum _ n U)

theorem coefficientOpenCube_subset_denseCountableCubeCoordinateLaw_support (K : ℕ) :
    coefficientOpenCube K ⊆ (denseCountableCubeCoordinateLaw K).support := by
  intro w hw
  rw [Measure.support_eq_forall_isOpen]
  exact fun U hwU hU => denseCountableCubeCoordinateLaw_pos_of_isOpen K hU hw hwU

theorem denseCountableCubeCoordinateLaw_ae_norm_sq_le (K : ℕ) :
    ∀ᵐ w ∂denseCountableCubeCoordinateLaw K,
      ‖representationToEuclidean K w‖ ^ 2 ≤ (K : ℝ) := by
  filter_upwards [denseCountableCubeCoordinateLaw_ae_mem_openCube K] with w hw
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ j : Fin K, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
      change (w j) ^ 2 ≤ 1
      have hj := hw j
      nlinarith [hj.1, hj.2]
    _ = K := by simp

theorem denseCountableCubeCoordinateLaw_secondMoment_le (K : ℕ) :
    (∫⁻ w, ENNReal.ofReal (‖representationToEuclidean K w‖ ^ 2)
      ∂denseCountableCubeCoordinateLaw K) ≤ ENNReal.ofReal (K : ℝ) := by
  calc
    _ ≤ ∫⁻ _, ENNReal.ofReal (K : ℝ) ∂denseCountableCubeCoordinateLaw K :=
      lintegral_mono_ae ((denseCountableCubeCoordinateLaw_ae_norm_sq_le K).mono
        fun _ h => ENNReal.ofReal_le_ofReal h)
    _ = _ := by simp

theorem denseCountableCubeCoordinateLaw_secondMoment_lt_top (K : ℕ) :
    (∫⁻ w, ENNReal.ofReal (‖representationToEuclidean K w‖ ^ 2)
      ∂denseCountableCubeCoordinateLaw K) < ∞ :=
  (denseCountableCubeCoordinateLaw_secondMoment_le K).trans_lt ENNReal.ofReal_lt_top

/-- The same countable law in the Euclidean coordinate convention used by
the population sampling modules. -/
noncomputable def denseCountableCubeCoefficientLaw (K : ℕ) :
    Measure (EuclideanRepresentation K) :=
  Measure.map (representationToEuclidean K) (denseCountableCubeCoordinateLaw K)

instance denseCountableCubeCoefficientLaw_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (denseCountableCubeCoefficientLaw K) :=
  Measure.isProbabilityMeasure_map
    (representationToEuclidean K).continuous.measurable.aemeasurable

theorem denseCountableCubeCoefficientLaw_ae_coordinates (K : ℕ) :
    ∀ᵐ w ∂denseCountableCubeCoefficientLaw K, ∀ j, w j ∈ Set.Ioo (0 : ℝ) 1 := by
  have hm : MeasurableSet {w : EuclideanRepresentation K |
      ∀ j, w j ∈ Set.Ioo (0 : ℝ) 1} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_Ioo.preimage (by fun_prop)
  apply (ae_map_iff (representationToEuclidean K).continuous.measurable.aemeasurable hm).mpr
  exact denseCountableCubeCoordinateLaw_ae_mem_openCube K

theorem denseCountableCubeCoefficientLaw_countably_supported (K : ℕ) :
    ∃ S : Set (EuclideanRepresentation K), S.Countable ∧
      ∀ᵐ w ∂denseCountableCubeCoefficientLaw K, w ∈ S := by
  let S := Set.range (fun n => representationToEuclidean K (denseCountableCubePoint K n))
  have hS : S.Countable := Set.countable_range _
  refine ⟨S, hS, ?_⟩
  apply (ae_map_iff (representationToEuclidean K).continuous.measurable.aemeasurable
    hS.measurableSet).mpr
  filter_upwards [denseCountableCubeCoordinateLaw_ae_mem_range K] with w hw
  obtain ⟨n, rfl⟩ := hw
  exact Set.mem_range_self n

theorem mem_denseCountableCubeCoefficientLaw_support (K : ℕ)
    (w : EuclideanRepresentation K) (hw : ∀ j, w j ∈ Set.Ioo (0 : ℝ) 1) :
    w ∈ (denseCountableCubeCoefficientLaw K).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro U hwU hU
  rw [denseCountableCubeCoefficientLaw,
    Measure.map_apply (representationToEuclidean K).continuous.measurable hU.measurableSet]
  apply denseCountableCubeCoordinateLaw_pos_of_isOpen K
    (hU.preimage (representationToEuclidean K).continuous)
    (w := (representationToEuclidean K).symm w)
  · exact hw
  · simpa only [Set.mem_preimage, LinearEquiv.apply_symm_apply] using hwU

theorem denseCountableCubeCoefficientLaw_ae_norm_sq_le (K : ℕ) :
    ∀ᵐ w ∂denseCountableCubeCoefficientLaw K, ‖w‖ ^ 2 ≤ (K : ℝ) := by
  apply (ae_map_iff (representationToEuclidean K).continuous.measurable.aemeasurable
    (measurableSet_le (measurable_norm.pow_const 2) measurable_const)).mpr
  exact denseCountableCubeCoordinateLaw_ae_norm_sq_le K

theorem denseCountableCubeCoefficientLaw_secondMoment_le (K : ℕ) :
    (∫⁻ w, ENNReal.ofReal (‖w‖ ^ 2) ∂denseCountableCubeCoefficientLaw K) ≤
      ENNReal.ofReal (K : ℝ) := by
  calc
    _ ≤ ∫⁻ _, ENNReal.ofReal (K : ℝ) ∂denseCountableCubeCoefficientLaw K :=
      lintegral_mono_ae ((denseCountableCubeCoefficientLaw_ae_norm_sq_le K).mono
        fun _ h => ENNReal.ofReal_le_ofReal h)
    _ = _ := by simp

theorem denseCountableCubeCoefficientLaw_secondMoment_lt_top (K : ℕ) :
    (∫⁻ w, ENNReal.ofReal (‖w‖ ^ 2) ∂denseCountableCubeCoefficientLaw K) < ∞ :=
  (denseCountableCubeCoefficientLaw_secondMoment_le K).trans_lt ENNReal.ofReal_lt_top

theorem denseCountableCubeCoefficientLaw_integrable_norm_sq (K : ℕ) :
    Integrable (fun w : EuclideanRepresentation K => ‖w‖ ^ 2)
      (denseCountableCubeCoefficientLaw K) := by
  apply (integrable_const (K : ℝ)).mono'
    (continuous_norm.pow 2).aestronglyMeasurable
  filter_upwards [denseCountableCubeCoefficientLaw_ae_norm_sq_le K] with w hw
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖w‖)] using hw

end PKG26AtomicFeatures
