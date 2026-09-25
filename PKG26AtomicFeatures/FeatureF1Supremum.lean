import PKG26AtomicFeatures.FeatureF1
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Best single-coordinate feature F1

The mesoscale table takes a supremum over learned coordinates and strictly
positive thresholds. Exact presence equivalence gives supremum one even
when no positive threshold attains it. The threshold limit is proved for
the actual population measure.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set Filter
open scoped Topology

theorem populationF1_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (truth prediction : Set Ω) : 0 ≤ populationF1 μ truth prediction := by
  exact div_nonneg (mul_nonneg (by norm_num) measureReal_nonneg)
    (add_nonneg measureReal_nonneg measureReal_nonneg)

theorem populationF1_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (truth prediction : Set Ω) :
    populationF1 μ truth prediction ≤ 1 := by
  have htruth : μ.real (truth ∩ prediction) ≤ μ.real truth := measureReal_mono inter_subset_left
  have hprediction : μ.real (truth ∩ prediction) ≤ μ.real prediction :=
    measureReal_mono inter_subset_right
  by_cases hdenom : μ.real truth + μ.real prediction = 0
  · simp [populationF1, hdenom]
  · have hpos : 0 < μ.real truth + μ.real prediction :=
      lt_of_le_of_ne (add_nonneg measureReal_nonneg measureReal_nonneg) (Ne.symm hdenom)
    rw [populationF1, div_le_iff₀ hpos]
    linarith

/-- The paper's supremum over individual learned coordinates and positive
thresholds, using actual population F1 scores. -/
noncomputable def singleCoordinateF1Sup {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (truth : Set Ω) (code : Ω → Fin m → ℝ) : ℝ :=
  sSup {r | ∃ (j : Fin m) (t : ℝ), 0 < t ∧ r = populationF1 μ truth {x | t < code x j}}

theorem singleCoordinateF1_values_bddAbove {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (truth : Set Ω) (code : Ω → Fin m → ℝ) :
    BddAbove {r | ∃ (j : Fin m) (t : ℝ), 0 < t ∧ r = populationF1 μ truth {x | t < code x j}} := by
  refine ⟨1, ?_⟩
  rintro r ⟨j, t, ht, rfl⟩
  exact populationF1_le_one μ truth _

theorem populationF1_le_singleCoordinateF1Sup {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (truth : Set Ω) (code : Ω → Fin m → ℝ)
    (j : Fin m) (t : ℝ) (ht : 0 < t) :
    populationF1 μ truth {x | t < code x j} ≤ singleCoordinateF1Sup μ truth code := by
  exact le_csSup (singleCoordinateF1_values_bddAbove μ truth code) ⟨j, t, ht, rfl⟩

theorem singleCoordinateF1Sup_le {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (truth : Set Ω) (code : Ω → Fin m → ℝ)
    (j : Fin m) (r : ℝ)
    (hbound : ∀ (k : Fin m) (t : ℝ), 0 < t → populationF1 μ truth {x | t < code x k} ≤ r) :
    singleCoordinateF1Sup μ truth code ≤ r := by
  apply csSup_le
  · exact ⟨populationF1 μ truth {x | 1 < code x j}, j, 1, by norm_num, rfl⟩
  · rintro a ⟨k, t, ht, rfl⟩
    exact hbound k t ht

theorem singleCoordinateF1Sup_le_one {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (truth : Set Ω) (code : Ω → Fin m → ℝ)
    (j : Fin m) : singleCoordinateF1Sup μ truth code ≤ 1 :=
  singleCoordinateF1Sup_le μ truth code j 1 (fun _ _ _ => populationF1_le_one μ truth _)

/-- Thresholds decreasing to zero recover the full positive event in
actual probability. No lower bound away from zero is imposed on the code. -/
theorem tendsto_positive_threshold_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (v : Ω → ℝ) :
    Tendsto (fun n : ℕ => μ.real {x | 1 / ((n : ℝ) + 1) < v x}) atTop
      (𝓝 (μ.real {x | 0 < v x})) := by
  let P : ℕ → Set Ω := fun n => {x | 1 / ((n : ℝ) + 1) < v x}
  have hmono : Monotone P := by
    intro n k hnk x hx
    change 1 / ((k : ℝ) + 1) < v x
    change 1 / ((n : ℝ) + 1) < v x at hx
    exact lt_of_le_of_lt (one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (by exact_mod_cast Nat.add_le_add_right hnk 1)) hx
  have hunion : (⋃ n, P n) = {x | 0 < v x} := by
    ext x
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_trans (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hn
    · intro hx
      exact exists_nat_one_div_lt hx
  have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion] at h
  exact (ENNReal.continuousAt_toReal (measure_ne_top μ _)).tendsto.comp h

/-- F1 tends to one for detecting a code's own positive event as the
strictly positive threshold tends to zero. -/
theorem tendsto_populationF1_positive_thresholds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (v : Ω → ℝ)
    (hpositive : 0 < μ.real {x | 0 < v x}) :
    Tendsto (fun n : ℕ => populationF1 μ {x | 0 < v x}
      {x | 1 / ((n : ℝ) + 1) < v x}) atTop (𝓝 1) := by
  have hprob := tendsto_positive_threshold_probability μ v
  have hden : μ.real {x | 0 < v x} + μ.real {x | 0 < v x} ≠ 0 := by linarith
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hlimit := (htwo.mul hprob).div
    (tendsto_const_nhds.add hprob) hden
  have heq : 2 * μ.real {x | 0 < v x} /
      (μ.real {x | 0 < v x} + μ.real {x | 0 < v x}) = 1 := by
    apply (div_eq_one_iff_eq hden).mpr
    ring
  rw [heq] at hlimit
  convert hlimit using 1
  ext n
  rw [populationF1]
  have hsubset : {x | 1 / ((n : ℝ) + 1) < v x} ⊆ {x | 0 < v x} := by
    intro x hx
    exact lt_trans (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hx
  rw [inter_eq_right.mpr hsubset]
  rfl

theorem populationF1_congr_truth_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {truth truth' : Set Ω} (htruth : truth =ᵐ[μ] truth')
    (prediction : Set Ω) : populationF1 μ truth prediction = populationF1 μ truth' prediction := by
  have hinter : (truth ∩ prediction : Set Ω) =ᵐ[μ] (truth' ∩ prediction : Set Ω) := by
    filter_upwards [htruth] with x hx
    exact congrArg (fun p : Prop => p ∧ x ∈ prediction) hx
  rw [populationF1, populationF1, measureReal_congr htruth, measureReal_congr hinter]

theorem singleCoordinateF1Sup_congr_truth_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) {truth truth' : Set Ω} (htruth : truth =ᵐ[μ] truth')
    (code : Ω → Fin m → ℝ) :
    singleCoordinateF1Sup μ truth code = singleCoordinateF1Sup μ truth' code := by
  unfold singleCoordinateF1Sup
  simp_rw [populationF1_congr_truth_ae μ htruth]

/-- Exact presence of one coordinate implies best positive-threshold F1
one as a supremum; an attained maximizing threshold is not assumed. -/
theorem singleCoordinateF1Sup_eq_one_of_positive_event
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Fin m → ℝ) (j : Fin m)
    (hpositive : 0 < μ.real {x | 0 < code x j}) :
    singleCoordinateF1Sup μ {x | 0 < code x j} code = 1 := by
  apply le_antisymm (singleCoordinateF1Sup_le_one μ _ code j)
  apply le_of_tendsto (tendsto_populationF1_positive_thresholds μ (fun x => code x j) hpositive)
  apply Filter.Eventually.of_forall
  intro n
  exact populationF1_le_singleCoordinateF1Sup μ _ code j (1 / ((n : ℝ) + 1)) (by positivity)

/-- Almost-everywhere presence equivalence suffices for the population
supremum; null-set choices of the actual encoder are immaterial. -/
theorem singleCoordinateF1Sup_eq_one_of_presence_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (truth : Set Ω)
    (code : Ω → Fin m → ℝ) (j : Fin m)
    (heq : truth =ᵐ[μ] {x | 0 < code x j}) (hpositive : 0 < μ.real truth) :
    singleCoordinateF1Sup μ truth code = 1 := by
  rw [singleCoordinateF1Sup_congr_truth_ae μ heq]
  apply singleCoordinateF1Sup_eq_one_of_positive_event
  rwa [← measureReal_congr heq]

/-- A balanced binary label cannot exceed F1 two-thirds when each
prediction event treats the two labels symmetrically. -/
theorem populationF1_le_two_thirds_of_balanced_prediction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (truth prediction : Set Ω) (hpositive : 0 < μ.real truth)
    (hbalance : μ.real (truth ∩ prediction) = μ.real prediction / 2)
    (hmass : μ.real prediction ≤ 2 * μ.real truth) :
    populationF1 μ truth prediction ≤ 2 / 3 := by
  have hden : 0 < μ.real truth + μ.real prediction :=
    add_pos_of_pos_of_nonneg hpositive measureReal_nonneg
  rw [populationF1, hbalance, div_le_iff₀ hden]
  linarith

/-- For a single symmetric scalar code, the balanced child F1 supremum
is exactly two-thirds when decreasing thresholds recover all nonzero data. -/
theorem singleCoordinateF1Sup_eq_two_thirds_of_balanced_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (truth : Set Ω) (code : Ω → Fin 1 → ℝ) (hpositive : 0 < μ.real truth)
    (hparent : μ.real {x | 0 < code x 0} = 2 * μ.real truth)
    (hbalance : ∀ t : ℝ, 0 < t → μ.real (truth ∩ {x | t < code x 0}) =
      μ.real {x | t < code x 0} / 2) :
    singleCoordinateF1Sup μ truth code = 2 / 3 := by
  apply le_antisymm
  · apply singleCoordinateF1Sup_le μ truth code 0
    intro j t ht
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    apply populationF1_le_two_thirds_of_balanced_prediction μ truth _ hpositive (hbalance t ht)
    rw [← hparent]
    exact measureReal_mono (fun x hx => ht.trans hx)
  · have hprob := tendsto_positive_threshold_probability μ (fun x => code x 0)
    rw [hparent] at hprob
    have hden : μ.real truth + 2 * μ.real truth ≠ 0 := by linarith
    have hlimit := hprob.div (tendsto_const_nhds.add hprob) hden
    have heq : 2 * μ.real truth / (μ.real truth + 2 * μ.real truth) = 2 / 3 := by
      field_simp
      <;> ring
    rw [heq] at hlimit
    have hF1 : Tendsto (fun n : ℕ => populationF1 μ truth
        {x | 1 / ((n : ℝ) + 1) < code x 0}) atTop (𝓝 (2 / 3)) := by
      convert hlimit using 1
      ext n
      rw [populationF1, hbalance _ (by positivity)]
      change 2 * (μ.real {x | 1 / ((n : ℝ) + 1) < code x 0} / 2) / _ = _
      congr 1
      ring
    apply le_of_tendsto hF1
    apply Filter.Eventually.of_forall
    intro n
    exact populationF1_le_singleCoordinateF1Sup μ truth code 0
      (1 / ((n : ℝ) + 1)) (by positivity)

/-- If a parent is present throughout the nonzero population and a learned
coordinate predicts at most a fraction r, its F1 is at most 2r/(1+r). -/
theorem populationF1_parent_le_of_prediction_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (truth prediction : Set Ω) (htruth : μ.real truth = 1)
    (r : ℝ) (hr : 0 ≤ r) (hmass : μ.real prediction ≤ r) :
    populationF1 μ truth prediction ≤ 2 * r / (1 + r) := by
  have htp : μ.real (truth ∩ prediction) ≤ μ.real prediction :=
    measureReal_mono inter_subset_right
  have hden : 0 < 1 + μ.real prediction := by positivity
  have hrden : 0 < 1 + r := by linarith
  rw [populationF1, htruth, div_le_div_iff₀ hden hrden]
  nlinarith [mul_nonneg hr (sub_nonneg.mpr htp)]

end PKG26AtomicFeatures
