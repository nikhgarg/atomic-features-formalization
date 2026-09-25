import PKG26AtomicFeatures.MesoscaleRiskIntegration

/-!
# Mesoscale populations with arbitrary bounded variation laws

The dominant and rare components are fixed atoms. The remaining coefficient
law may be any probability measure with strictly positive coordinates bounded
by one. In particular it need not have a density. An independent fair choice
of child preserves the hierarchical support and swap symmetry. The explicit
mixture formulas, mass bounds, and finite moments retain the actual law.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal Matrix

variable (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν]

theorem variationLaw_ae_pos (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) :
    ∀ᵐ q ∂ν, ∀ j, 0 < q j := hν.mono fun _ h j => (h j).1

theorem variationLaw_ae_bounds (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) :
    ∀ᵐ q ∂ν, ∀ j, 0 ≤ q j ∧ q j ≤ 1 := hν.mono fun _ h j => ⟨(h j).1.le, (h j).2⟩

noncomputable def mesoscalePairLaw_withVariation (δ θ H η : ℝ) : Measure (EuclideanRepresentation 2) :=
  ENNReal.ofReal ((1 - θ) * (1 - δ)) • Measure.dirac mesoscaleDominantPair +
  ENNReal.ofReal ((1 - θ) * δ) • Measure.dirac (mesoscaleRarePair H η) +
  ENNReal.ofReal θ • ν


noncomputable def mesoscalePopulationLaw_withVariation (δ θ H η : ℝ) : Measure (FeatureVector 3) :=
  (1 / 2 : ℝ≥0∞) • Measure.map (mesoscalePlaneEmbedding 0) (mesoscalePairLaw_withVariation ν δ θ H η) +
  (1 / 2 : ℝ≥0∞) • Measure.map (mesoscalePlaneEmbedding 1) (mesoscalePairLaw_withVariation ν δ θ H η)



theorem mesoscalePairLaw_isProbabilityMeasure_withVariation (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (mesoscalePairLaw_withVariation ν δ θ H η) := by
  constructor
  have ha : 0 ≤ (1 - θ) * (1 - δ) := mul_nonneg (sub_nonneg.mpr hθone) (sub_nonneg.mpr hδone)
  have hb : 0 ≤ (1 - θ) * δ := mul_nonneg (sub_nonneg.mpr hθone) hδ
  simp only [mesoscalePairLaw_withVariation, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (add_nonneg ha hb) hθ]
  convert ENNReal.ofReal_one using 1 <;> congr 1 <;> ring


theorem mesoscalePopulationLaw_isProbabilityMeasure_withVariation (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (mesoscalePopulationLaw_withVariation ν δ θ H η) := by
  letI := mesoscalePairLaw_isProbabilityMeasure_withVariation ν δ θ H η hδ hδone hθ hθone
  constructor
  simp only [mesoscalePopulationLaw_withVariation, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_mesoscalePlaneEmbedding 0) MeasurableSet.univ,
    Measure.map_apply (measurable_mesoscalePlaneEmbedding 1) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, mul_one]
  exact ENNReal.add_halves 1


theorem mesoscalePairLaw_ae_pos_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ q ∂mesoscalePairLaw_withVariation ν δ θ H η, 0 < q 0 ∧ 0 < q 1 := by
  rw [mesoscalePairLaw_withVariation, ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩,
    Measure.ae_smul_measure ?_ _⟩
  · simp [mesoscaleDominantPair, representationToEuclidean]
  · simpa [mesoscaleRarePair, representationToEuclidean] using And.intro hH hη
  · filter_upwards [variationLaw_ae_pos ν hν] with q hq
    exact ⟨hq 0, hq 1⟩


theorem mesoscalePopulationLaw_ae_of_planes_withVariation (δ θ H η : ℝ)
    (p : FeatureVector 3 → Prop) (hp : MeasurableSet {z | p z})
    (hplane : ∀ k : Fin 2, ∀ᵐ q ∂mesoscalePairLaw_withVariation ν δ θ H η, p (mesoscalePlaneEmbedding k q)) :
    ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, p z := by
  rw [mesoscalePopulationLaw_withVariation, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure
      ((ae_map_iff (measurable_mesoscalePlaneEmbedding 0).aemeasurable hp).mpr (hplane 0)) _
  · exact Measure.ae_smul_measure
      ((ae_map_iff (measurable_mesoscalePlaneEmbedding 1).aemeasurable hp).mpr (hplane 1)) _



theorem mesoscalePopulationLaw_ae_hierarchicalPresence_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, MesoscaleHierarchicalPresence z := by
  apply mesoscalePopulationLaw_ae_of_planes_withVariation ν δ θ H η _ measurableSet_mesoscaleHierarchicalPresence
  intro k
  filter_upwards [mesoscalePairLaw_ae_pos_withVariation ν hν δ θ H η hH hη] with q hq
  fin_cases k <;> simpa [MesoscaleHierarchicalPresence, mesoscalePlaneEmbedding,
    Matrix.cons_val_two] using hq



theorem mesoscalePopulationLaw_ae_support_card_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, (nonzeroSupport z).card = 2 :=
  (mesoscalePopulationLaw_ae_hierarchicalPresence_withVariation ν hν δ θ H η hH hη).mono fun _ hz => hz.support_card

private theorem mesoscalePlaneLaw_present_probability_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η) (k : Fin 2) (j : Fin 3) :
    (Measure.map (mesoscalePlaneEmbedding k) (mesoscalePairLaw_withVariation ν δ θ H η)) {z | 0 < z j} =
      if j = 0 ∨ j = k.succ then 1 else 0 := by
  letI := mesoscalePairLaw_isProbabilityMeasure_withVariation ν δ θ H η hδ hδone hθ hθone
  rw [Measure.map_apply (measurable_mesoscalePlaneEmbedding k)
    (measurableSet_lt measurable_const (measurable_pi_apply j))]
  have hevent : (mesoscalePlaneEmbedding k ⁻¹' {z | 0 < z j}) =ᵐ[mesoscalePairLaw_withVariation ν δ θ H η]
      (if j = 0 ∨ j = k.succ then Set.univ else ∅ : Set (EuclideanRepresentation 2)) := by
    filter_upwards [mesoscalePairLaw_ae_pos_withVariation ν hν δ θ H η hH hη] with q hq
    apply propext
    change (0 < mesoscalePlaneEmbedding k q j) ↔
      q ∈ (if j = 0 ∨ j = k.succ then Set.univ else ∅ : Set (EuclideanRepresentation 2))
    fin_cases k <;> fin_cases j <;>
      norm_num [mesoscalePlaneEmbedding, Matrix.cons_val_two, Fin.succ, hq.1, hq.2]
  rw [measure_congr hevent]
  split_ifs <;> simp


theorem mesoscalePopulationLaw_prevalence_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η) (j : Fin 3) :
    (mesoscalePopulationLaw_withVariation ν δ θ H η).real {z | 0 < z j} = if j = 0 then 1 else 1 / 2 := by
  have heval : (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z j} =
      if j = 0 then 1 else 1 / 2 := by
    simp only [mesoscalePopulationLaw_withVariation, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      mesoscalePlaneLaw_present_probability_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη]
    have hhalf : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by simpa using ENNReal.add_halves 1
    fin_cases j <;> norm_num [Fin.succ, hhalf]
  change ((mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z j}).toReal = _
  rw [heval]
  split_ifs <;> norm_num



theorem mesoscalePopulationLaw_swap_children_withVariation (δ θ H η : ℝ) :
    Measure.map mesoscaleSwapChildren (mesoscalePopulationLaw_withVariation ν δ θ H η) =
      mesoscalePopulationLaw_withVariation ν δ θ H η := by
  rw [mesoscalePopulationLaw_withVariation, Measure.map_add _ _ measurable_mesoscaleSwapChildren,
    Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_mesoscaleSwapChildren (measurable_mesoscalePlaneEmbedding 0),
    Measure.map_map measurable_mesoscaleSwapChildren (measurable_mesoscalePlaneEmbedding 1),
    mesoscaleSwapChildren_plane_zero, mesoscaleSwapChildren_plane_one]
  exact add_comm _ _


theorem mesoscalePairLaw_dominant_le_withVariation (δ θ H η : ℝ) :
    ENNReal.ofReal ((1 - θ) * (1 - δ)) • Measure.dirac mesoscaleDominantPair ≤
      mesoscalePairLaw_withVariation ν δ θ H η := by
  unfold mesoscalePairLaw_withVariation
  exact Measure.le_add_right (Measure.le_add_right le_rfl)


theorem mesoscalePopulationLaw_dominant_mass_withVariation (δ θ H η : ℝ) (k : Fin 2) :
    ENNReal.ofReal ((1 - θ) * (1 - δ) / 2) ≤
      mesoscalePopulationLaw_withVariation ν δ θ H η {mesoscalePlaneEmbedding k mesoscaleDominantPair} := by
  have hmap := Measure.map_mono (mesoscalePairLaw_dominant_le_withVariation ν δ θ H η)
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
  rw [mesoscalePopulationLaw_withVariation, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul]
  fin_cases k
  · exact le_add_right le_rfl
  · exact le_add_left le_rfl


theorem mesoscalePairLaw_ae_bounds_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) (hηone : η ≤ 1) :
    ∀ᵐ q ∂mesoscalePairLaw_withVariation ν δ θ H η,
      0 ≤ q 0 ∧ q 0 ≤ H ∧ 0 ≤ q 1 ∧ q 1 ≤ 1 := by
  rw [mesoscalePairLaw_withVariation, ae_add_measure_iff, ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩,
    Measure.ae_smul_measure ?_ _⟩
  · simp only [ae_dirac_eq, Filter.eventually_pure]
    norm_num [mesoscaleDominantPair, representationToEuclidean]
    linarith
  · simp only [ae_dirac_eq, Filter.eventually_pure]
    norm_num [mesoscaleRarePair, representationToEuclidean]
    exact ⟨by linarith, hη.le, hηone⟩
  · filter_upwards [variationLaw_ae_bounds ν hν] with q hq
    exact ⟨(hq 0).1, (hq 0).2.trans hH, (hq 1).1, (hq 1).2⟩


theorem mesoscalePopulationLaw_ae_bounds_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) (hηone : η ≤ 1) :
    ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, ∀ j, 0 ≤ z j ∧ z j ≤ H + 1 := by
  have hm : MeasurableSet {z : FeatureVector 3 | ∀ j, 0 ≤ z j ∧ z j ≤ H + 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le measurable_const (measurable_pi_apply j)).inter
        (measurableSet_le (measurable_pi_apply j) measurable_const)
  apply mesoscalePopulationLaw_ae_of_planes_withVariation ν δ θ H η _ hm
  intro k
  filter_upwards [mesoscalePairLaw_ae_bounds_withVariation ν hν δ θ H η hH hη hηone] with q hq
  intro j
  fin_cases k <;> fin_cases j <;>
    norm_num [mesoscalePlaneEmbedding, Matrix.cons_val_two] <;> (try constructor) <;> linarith [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2]


theorem integrable_mesoscalePairLaw_withVariation {g : EuclideanRepresentation 2 → ℝ}
    (δ θ H η : ℝ) (hcube : Integrable g (ν)) :
    Integrable g (mesoscalePairLaw_withVariation ν δ θ H η) := by
  unfold mesoscalePairLaw_withVariation
  exact ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top) |>.add_measure
      (hcube.smul_measure ENNReal.ofReal_ne_top)

theorem integral_mesoscalePairLaw_withVariation {g : EuclideanRepresentation 2 → ℝ}
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hcube : Integrable g (ν)) :
    (∫ q, g q ∂mesoscalePairLaw_withVariation ν δ θ H η) =
      (1 - θ) * (1 - δ) * g mesoscaleDominantPair +
      (1 - θ) * δ * g (mesoscaleRarePair H η) + θ * ∫ q, g q ∂ν := by
  have ha : Integrable g (ENNReal.ofReal ((1 - θ) * (1 - δ)) • Measure.dirac mesoscaleDominantPair) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have hb : Integrable g (ENNReal.ofReal ((1 - θ) * δ) • Measure.dirac (mesoscaleRarePair H η)) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [mesoscalePairLaw_withVariation, integral_add_measure (ha.add_measure hb)
    (hcube.smul_measure ENNReal.ofReal_ne_top), integral_add_measure ha hb]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr hθone) (sub_nonneg.mpr hδone)),
    ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr hθone) hδ), ENNReal.toReal_ofReal hθ]

theorem integrable_mesoscalePopulationLaw_withVariation {g : FeatureVector 3 → ℝ}
    (δ θ H η : ℝ) (hg : Measurable g)
    (hcube : ∀ k : Fin 2, Integrable (g ∘ mesoscalePlaneEmbedding k) (ν)) :
    Integrable g (mesoscalePopulationLaw_withVariation ν δ θ H η) := by
  have hi (k : Fin 2) : Integrable g
      (Measure.map (mesoscalePlaneEmbedding k) (mesoscalePairLaw_withVariation ν δ θ H η)) :=
    (integrable_map_measure hg.aestronglyMeasurable
      (measurable_mesoscalePlaneEmbedding k).aemeasurable).mpr
      (integrable_mesoscalePairLaw_withVariation ν δ θ H η (hcube k))
  exact (hi 0 |>.smul_measure (by norm_num)).add_measure
    (hi 1 |>.smul_measure (by norm_num))


theorem integral_mesoscalePopulationLaw_withVariation {g : FeatureVector 3 → ℝ}
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hg : Measurable g)
    (hcube : ∀ k : Fin 2, Integrable (g ∘ mesoscalePlaneEmbedding k) (ν)) :
    (∫ z, g z ∂mesoscalePopulationLaw_withVariation ν δ θ H η) =
      (1 - θ) * (1 - δ) / 2 *
        (g (mesoscalePlaneEmbedding 0 mesoscaleDominantPair) +
          g (mesoscalePlaneEmbedding 1 mesoscaleDominantPair)) +
      (1 - θ) * δ / 2 *
        (g (mesoscalePlaneEmbedding 0 (mesoscaleRarePair H η)) +
          g (mesoscalePlaneEmbedding 1 (mesoscaleRarePair H η))) +
      θ / 2 * ((∫ q, g (mesoscalePlaneEmbedding 0 q) ∂ν) +
        ∫ q, g (mesoscalePlaneEmbedding 1 q) ∂ν) := by
  have hi (k : Fin 2) : Integrable g
      (Measure.map (mesoscalePlaneEmbedding k) (mesoscalePairLaw_withVariation ν δ θ H η)) :=
    (integrable_map_measure hg.aestronglyMeasurable
      (measurable_mesoscalePlaneEmbedding k).aemeasurable).mpr
      (integrable_mesoscalePairLaw_withVariation ν δ θ H η (hcube k))
  rw [mesoscalePopulationLaw_withVariation, integral_add_measure
    (hi 0 |>.smul_measure (by norm_num)) (hi 1 |>.smul_measure (by norm_num))]
  simp only [integral_smul_measure, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, smul_eq_mul]
  rw [integral_map (measurable_mesoscalePlaneEmbedding 0).aemeasurable hg.aestronglyMeasurable,
    integral_map (measurable_mesoscalePlaneEmbedding 1).aemeasurable hg.aestronglyMeasurable]
  have hzero := integral_mesoscalePairLaw_withVariation ν δ θ H η hδ hδone hθ hθone (hcube 0)
  have hone := integral_mesoscalePairLaw_withVariation ν δ θ H η hδ hδone hθ hθone (hcube 1)
  dsimp only [Function.comp_def] at hzero hone
  rw [hzero, hone]
  ring


theorem integrable_mesoscalePlane_secondMoment_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (k : Fin 2) :
    Integrable (fun q => ‖representationToEuclidean 3 (mesoscalePlaneEmbedding k q)‖ ^ 2)
      (ν) := by
  have hm : Measurable (fun q => ‖representationToEuclidean 3 (mesoscalePlaneEmbedding k q)‖ ^ 2) :=
    (((representationToEuclidean 3).continuous.measurable.comp
      (measurable_mesoscalePlaneEmbedding k)).norm.pow_const 2)
  apply (integrable_const (2 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [variationLaw_ae_bounds ν hν] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_sq_mesoscalePlaneEmbedding]
  nlinarith [(hq 0).1, (hq 0).2, (hq 1).1, (hq 1).2]


theorem integrable_mesoscalePopulation_secondMoment_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ) :
    Integrable (fun z => ‖representationToEuclidean 3 z‖ ^ 2)
      (mesoscalePopulationLaw_withVariation ν δ θ H η) := by
  apply integrable_mesoscalePopulationLaw_withVariation ν δ θ H η
    ((representationToEuclidean 3).continuous.measurable.norm.pow_const 2)
  exact integrable_mesoscalePlane_secondMoment_withVariation ν hν


end PKG26AtomicFeatures
