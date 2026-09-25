import PKG26AtomicFeatures.MesoscalePopulationModel
import PKG26AtomicFeatures.ContinuousLeastSquaresRisk

/-!
# Integrating the explicit mesoscale mixture

The dominant, rare, and cube terms below are obtained by integrating the
actual coefficient law. Integrability follows from bounded coefficients,
including for the continuous cube component.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal

theorem integrable_mesoscalePairLaw {g : EuclideanRepresentation 2 → ℝ}
    (δ θ H η : ℝ) (hcube : Integrable g (uniformCubeCoefficientLaw 2)) :
    Integrable g (mesoscalePairLaw δ θ H η) := by
  unfold mesoscalePairLaw
  exact ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top) |>.add_measure
      (hcube.smul_measure ENNReal.ofReal_ne_top)

theorem integral_mesoscalePairLaw {g : EuclideanRepresentation 2 → ℝ}
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hcube : Integrable g (uniformCubeCoefficientLaw 2)) :
    (∫ q, g q ∂mesoscalePairLaw δ θ H η) =
      (1 - θ) * (1 - δ) * g mesoscaleDominantPair +
      (1 - θ) * δ * g (mesoscaleRarePair H η) + θ * ∫ q, g q ∂uniformCubeCoefficientLaw 2 := by
  have ha : Integrable g (ENNReal.ofReal ((1 - θ) * (1 - δ)) • Measure.dirac mesoscaleDominantPair) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have hb : Integrable g (ENNReal.ofReal ((1 - θ) * δ) • Measure.dirac (mesoscaleRarePair H η)) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [mesoscalePairLaw, integral_add_measure (ha.add_measure hb)
    (hcube.smul_measure ENNReal.ofReal_ne_top), integral_add_measure ha hb]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr hθone) (sub_nonneg.mpr hδone)),
    ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr hθone) hδ), ENNReal.toReal_ofReal hθ]

theorem integrable_mesoscalePopulationLaw {g : FeatureVector 3 → ℝ}
    (δ θ H η : ℝ) (hg : Measurable g)
    (hcube : ∀ k : Fin 2, Integrable (g ∘ mesoscalePlaneEmbedding k) (uniformCubeCoefficientLaw 2)) :
    Integrable g (mesoscalePopulationLaw δ θ H η) := by
  have hi (k : Fin 2) : Integrable g
      (Measure.map (mesoscalePlaneEmbedding k) (mesoscalePairLaw δ θ H η)) :=
    (integrable_map_measure hg.aestronglyMeasurable
      (measurable_mesoscalePlaneEmbedding k).aemeasurable).mpr
      (integrable_mesoscalePairLaw δ θ H η (hcube k))
  exact (hi 0 |>.smul_measure (by norm_num)).add_measure
    (hi 1 |>.smul_measure (by norm_num))

/-- Exact decomposition of the actual expectation into its six primitive
components. The two continuous terms retain their true cube law. -/
theorem integral_mesoscalePopulationLaw {g : FeatureVector 3 → ℝ}
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hg : Measurable g)
    (hcube : ∀ k : Fin 2, Integrable (g ∘ mesoscalePlaneEmbedding k) (uniformCubeCoefficientLaw 2)) :
    (∫ z, g z ∂mesoscalePopulationLaw δ θ H η) =
      (1 - θ) * (1 - δ) / 2 *
        (g (mesoscalePlaneEmbedding 0 mesoscaleDominantPair) +
          g (mesoscalePlaneEmbedding 1 mesoscaleDominantPair)) +
      (1 - θ) * δ / 2 *
        (g (mesoscalePlaneEmbedding 0 (mesoscaleRarePair H η)) +
          g (mesoscalePlaneEmbedding 1 (mesoscaleRarePair H η))) +
      θ / 2 * ((∫ q, g (mesoscalePlaneEmbedding 0 q) ∂uniformCubeCoefficientLaw 2) +
        ∫ q, g (mesoscalePlaneEmbedding 1 q) ∂uniformCubeCoefficientLaw 2) := by
  have hi (k : Fin 2) : Integrable g
      (Measure.map (mesoscalePlaneEmbedding k) (mesoscalePairLaw δ θ H η)) :=
    (integrable_map_measure hg.aestronglyMeasurable
      (measurable_mesoscalePlaneEmbedding k).aemeasurable).mpr
      (integrable_mesoscalePairLaw δ θ H η (hcube k))
  rw [mesoscalePopulationLaw, integral_add_measure
    (hi 0 |>.smul_measure (by norm_num)) (hi 1 |>.smul_measure (by norm_num))]
  simp only [integral_smul_measure, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, smul_eq_mul]
  rw [integral_map (measurable_mesoscalePlaneEmbedding 0).aemeasurable hg.aestronglyMeasurable,
    integral_map (measurable_mesoscalePlaneEmbedding 1).aemeasurable hg.aestronglyMeasurable]
  have hzero := integral_mesoscalePairLaw δ θ H η hδ hδone hθ hθone (hcube 0)
  have hone := integral_mesoscalePairLaw δ θ H η hδ hδone hθ hθone (hcube 1)
  dsimp only [Function.comp_def] at hzero hone
  rw [hzero, hone]
  ring

theorem norm_sq_mesoscalePlaneEmbedding (k : Fin 2) (q : EuclideanRepresentation 2) :
    ‖representationToEuclidean 3 (mesoscalePlaneEmbedding k q)‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  fin_cases k <;> norm_num [mesoscalePlaneEmbedding, Fin.sum_univ_succ,
    representationToEuclidean, Matrix.cons_val_two]

theorem integrable_mesoscalePlane_secondMoment (k : Fin 2) :
    Integrable (fun q => ‖representationToEuclidean 3 (mesoscalePlaneEmbedding k q)‖ ^ 2)
      (uniformCubeCoefficientLaw 2) := by
  have hm : Measurable (fun q => ‖representationToEuclidean 3 (mesoscalePlaneEmbedding k q)‖ ^ 2) :=
    (((representationToEuclidean 3).continuous.measurable.comp
      (measurable_mesoscalePlaneEmbedding k)).norm.pow_const 2)
  apply (integrable_const (2 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [uniformCubeCoefficientLaw_ae_coordinate_bounds 2] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_sq_mesoscalePlaneEmbedding]
  nlinarith [(hq 0).1, (hq 0).2, (hq 1).1, (hq 1).2]

/-- The explicit law has a finite second moment for every finite choice
of its real mixture parameters. -/
theorem integrable_mesoscalePopulation_secondMoment (δ θ H η : ℝ) :
    Integrable (fun z => ‖representationToEuclidean 3 z‖ ^ 2)
      (mesoscalePopulationLaw δ θ H η) := by
  apply integrable_mesoscalePopulationLaw δ θ H η
    ((representationToEuclidean 3).continuous.measurable.norm.pow_const 2)
  exact integrable_mesoscalePlane_secondMoment

end PKG26AtomicFeatures
