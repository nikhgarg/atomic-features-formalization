import PKG26AtomicFeatures.MesoscaleVariationPopulation
import PKG26AtomicFeatures.MesoscaleRiskPerturbation

/-!
# Uniform reference-risk approximation for arbitrary bounded variation

The same explicit rare and dominant components approximate the finite
reference objective for every probability variation law supported on
strictly positive coefficient pairs bounded by one. The estimate uses
actual integrated NNLS risk and is uniform in the variation law, learned
width, and dictionary. No density or topological-support premise is used.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped BigOperators

variable (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν]

/-- Bounded variation coefficients give a uniform integral bound for the
actual nonnegative least-squares value in either parent-child plane. -/
theorem nnls_mesoscaleVariation_integral_bounds
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) {m : ℕ}
    (B : Matrix (Fin 3) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖) (k : Fin 2) :
    0 ≤ (∫ q, nonnegativeLeastSquaresValue B γ hγ hlower
      (representationToEuclidean 3 (mesoscalePlaneEmbedding k q)) ∂ν) ∧
    (∫ q, nonnegativeLeastSquaresValue B γ hγ hlower
      (representationToEuclidean 3 (mesoscalePlaneEmbedding k q)) ∂ν) ≤ 2 := by
  have hf : Measurable (fun q => representationToEuclidean 3 (mesoscalePlaneEmbedding k q)) :=
    (representationToEuclidean 3).continuous.measurable.comp (measurable_mesoscalePlaneEmbedding k)
  have hi := integrable_nonnegativeLeastSquaresValue (ν) hf
    (integrable_mesoscalePlane_secondMoment_withVariation ν hν k) B γ hγ hlower
  constructor
  · exact integral_nonneg fun q => nonnegativeLeastSquaresValue_nonneg B γ hγ hlower _
  · have hbound : ∀ᵐ q ∂ν,
        nonnegativeLeastSquaresValue B γ hγ hlower
          (representationToEuclidean 3 (mesoscalePlaneEmbedding k q)) ≤ (2 : ℝ) := by
      filter_upwards [variationLaw_ae_bounds ν hν] with q hq
      apply (nonnegativeLeastSquaresValue_le_norm_sq B γ hγ hlower _).trans
      rw [norm_sq_mesoscalePlaneEmbedding]
      nlinarith [(hq 0).1, (hq 0).2, (hq 1).1, (hq 1).2]
    simpa using integral_mono_ae hi (integrable_const (2 : ℝ)) hbound

/-- The actual population risk is uniformly close to the finite reference
objective. The bound holds at every width and every positive global margin;
it does not assume a particular optimizer or its active coordinates. -/
theorem nnls_mesoscalePopulation_perturbation_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) {m : ℕ}
    (B : Matrix (Fin 3) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ)) :
    |nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw_withVariation ν δ θ H η)
        (representationToEuclidean 3) B γ hγ hlower -
      (1 - δ) * ∑ s, mesoscaleReferenceWeight s *
        nonnegativeLeastSquaresValue B γ hγ hlower (mesoscaleReferenceInput s)| ≤
      δ * η * (2 * H + η) + 2 * θ := by
  let V := nonnegativeLeastSquaresValue B γ hγ hlower
  let D := (V (mesoscaleReferenceInput 0) + V (mesoscaleReferenceInput 1)) / 2
  let P := V (mesoscaleReferenceInput 2)
  let R := (V (representationToEuclidean 3 (mesoscalePlaneEmbedding 0 (mesoscaleRarePair H η))) +
    V (representationToEuclidean 3 (mesoscalePlaneEmbedding 1 (mesoscaleRarePair H η)))) / 2
  let G := ((∫ q, V (representationToEuclidean 3 (mesoscalePlaneEmbedding 0 q)) ∂ν) +
    ∫ q, V (representationToEuclidean 3 (mesoscalePlaneEmbedding 1 q)) ∂ν) / 2
  have hvariation (k : Fin 2) : Integrable
      ((V ∘ representationToEuclidean 3) ∘ mesoscalePlaneEmbedding k) (ν) :=
    integrable_nonnegativeLeastSquaresValue (ν)
      ((representationToEuclidean 3).continuous.measurable.comp (measurable_mesoscalePlaneEmbedding k))
      (integrable_mesoscalePlane_secondMoment_withVariation ν hν k) B γ hγ hlower
  have hmix := integral_mesoscalePopulationLaw_withVariation ν δ θ H η hδ hδone hθ hθone
    ((continuous_nonnegativeLeastSquaresValue B γ hγ hlower).measurable.comp
      (representationToEuclidean 3).continuous.measurable) hvariation
  dsimp only [Function.comp_def] at hmix
  rw [mesoscaleDominantPoint_eq_reference 0, mesoscaleDominantPoint_eq_reference 1] at hmix
  have hF : (∑ s, mesoscaleReferenceWeight s * V (mesoscaleReferenceInput s)) = D + (3 / 5) * P := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, mesoscaleReferenceWeight,
      Matrix.cons_val_zero]
    dsimp [D, P]
    ring
  have hFbound := nnls_mesoscaleReference_bounds B γ hγ hlower
  change 0 ≤ (∑ s, mesoscaleReferenceWeight s * V (mesoscaleReferenceInput s)) ∧ _ at hFbound
  rw [hF] at hFbound
  have hGzero := nnls_mesoscaleVariation_integral_bounds ν hν B γ hγ hlower 0
  have hGone := nnls_mesoscaleVariation_integral_bounds ν hν B γ hγ hlower 1
  have hG : 0 ≤ G ∧ G ≤ 2 := by dsimp [G, V]; constructor <;> linarith
  have hRzero := abs_le.mp (nnls_mesoscaleRarePoint_perturbation B γ hγ hlower H η hH hη 0)
  have hRone := abs_le.mp (nnls_mesoscaleRarePoint_perturbation B γ hγ hlower H η hH hη 1)
  have hR : |R - H ^ 2 * P| ≤ η * (2 * H + η) := by
    apply abs_le.mpr
    dsimp [R, P, V]
    constructor <;> linarith
  have hrisk : nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (representationToEuclidean 3) B γ hγ hlower =
        (1 - θ) * (1 - δ) * D + (1 - θ) * δ * R + θ * G := by
    unfold nonnegativeLeastSquaresPopulationRisk
    rw [hmix]
    dsimp [D, R, G, V]
    ring
  rw [hrisk]
  change |(1 - θ) * (1 - δ) * D + (1 - θ) * δ * R + θ * G -
    (1 - δ) * (∑ s, mesoscaleReferenceWeight s * V (mesoscaleReferenceInput s))| ≤ _
  rw [hF]
  exact real_mixture_reference_bound δ θ H η D P R G hδ hδone hθ hθone hH hη
    hcal hFbound hG hR

end PKG26AtomicFeatures
