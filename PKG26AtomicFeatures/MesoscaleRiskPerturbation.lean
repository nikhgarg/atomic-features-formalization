import PKG26AtomicFeatures.MesoscaleRiskIntegration
import PKG26AtomicFeatures.NonnegativeLeastSquaresRiskPerturbation
import PKG26AtomicFeatures.NonnegativeLeastSquaresHomogeneity

/-!
# Uniform approximation of the reference objective by the actual population

The rare parent mass reproduces the reference parent weight after choosing
`δ H² = (3/5)(1-δ)`. Adding a small child coefficient and a small uniform
cube component changes the actual expected NNLS loss uniformly over all
feasible dictionaries. All integrals are over the explicit population law.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped BigOperators

theorem mesoscaleDominantPoint_eq_reference (k : Fin 2) :
    representationToEuclidean 3 (mesoscalePlaneEmbedding k mesoscaleDominantPair) =
      mesoscaleReferenceInput k.castSucc := by
  fin_cases k <;> rfl

theorem mesoscaleRarePoint_eq (k : Fin 2) (H η : ℝ) :
    representationToEuclidean 3 (mesoscalePlaneEmbedding k (mesoscaleRarePair H η)) =
      H • mesoscaleReferenceInput 2 + η • EuclideanSpace.single k.succ (1 : ℝ) := by
  ext i
  fin_cases k <;> fin_cases i <;>
    norm_num [mesoscalePlaneEmbedding, mesoscaleRarePair, mesoscaleReferenceInput,
      representationToEuclidean, PiLp.single_apply, Matrix.cons_val_two, Fin.ext_iff]

theorem mesoscaleReferenceInput_parent_norm : ‖mesoscaleReferenceInput 2‖ = 1 := by
  have heq : mesoscaleReferenceInput 2 = EuclideanSpace.single 0 (1 : ℝ) := by
    ext i
    fin_cases i <;> norm_num [mesoscaleReferenceInput, representationToEuclidean,
      PiLp.single_apply, Matrix.cons_val_two, Fin.ext_iff]
  rw [heq, PiLp.norm_single]
  norm_num

theorem nnls_mesoscaleRarePoint_perturbation {m : ℕ}
    (B : Matrix (Fin 3) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖)
    (H η : ℝ) (hH : 0 ≤ H) (hη : 0 ≤ η) (k : Fin 2) :
    |nonnegativeLeastSquaresValue B γ hγ hlower
        (representationToEuclidean 3 (mesoscalePlaneEmbedding k (mesoscaleRarePair H η))) -
      H ^ 2 * nonnegativeLeastSquaresValue B γ hγ hlower (mesoscaleReferenceInput 2)| ≤
        η * (2 * H + η) := by
  rw [mesoscaleRarePoint_eq, ← nonnegativeLeastSquaresValue_smul B γ hγ hlower _ H hH]
  apply nonnegativeLeastSquaresValue_perturbation_bound B γ hγ hlower
  · simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hH, mesoscaleReferenceInput_parent_norm]
  · simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]

theorem nnls_mesoscaleCube_integral_bounds {m : ℕ}
    (B : Matrix (Fin 3) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖) (k : Fin 2) :
    0 ≤ (∫ q, nonnegativeLeastSquaresValue B γ hγ hlower
      (representationToEuclidean 3 (mesoscalePlaneEmbedding k q)) ∂uniformCubeCoefficientLaw 2) ∧
    (∫ q, nonnegativeLeastSquaresValue B γ hγ hlower
      (representationToEuclidean 3 (mesoscalePlaneEmbedding k q)) ∂uniformCubeCoefficientLaw 2) ≤ 2 := by
  have hf : Measurable (fun q => representationToEuclidean 3 (mesoscalePlaneEmbedding k q)) :=
    (representationToEuclidean 3).continuous.measurable.comp (measurable_mesoscalePlaneEmbedding k)
  have hi := integrable_nonnegativeLeastSquaresValue (uniformCubeCoefficientLaw 2) hf
    (integrable_mesoscalePlane_secondMoment k) B γ hγ hlower
  constructor
  · exact integral_nonneg fun q => nonnegativeLeastSquaresValue_nonneg B γ hγ hlower _
  · have hbound : ∀ᵐ q ∂uniformCubeCoefficientLaw 2,
        nonnegativeLeastSquaresValue B γ hγ hlower
          (representationToEuclidean 3 (mesoscalePlaneEmbedding k q)) ≤ (2 : ℝ) := by
      filter_upwards [uniformCubeCoefficientLaw_ae_coordinate_bounds 2] with q hq
      apply (nonnegativeLeastSquaresValue_le_norm_sq B γ hγ hlower _).trans
      rw [norm_sq_mesoscalePlaneEmbedding]
      nlinarith [(hq 0).1, (hq 0).2, (hq 1).1, (hq 1).2]
    simpa using integral_mono_ae hi (integrable_const (2 : ℝ)) hbound

theorem nnls_mesoscaleReference_bounds {m : ℕ}
    (B : Matrix (Fin 3) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖) :
    0 ≤ (∑ s, mesoscaleReferenceWeight s *
      nonnegativeLeastSquaresValue B γ hγ hlower (mesoscaleReferenceInput s)) ∧
    (∑ s, mesoscaleReferenceWeight s *
      nonnegativeLeastSquaresValue B γ hγ hlower (mesoscaleReferenceInput s)) ≤ 2 := by
  have hw (s : Fin 3) : 0 ≤ mesoscaleReferenceWeight s := by
    fin_cases s <;> norm_num [mesoscaleReferenceWeight]
  constructor
  · exact Finset.sum_nonneg fun s _ => mul_nonneg (hw s)
      (nonnegativeLeastSquaresValue_nonneg B γ hγ hlower _)
  · apply (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (nonnegativeLeastSquaresValue_le_norm_sq B γ hγ hlower _) (hw s)).trans
    norm_num [mesoscaleReferenceWeight, mesoscaleReferenceInput, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succ, representationToEuclidean, Matrix.cons_val_two]

theorem real_mixture_reference_bound
    (δ θ H η D P R G : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ))
    (hF : 0 ≤ D + (3 / 5) * P ∧ D + (3 / 5) * P ≤ 2)
    (hG : 0 ≤ G ∧ G ≤ 2) (hR : |R - H ^ 2 * P| ≤ η * (2 * H + η)) :
    |(1 - θ) * (1 - δ) * D + (1 - θ) * δ * R + θ * G -
        (1 - δ) * (D + (3 / 5) * P)| ≤ δ * η * (2 * H + η) + 2 * θ := by
  have hbase : 0 ≤ (1 - δ) * (D + (3 / 5) * P) ∧
      (1 - δ) * (D + (3 / 5) * P) ≤ 2 := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr hδone) hF.1
    · nlinarith [mul_nonneg hδ hF.1]
  have hGdiff : |G - (1 - δ) * (D + (3 / 5) * P)| ≤ 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have heq : (1 - θ) * (1 - δ) * D + (1 - θ) * δ * R + θ * G -
      (1 - δ) * (D + (3 / 5) * P) =
      (1 - θ) * δ * (R - H ^ 2 * P) +
        θ * (G - (1 - δ) * (D + (3 / 5) * P)) := by
    nlinarith [congrArg (fun x : ℝ => (1 - θ) * P * x) hcal]
  rw [heq]
  apply (abs_add_le _ _).trans
  simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr hθone), abs_of_nonneg hδ,
    abs_of_nonneg hθ]
  have hfirst := mul_le_mul_of_nonneg_left hR (mul_nonneg (sub_nonneg.mpr hθone) hδ)
  have hsecond := mul_le_mul_of_nonneg_left hGdiff hθ
  have hpositive : 0 ≤ θ * δ * (η * (2 * H + η)) := by positivity
  nlinarith

/-- The actual population risk is uniformly close to the finite reference
objective. The bound holds at every width and every positive global margin;
it does not assume a particular optimizer or its active coordinates. -/
theorem nnls_mesoscalePopulation_perturbation {m : ℕ}
    (B : Matrix (Fin 3) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ)) :
    |nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
        (representationToEuclidean 3) B γ hγ hlower -
      (1 - δ) * ∑ s, mesoscaleReferenceWeight s *
        nonnegativeLeastSquaresValue B γ hγ hlower (mesoscaleReferenceInput s)| ≤
      δ * η * (2 * H + η) + 2 * θ := by
  let V := nonnegativeLeastSquaresValue B γ hγ hlower
  let D := (V (mesoscaleReferenceInput 0) + V (mesoscaleReferenceInput 1)) / 2
  let P := V (mesoscaleReferenceInput 2)
  let R := (V (representationToEuclidean 3 (mesoscalePlaneEmbedding 0 (mesoscaleRarePair H η))) +
    V (representationToEuclidean 3 (mesoscalePlaneEmbedding 1 (mesoscaleRarePair H η)))) / 2
  let G := ((∫ q, V (representationToEuclidean 3 (mesoscalePlaneEmbedding 0 q)) ∂uniformCubeCoefficientLaw 2) +
    ∫ q, V (representationToEuclidean 3 (mesoscalePlaneEmbedding 1 q)) ∂uniformCubeCoefficientLaw 2) / 2
  have hcube (k : Fin 2) : Integrable
      ((V ∘ representationToEuclidean 3) ∘ mesoscalePlaneEmbedding k) (uniformCubeCoefficientLaw 2) :=
    integrable_nonnegativeLeastSquaresValue (uniformCubeCoefficientLaw 2)
      ((representationToEuclidean 3).continuous.measurable.comp (measurable_mesoscalePlaneEmbedding k))
      (integrable_mesoscalePlane_secondMoment k) B γ hγ hlower
  have hmix := integral_mesoscalePopulationLaw δ θ H η hδ hδone hθ hθone
    ((continuous_nonnegativeLeastSquaresValue B γ hγ hlower).measurable.comp
      (representationToEuclidean 3).continuous.measurable) hcube
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
  have hGzero := nnls_mesoscaleCube_integral_bounds B γ hγ hlower 0
  have hGone := nnls_mesoscaleCube_integral_bounds B γ hγ hlower 1
  have hG : 0 ≤ G ∧ G ≤ 2 := by dsimp [G, V]; constructor <;> linarith
  have hRzero := abs_le.mp (nnls_mesoscaleRarePoint_perturbation B γ hγ hlower H η hH hη 0)
  have hRone := abs_le.mp (nnls_mesoscaleRarePoint_perturbation B γ hγ hlower H η hH hη 1)
  have hR : |R - H ^ 2 * P| ≤ η * (2 * H + η) := by
    apply abs_le.mpr
    dsimp [R, P, V]
    constructor <;> linarith
  have hrisk : nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
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
