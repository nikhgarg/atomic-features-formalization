import PKG26AtomicFeatures.NonnegativeLeastSquaresContinuity
import PKG26AtomicFeatures.NonnegativeLeastSquaresDerivative
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
# Continuous population risk of stable nonnegative least squares

The input's second moment dominates every optimal squared residual.
Dominated convergence therefore gives continuity of the actual population
objective in a stable dictionary. The real integral is explicitly identified
with the nonnegative expected loss; its use does not discard infinite risk.
-/

namespace PKG26AtomicFeatures

open MeasureTheory

theorem continuous_nonnegativeLeastSquaresValue {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    Continuous (nonnegativeLeastSquaresValue B γ hγ hlower) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasFDerivAt_nonnegativeLeastSquaresValue B γ hγ hlower x).continuousAt

theorem nonnegativeLeastSquaresValue_nonneg {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) (x : EuclideanRepresentation d) :
    0 ≤ nonnegativeLeastSquaresValue B γ hγ hlower x := sq_nonneg _

theorem nonnegativeLeastSquaresValue_le_norm_sq {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) (x : EuclideanRepresentation d) :
    nonnegativeLeastSquaresValue B γ hγ hlower x ≤ ‖x‖ ^ 2 := by
  simpa only [Matrix.mulVec_zero, map_zero, sub_zero] using
    (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower x).2 0 (fun _ => le_rfl)

theorem integrable_nonnegativeLeastSquaresValue
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) {f : Ω → EuclideanRepresentation d} (hf : Measurable f)
    (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    Integrable (fun ω => nonnegativeLeastSquaresValue B γ hγ hlower (f ω)) μ := by
  apply hsecond.mono'
    (((continuous_nonnegativeLeastSquaresValue B γ hγ hlower).measurable.comp hf).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun ω => by
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (nonnegativeLeastSquaresValue_nonneg B γ hγ hlower _)]
    exact nonnegativeLeastSquaresValue_le_norm_sq B γ hγ hlower (f ω)

/-- Actual mean optimal squared residual, under the finite-second-moment
hypothesis used by its connection to nonnegative expected loss. -/
noncomputable def nonnegativeLeastSquaresPopulationRisk
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) : ℝ :=
  ∫ ω, nonnegativeLeastSquaresValue B γ hγ hlower (f ω) ∂μ

theorem ofReal_nonnegativeLeastSquaresPopulationRisk
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) {f : Ω → EuclideanRepresentation d} (hf : Measurable f)
    (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    ENNReal.ofReal (nonnegativeLeastSquaresPopulationRisk μ f B γ hγ hlower) =
      euclideanPopulationSquaredLoss μ f B
        (nonnegativeLeastSquaresEncoder f B γ hγ hlower) := by
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_nonnegativeLeastSquaresValue μ hf hsecond B γ hγ hlower)
    (Filter.Eventually.of_forall fun ω => nonnegativeLeastSquaresValue_nonneg B γ hγ hlower _)

/-- Population risk is continuous on the actual dictionary space with a
common positive lower singular margin. The population need not be discrete. -/
theorem continuous_nonnegativeLeastSquaresPopulationRisk
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) {f : Ω → EuclideanRepresentation d} (hf : Measurable f)
    (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ) (γ : ℝ) (hγ : 0 < γ) :
    Continuous (fun B : GlobalStableDictionary d m γ =>
      nonnegativeLeastSquaresPopulationRisk μ f B.1 γ hγ B.2) := by
  letI : FirstCountableTopology (Matrix (Fin d) (Fin m) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin d → Fin m → ℝ))
  letI : FirstCountableTopology (GlobalStableDictionary d m γ) :=
    TopologicalSpace.Subtype.firstCountableTopology {B : Matrix (Fin d) (Fin m) ℝ |
      ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
        ‖representationToEuclidean d (B.mulVec u)‖}
  unfold nonnegativeLeastSquaresPopulationRisk
  apply continuous_of_dominated (bound := fun ω => ‖f ω‖ ^ 2)
  · intro B
    exact ((continuous_nonnegativeLeastSquaresValue B.1 γ hγ B.2).measurable.comp hf).aestronglyMeasurable
  · intro B
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (nonnegativeLeastSquaresValue_nonneg B.1 γ hγ B.2 _)]
      exact nonnegativeLeastSquaresValue_le_norm_sq B.1 γ hγ B.2 (f ω)
  · exact hsecond
  · apply Filter.Eventually.of_forall
    intro ω
    have hp : Continuous (fun B : GlobalStableDictionary d m γ => (B, f ω)) :=
      continuous_id.prodMk continuous_const
    change Continuous (fun B : GlobalStableDictionary d m γ =>
      ‖f ω - representationToEuclidean d (B.1.mulVec
        (stableDictionaryNNLSCode γ hγ (B, f ω)))‖ ^ 2)
    apply Continuous.comp (continuous_stableDictionaryNNLS_squaredResidual (d := d) (m := m) γ hγ) hp

end PKG26AtomicFeatures
