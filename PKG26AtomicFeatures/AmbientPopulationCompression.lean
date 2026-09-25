import PKG26AtomicFeatures.AmbientDictionaryCompression
import PKG26AtomicFeatures.NonnegativeLeastSquaresPopulation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Expected-loss compression with unchanged codes

The cross moments are actual Bochner integrals of code coefficients times
the source. Finite second moments make them integrable, and almost-everywhere
source-subspace membership puts their integrals in that subspace. The exact
quadratic loss identity then turns Gram-preserving finite compression into
nonincrease of the actual population loss, with the code map unchanged.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Module
open scoped ENNReal BigOperators

/-- Actual vector cross moment of one code coordinate and the source input. -/
noncomputable def populationCodeCrossMoment
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (u : Ω → FeatureVector m)
    (j : Fin m) : EuclideanRepresentation d := ∫ ω, u ω j • f ω ∂μ

/-- Two finite second moments dominate every vector-valued cross moment. -/
theorem integrable_code_mul_input_of_second_moments
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (u : Ω → FeatureVector m)
    (hf : Measurable f) (hu : Measurable u)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hu2 : Integrable (fun ω => ‖representationToEuclidean m (u ω)‖ ^ 2) μ) (j : Fin m) :
    Integrable (fun ω => u ω j • f ω) μ := by
  apply (hf2.add hu2).mono' (((measurable_pi_apply j).comp hu).smul hf).aestronglyMeasurable
  filter_upwards [] with ω
  have hj := PiLp.norm_apply_le (representationToEuclidean m (u ω)) j
  change ‖u ω j‖ ≤ ‖representationToEuclidean m (u ω)‖ at hj
  rw [norm_smul]
  change ‖u ω j‖ * ‖f ω‖ ≤ ‖f ω‖ ^ 2 + ‖representationToEuclidean m (u ω)‖ ^ 2
  have hprod := mul_le_mul_of_nonneg_right hj (norm_nonneg (f ω))
  nlinarith [sq_nonneg (‖f ω‖ - ‖representationToEuclidean m (u ω)‖),
    sq_nonneg ‖f ω‖, sq_nonneg ‖representationToEuclidean m (u ω)‖]

/-- Integration preserves a closed source subspace, without requiring the
measure to be a probability or even a finite measure. -/
theorem populationCodeCrossMoment_mem_subspace
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (u : Ω → FeatureVector m)
    (S : Submodule ℝ (EuclideanRepresentation d)) (hS : ∀ᵐ ω ∂μ, f ω ∈ S)
    (j : Fin m) (hint : Integrable (fun ω => u ω j • f ω) μ) :
    populationCodeCrossMoment μ f u j ∈ S := by
  apply S.starProjection_eq_self_iff.mp
  rw [populationCodeCrossMoment, ← S.starProjection.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [hS] with ω hω
  exact S.starProjection_eq_self_iff.mpr (S.smul_mem _ hω)

/-- Linear synthesis maps every finite code second moment to a finite
reconstruction second moment, for an arbitrary finite matrix. -/
theorem integrable_synthesis_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m)
    (hu : Measurable u)
    (hu2 : Integrable (fun ω => ‖representationToEuclidean m (u ω)‖ ^ 2) μ) :
    Integrable (fun ω => ‖representationToEuclidean d (B.mulVec (u ω))‖ ^ 2) μ := by
  let L : EuclideanRepresentation m →L[ℝ] EuclideanRepresentation d :=
    (Matrix.toEuclideanLin B).toContinuousLinearMap
  have hm : Measurable (fun ω => ‖representationToEuclidean d (B.mulVec (u ω))‖ ^ 2) :=
    (((representationToEuclidean d).continuous.measurable.comp
      (B.mulVecLin.continuous_of_finiteDimensional.measurable.comp hu)).norm.pow_const 2)
  apply (hu2.const_mul (‖L‖ ^ 2)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hbound := L.le_opNorm (representationToEuclidean m (u ω))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hbound
  simpa only [mul_pow] using hs

private theorem input_synthesis_inner_eq_sum {d m : ℕ}
    (x : EuclideanRepresentation d) (B : Matrix (Fin d) (Fin m) ℝ) (v : FeatureVector m) :
    inner ℝ x (representationToEuclidean d (B.mulVec v)) =
      ∑ j, inner ℝ (v j • x) (representationToEuclidean d (B.col j)) := by
  rw [euclidean_mulVec_eq_sum, inner_sum]
  simp only [real_inner_smul_right, real_inner_smul_left]

/-- The cross term in squared reconstruction loss is integrable under the
two second-moment hypotheses. -/
theorem integrable_input_synthesis_inner
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (B : Matrix (Fin d) (Fin m) ℝ)
    (u : Ω → FeatureVector m) (hf : Measurable f) (hu : Measurable u)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hu2 : Integrable (fun ω => ‖representationToEuclidean m (u ω)‖ ^ 2) μ) :
    Integrable (fun ω => inner ℝ (f ω) (representationToEuclidean d (B.mulVec (u ω)))) μ := by
  simp_rw [input_synthesis_inner_eq_sum]
  exact integrable_finset_sum _ fun j _ =>
    (integrable_code_mul_input_of_second_moments μ f u hf hu hf2 hu2 j).inner_const _

/-- The integrated cross term equals the actual finite vector cross-moment
pairing with the dictionary columns. -/
theorem integral_input_synthesis_inner_eq_cross_moments
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (B : Matrix (Fin d) (Fin m) ℝ)
    (u : Ω → FeatureVector m) (hf : Measurable f) (hu : Measurable u)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hu2 : Integrable (fun ω => ‖representationToEuclidean m (u ω)‖ ^ 2) μ) :
    (∫ ω, inner ℝ (f ω) (representationToEuclidean d (B.mulVec (u ω))) ∂μ) =
      ∑ j, inner ℝ (populationCodeCrossMoment μ f u j) (representationToEuclidean d (B.col j)) := by
  simp_rw [input_synthesis_inner_eq_sum]
  rw [integral_finset_sum _ (fun j _ =>
    (integrable_code_mul_input_of_second_moments μ f u hf hu hf2 hu2 j).inner_const _)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [populationCodeCrossMoment, real_inner_comm] using
    integral_inner (𝕜 := ℝ) (integrable_code_mul_input_of_second_moments μ f u hf hu hf2 hu2 j)
      (representationToEuclidean d (B.col j))

/-- Actual squared residuals are integrable under finite source and code
second moments. -/
theorem integrable_squared_residual_of_second_moments
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (B : Matrix (Fin d) (Fin m) ℝ)
    (u : Ω → FeatureVector m) (hf : Measurable f) (hu : Measurable u)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hu2 : Integrable (fun ω => ‖representationToEuclidean m (u ω)‖ ^ 2) μ) :
    Integrable (fun ω => ‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2) μ := by
  simp_rw [norm_sub_sq_real]
  exact (hf2.sub ((integrable_input_synthesis_inner μ f B u hf hu hf2 hu2).const_mul 2)).add
    (integrable_synthesis_second_moment μ B u hu hu2)

/-- The complete expected squared-loss decomposition uses derived Bochner
cross moments and actual synthesis norms. -/
theorem integral_squared_residual_eq_cross_moments
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (B : Matrix (Fin d) (Fin m) ℝ)
    (u : Ω → FeatureVector m) (hf : Measurable f) (hu : Measurable u)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hu2 : Integrable (fun ω => ‖representationToEuclidean m (u ω)‖ ^ 2) μ) :
    (∫ ω, ‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2 ∂μ) =
      (∫ ω, ‖f ω‖ ^ 2 ∂μ) + (∫ ω, ‖representationToEuclidean d (B.mulVec (u ω))‖ ^ 2 ∂μ) -
        2 * ∑ j, inner ℝ (populationCodeCrossMoment μ f u j) (representationToEuclidean d (B.col j)) := by
  have hi := integrable_input_synthesis_inner μ f B u hf hu hf2 hu2
  have hs := integrable_synthesis_second_moment μ B u hu hu2
  have hic : Integrable (fun ω => 2 * inner ℝ (f ω) (representationToEuclidean d (B.mulVec (u ω)))) μ := hi.const_mul 2
  have hid : Integrable (fun ω => ‖f ω‖ ^ 2 - 2 * inner ℝ (f ω) (representationToEuclidean d (B.mulVec (u ω)))) μ := hf2.sub hic
  simp_rw [norm_sub_sq_real]
  rw [integral_add hid hs, integral_sub hf2 hic,
    integral_const_mul, integral_input_synthesis_inner_eq_cross_moments μ f B u hf hu hf2 hu2]
  ring

/-- Ambient compression for actual expected squared loss. The code map is
unchanged, while the new dictionary lies in the source subspace and retains
its full Gram matrix, normalization, and sparse stability. -/
theorem exists_unit_stable_population_compression
    {Ω : Type*} [MeasurableSpace Ω] {d m s : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (u : Ω → FeatureVector m)
    (hf : Measurable f) (hu : Measurable u)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hu2 : Integrable (fun ω => ‖representationToEuclidean m (u ω)‖ ^ 2) μ)
    (S : Submodule ℝ (EuclideanRepresentation d)) (hdim : m ≤ finrank ℝ S)
    (hS : ∀ᵐ ω ∂μ, f ω ∈ S)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ)
    (hunit : HasUnitEuclideanColumns B) (hstable : SparseLowerStable B γ s) :
    ∃ B' : Matrix (Fin d) (Fin m) ℝ,
      (∀ j, representationToEuclidean d (B'.col j) ∈ S) ∧
      HasUnitEuclideanColumns B' ∧ SparseLowerStable B' γ s ∧
      (∀ i j,
        inner ℝ (representationToEuclidean d (B'.col i)) (representationToEuclidean d (B'.col j)) =
        inner ℝ (representationToEuclidean d (B.col i)) (representationToEuclidean d (B.col j))) ∧
      euclideanPopulationSquaredLoss μ f B' u ≤ euclideanPopulationSquaredLoss μ f B u := by
  have hc (j) : populationCodeCrossMoment μ f u j ∈ S :=
    populationCodeCrossMoment_mem_subspace μ f u S hS j
      (integrable_code_mul_input_of_second_moments μ f u hf hu hf2 hu2 j)
  obtain ⟨B', hB'S, hB'unit, hB'stable, hgram, hnorm, hobj⟩ :=
    exists_unit_stable_dictionary_compression S hdim B γ hunit hstable
      (populationCodeCrossMoment μ f u) hc
  refine ⟨B', hB'S, hB'unit, hB'stable, hgram, ?_⟩
  have hsynth : (∫ ω, ‖representationToEuclidean d (B'.mulVec (u ω))‖ ^ 2 ∂μ) =
      ∫ ω, ‖representationToEuclidean d (B.mulVec (u ω))‖ ^ 2 ∂μ := by
    simp_rw [hnorm]
  have hreal : (∫ ω, ‖f ω - representationToEuclidean d (B'.mulVec (u ω))‖ ^ 2 ∂μ) ≤
      ∫ ω, ‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2 ∂μ := by
    rw [integral_squared_residual_eq_cross_moments μ f B' u hf hu hf2 hu2,
      integral_squared_residual_eq_cross_moments μ f B u hf hu hf2 hu2, hsynth]
    linarith
  have hbridge (C : Matrix (Fin d) (Fin m) ℝ) :
      ENNReal.ofReal (∫ ω, ‖f ω - representationToEuclidean d (C.mulVec (u ω))‖ ^ 2 ∂μ) =
        euclideanPopulationSquaredLoss μ f C u :=
    ofReal_integral_eq_lintegral_ofReal
      (integrable_squared_residual_of_second_moments μ f C u hf hu hf2 hu2)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  rw [← hbridge B', ← hbridge B]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Positive global stability turns finite actual reconstruction loss and
finite source second moment into finite code second moment. -/
theorem integrable_code_second_moment_of_finite_loss
    {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (u : Ω → FeatureVector m)
    (hf : Measurable f) (hu : Measurable u)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ v : FeatureVector m, γ * ‖representationToEuclidean m v‖ ≤
      ‖representationToEuclidean d (B.mulVec v)‖)
    (hfinite : euclideanPopulationSquaredLoss μ f B u < ⊤) :
    Integrable (fun ω => ‖representationToEuclidean m (u ω)‖ ^ 2) μ := by
  have hm : Measurable (fun ω => ‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2) :=
    ((hf.sub ((representationToEuclidean d).continuous.measurable.comp
      (B.mulVecLin.continuous_of_finiteDimensional.measurable.comp hu))).norm.pow_const 2)
  have hr2 : Integrable (fun ω => ‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hfinite.ne
  have humeas := (((representationToEuclidean m).continuous.measurable.comp hu).norm.pow_const 2)
  apply (((hf2.add hr2).const_mul 2).div_const (γ ^ 2)).mono' humeas.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖representationToEuclidean m (u ω)‖ ^ 2 ≤
    2 * (‖f ω‖ ^ 2 + ‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ ^ 2) / γ ^ 2
  apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
  have htriangle : ‖representationToEuclidean d (B.mulVec (u ω))‖ ≤
      ‖f ω‖ + ‖f ω - representationToEuclidean d (B.mulVec (u ω))‖ := by
    simpa only [sub_sub_cancel] using
      norm_sub_le (f ω) (f ω - representationToEuclidean d (B.mulVec (u ω)))
  have hbound := (hlower (u ω)).trans htriangle
  have hsq := (sq_le_sq₀ (mul_nonneg hγ.le (norm_nonneg _))
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hbound
  nlinarith [sq_nonneg (‖f ω‖ - ‖f ω - representationToEuclidean d (B.mulVec (u ω))‖)]

/-- Compression from the actual finite-loss primitives. Testing stability
at least up to the learned width supplies the global bound and derives the
code moment, so no code-moment hypothesis is needed at this endpoint. -/
theorem exists_unit_stable_population_compression_of_finite_loss
    {Ω : Type*} [MeasurableSpace Ω] {d m s : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (u : Ω → FeatureVector m)
    (hf : Measurable f) (hu : Measurable u)
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (S : Submodule ℝ (EuclideanRepresentation d)) (hdim : m ≤ finrank ℝ S)
    (hS : ∀ᵐ ω ∂μ, f ω ∈ S)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hunit : HasUnitEuclideanColumns B) (hstable : SparseLowerStable B γ s)
    (hwidth : m ≤ s) (hfinite : euclideanPopulationSquaredLoss μ f B u < ⊤) :
    ∃ B' : Matrix (Fin d) (Fin m) ℝ,
      (∀ j, representationToEuclidean d (B'.col j) ∈ S) ∧
      HasUnitEuclideanColumns B' ∧ SparseLowerStable B' γ s ∧
      (∀ i j,
        inner ℝ (representationToEuclidean d (B'.col i)) (representationToEuclidean d (B'.col j)) =
        inner ℝ (representationToEuclidean d (B.col i)) (representationToEuclidean d (B.col j))) ∧
      euclideanPopulationSquaredLoss μ f B' u ≤ euclideanPopulationSquaredLoss μ f B u := by
  exact exists_unit_stable_population_compression μ f u hf hu hf2
    (integrable_code_second_moment_of_finite_loss μ f u hf hu hf2 B γ hγ
      (hstable.global_bound_of_width_le hwidth) hfinite)
    S hdim hS B γ hunit hstable

end PKG26AtomicFeatures
