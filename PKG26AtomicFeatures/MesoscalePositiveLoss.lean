import PKG26AtomicFeatures.MesoscaleZeroLossRecovery
import PKG26AtomicFeatures.MesoscaleRiskIntegration

/-!
# Strictly positive loss below three columns

Positive mass on both independent parent-child squares forces any exact
linear decoder to span all three coordinates. Closedness of its range
upgrades almost-everywhere cube inclusion to inclusion of the open squares.
Differences of interior points recover the three coordinate basis vectors.
Thus every measurable encoder has positive actual loss at width below three.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal Matrix

/-- A linear subspace containing both open parent-child squares contains
all three coordinate directions. -/
theorem submodule_eq_top_of_parent_child_open_squares
    (S : Submodule ℝ (FeatureVector 3))
    (hopen : ∀ (child : Fin 2) (a b : ℝ), a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 →
      hierarchicalParentChildCode child a b ∈ S) : S = ⊤ := by
  have hparent : (Pi.single 0 1 : FeatureVector 3) ∈ S := by
    have h := S.smul_mem (4 : ℝ) (S.sub_mem
      (hopen 0 (1 / 2) (1 / 2) (by constructor <;> norm_num) (by constructor <;> norm_num))
      (hopen 0 (1 / 4) (1 / 2) (by constructor <;> norm_num) (by constructor <;> norm_num)))
    have heq : (4 : ℝ) • (hierarchicalParentChildCode 0 (1 / 2) (1 / 2) -
        hierarchicalParentChildCode 0 (1 / 4) (1 / 2)) = (Pi.single 0 1 : FeatureVector 3) := by
      ext j
      fin_cases j <;> norm_num [hierarchicalParentChildCode, Pi.single_apply, Fin.succ]
    rwa [heq] at h
  have hchild (child : Fin 2) : (Pi.single child.succ 1 : FeatureVector 3) ∈ S := by
    have h := S.smul_mem (4 : ℝ) (S.sub_mem
      (hopen child (1 / 2) (1 / 2) (by constructor <;> norm_num) (by constructor <;> norm_num))
      (hopen child (1 / 2) (1 / 4) (by constructor <;> norm_num) (by constructor <;> norm_num)))
    have heq : (4 : ℝ) • (hierarchicalParentChildCode child (1 / 2) (1 / 2) -
        hierarchicalParentChildCode child (1 / 2) (1 / 4)) =
          (Pi.single child.succ 1 : FeatureVector 3) := by
      ext j
      fin_cases child <;> fin_cases j <;> norm_num [hierarchicalParentChildCode, Pi.single_apply, Fin.succ]
    rwa [heq] at h
  apply top_unique
  intro z _
  have heq : z = z 0 • (Pi.single 0 1 : FeatureVector 3) +
      z 1 • (Pi.single 1 1 : FeatureVector 3) + z 2 • (Pi.single 2 1 : FeatureVector 3) := by
    ext j
    fin_cases j <;> simp
  rw [heq]
  exact S.add_mem (S.add_mem (S.smul_mem _ hparent) (S.smul_mem _ (hchild 0)))
    (S.smul_mem _ (hchild 1))

/-- A linear subspace containing both parent-child cube laws almost everywhere
must be the whole three-dimensional source space. -/
theorem submodule_eq_top_of_parent_child_cubes_ae
    (S : Submodule ℝ (FeatureVector 3))
    (hae : ∀ child : Fin 2, ∀ᵐ z ∂hierarchicalParentChildCubeLaw child, z ∈ S) :
    S = ⊤ := by
  have hopen (child : Fin 2) (a b : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
      hierarchicalParentChildCode child a b ∈ S := by
    let f : FeatureVector 2 → FeatureVector 3 := fun w =>
      hierarchicalParentChildCode child (w 0) (w 1)
    have hf : Continuous f := (continuous_hierarchicalParentChildEmbedding child).comp
      (representationToEuclidean 2).continuous
    have hc : IsClosed (f ⁻¹' (S : Set (FeatureVector 3))) :=
      S.closed_of_finiteDimensional.preimage hf
    have hcoord : ∀ᵐ w ∂uniformCubeCoordinateLaw 2, f w ∈ S := by
      have h := hae child
      rw [hierarchicalParentChildCubeLaw_eq_map_coordinates] at h
      exact (ae_map_iff hf.measurable.aemeasurable S.closed_of_finiteDimensional.measurableSet).mp h
    exact closed_property_on_open_cube_of_ae 2 hc hcoord ![a, b] (by
      intro j
      fin_cases j
      · exact ha
      · exact hb)
  exact submodule_eq_top_of_parent_child_open_squares S hopen

/-- Zero actual loss forces source vectors into the actual decoder range
almost everywhere, without any sign, sparsity, or stability hypothesis. -/
theorem ae_mem_range_of_actualPopulationSquaredLoss_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector 3) (u : Ω → FeatureVector m)
    (B : Matrix (Fin 3) (Fin m) ℝ) (hz : Measurable z) (hu : Measurable u)
    (hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u = 0) :
    ∀ᵐ ω ∂μ, z ω ∈ LinearMap.range B.mulVecLin := by
  have hmeas := measurable_euclideanSquaredResidual
    ((representationToEuclidean 3).continuous.measurable.comp hz) B hu
  have hzero : ∀ᵐ ω ∂μ, ENNReal.ofReal
      (‖representationToEuclidean 3 (z ω) -
        representationToEuclidean 3 (B.mulVec (u ω))‖ ^ 2) = 0 := by
    apply (lintegral_eq_zero_iff' hmeas.aemeasurable).mp
    simpa only [actualPopulationSquaredLoss, Matrix.one_mulVec] using hloss
  filter_upwards [hzero] with ω hω
  have hnorm : ‖representationToEuclidean 3 (z ω) -
      representationToEuclidean 3 (B.mulVec (u ω))‖ = 0 := by
    have hle := ENNReal.ofReal_eq_zero.mp hω
    nlinarith [norm_nonneg (representationToEuclidean 3 (z ω) -
      representationToEuclidean 3 (B.mulVec (u ω)))]
  have hexact : z ω = B.mulVec (u ω) :=
    (representationToEuclidean 3).injective (sub_eq_zero.mp (norm_eq_zero.mp hnorm))
  exact ⟨u ω, hexact.symm⟩

/-- Positive domination of both actual cube laws rules out zero loss for
any dictionary with fewer than three columns and any measurable encoder.
The conclusion retains infinite loss through the nonnegative integral. -/
theorem actualPopulationSquaredLoss_pos_of_parent_child_cube_domination
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : m < 3)
    (μ : Measure Ω) (z : Ω → FeatureVector 3) (u : Ω → FeatureVector m)
    (B : Matrix (Fin 3) (Fin m) ℝ) (hz : Measurable z) (hu : Measurable u)
    (hdom : ∀ child : Fin 2, ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal c • hierarchicalParentChildCubeLaw child ≤ Measure.map z μ) :
    0 < actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u := by
  apply pos_iff_ne_zero.mpr
  intro hloss
  have hae := ae_mem_range_of_actualPopulationSquaredLoss_eq_zero μ z u B hz hu hloss
  have hrange := (LinearMap.range B.mulVecLin).closed_of_finiteDimensional
  have hlaw : ∀ᵐ v ∂Measure.map z μ, v ∈ LinearMap.range B.mulVecLin :=
    (ae_map_iff hz.aemeasurable hrange.measurableSet).mpr hae
  have htop : LinearMap.range B.mulVecLin = ⊤ := by
    apply submodule_eq_top_of_parent_child_cubes_ae
    intro child
    obtain ⟨c, hc, hcle⟩ := hdom child
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hc).ne').mp
      (ae_mono hcle hlaw)
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (LinearMap.range_eq_top.mp htop)
  have hle : 3 ≤ m := by simpa only [Module.finrank_pi, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hdim
  omega

/-- The explicit positive cube mixture supplies the domination itself.
No feasibility or exact-reconstruction premise is imposed on the encoder. -/
theorem mesoscalePopulationLaw_loss_pos_of_width_lt_three
    (δ θ H η : ℝ) (hθ : 0 < θ) {m : ℕ} (hm : m < 3)
    (B : Matrix (Fin 3) (Fin m) ℝ) (u : FeatureVector 3 → FeatureVector m)
    (hu : Measurable u) :
    0 < actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u := by
  apply actualPopulationSquaredLoss_pos_of_parent_child_cube_domination hm
    (mesoscalePopulationLaw δ θ H η) id u B measurable_id hu
  intro child
  refine ⟨θ / 2, by positivity, ?_⟩
  simpa only [Measure.map_id] using mesoscalePopulationLaw_cube_le δ θ H η child

/-- The finite-second-moment real canonical NNLS objective is strictly
positive as well; its identification with actual loss is proved explicitly. -/
theorem mesoscalePopulationLaw_nnls_risk_pos_of_width_lt_three
    (δ θ H η : ℝ) (hθ : 0 < θ) {m : ℕ} (hm : m < 3)
    (B : Matrix (Fin 3) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ v : FeatureVector m, γ * ‖representationToEuclidean m v‖ ≤
      ‖representationToEuclidean 3 (B.mulVec v)‖) :
    0 < nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
      (representationToEuclidean 3) B γ hγ hlower := by
  have hf := (representationToEuclidean 3).continuous.measurable
  have hpos := mesoscalePopulationLaw_loss_pos_of_width_lt_three δ θ H η hθ hm B
    (nonnegativeLeastSquaresEncoder (representationToEuclidean 3) B γ hγ hlower)
    (measurable_nonnegativeLeastSquaresEncoder hf B γ hγ hlower)
  have heq := ofReal_nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw δ θ H η)
    hf (integrable_mesoscalePopulation_secondMoment δ θ H η) B γ hγ hlower
  apply ENNReal.ofReal_pos.mp
  rw [heq]
  simpa only [actualPopulationSquaredLoss, euclideanPopulationSquaredLoss, Matrix.one_mulVec,
    id_eq] using hpos

end PKG26AtomicFeatures
