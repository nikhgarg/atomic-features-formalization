import PKG26AtomicFeatures.HierarchicalInversePattern
import PKG26AtomicFeatures.NonnegativeLeastSquaresPopulation

/-!
# Hierarchical feature presence at every invertible zero-loss decoder

The sampling primitive is positive domination of both embedded independent
uniform parent-child squares. Zero actual population loss determines the
code almost everywhere. Closedness of nonnegative sparse codes upgrades the
resulting cube-almost-everywhere inverse-decoder constraints to the open
squares, where the finite-dimensional hierarchy pattern applies.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set Topology
open scoped ENNReal Matrix

/-- The set of nonnegative codes with the stated sparsity budget is closed. -/
theorem isClosed_nonnegative_sparse_codes (m K : ℕ) :
    IsClosed {v : FeatureVector m | (∀ j, 0 ≤ v j) ∧ (nonzeroSupport v).card ≤ K} := by
  classical
  have hnonneg : IsClosed {v : FeatureVector m | ∀ j, 0 ≤ v j} := by
    have heq : {v : FeatureVector m | ∀ j, 0 ≤ v j} =
        ⋂ j : Fin m, {v : FeatureVector m | 0 ≤ v j} := by ext v; simp
    rw [heq]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have hsparse : IsClosed {v : FeatureVector m | (nonzeroSupport v).card ≤ K} := by
    have heq : {v : FeatureVector m | (nonzeroSupport v).card ≤ K} =
        ⋃ S : {S : Finset (Fin m) // S.card ≤ K},
          (coordinateSpan S.1 : Set (FeatureVector m)) := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨⟨nonzeroSupport v, h⟩,
          mem_coordinateSpan_of_nonzeroSupport_subset (by rfl)⟩
      · rintro ⟨S, hv⟩
        exact (Finset.card_le_card (nonzeroSupport_subset_of_mem_coordinateSpan hv)).trans S.2
    rw [heq]
    exact isClosed_iUnion_of_finite fun S => (coordinateSpan S.1).closed_of_finiteDimensional
  exact hnonneg.inter hsparse

/-- A closed property holding almost everywhere under the uniform cube law
holds at every point of the open cube. This uses positivity of Lebesgue
measure on nonempty open sets, with no assumed support certificate. -/
theorem closed_property_on_open_cube_of_ae
    (K : ℕ) {F : Set (FeatureVector K)} (hF : IsClosed F)
    (hae : ∀ᵐ w ∂uniformCubeCoordinateLaw K, w ∈ F) :
    ∀ w : FeatureVector K, (∀ j, w j ∈ Set.Ioo (0 : ℝ) 1) → w ∈ F := by
  let U : Set (FeatureVector K) := Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have hUCube : U ⊆ coefficientUnitCube K := by
    intro w hw
    simp only [U, coefficientUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left] at hw ⊢
    exact fun j => ⟨(hw j).1.le, (hw j).2.le⟩
  have hvol : ∀ᵐ w ∂(volume : Measure (FeatureVector K)),
      w ∈ coefficientUnitCube K → w ∈ F :=
    ae_imp_of_ae_restrict hae
  have hnull : (volume : Measure (FeatureVector K)) (U ∩ Fᶜ) = 0 := by
    apply measure_mono_null (show U ∩ Fᶜ ⊆ {w | ¬ (w ∈ coefficientUnitCube K → w ∈ F)} from ?_) hvol
    intro w hw h
    exact hw.2 (h (hUCube hw.1))
  have hempty := (hU.inter hF.isOpen_compl).eq_empty_of_measure_zero hnull
  intro w hw
  by_contra hnot
  have hmem : w ∈ U ∩ Fᶜ := ⟨by simpa [U] using hw, hnot⟩
  simp only [hempty, Set.mem_empty_iff_false] at hmem

/-- Embed two Euclidean coefficients as the parent and the selected child. -/
noncomputable def hierarchicalParentChildEmbedding (child : Fin 2)
    (w : EuclideanRepresentation 2) : FeatureVector 3 :=
  hierarchicalParentChildCode child (w 0) (w 1)

theorem continuous_hierarchicalParentChildEmbedding (child : Fin 2) :
    Continuous (hierarchicalParentChildEmbedding child) := by
  have hsingle (j : Fin 3) : Continuous (fun a : ℝ => (Pi.single j a : FeatureVector 3)) :=
    continuous_single (A := fun _ : Fin 3 => ℝ) j
  exact ((hsingle 0).comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).add
    ((hsingle child.succ).comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1))

/-- The actual independent uniform parent-child square in source space. -/
noncomputable def hierarchicalParentChildCubeLaw (child : Fin 2) :
    Measure (FeatureVector 3) :=
  Measure.map (hierarchicalParentChildEmbedding child) (uniformCubeCoefficientLaw 2)

instance hierarchicalParentChildCubeLaw_isProbabilityMeasure (child : Fin 2) :
    IsProbabilityMeasure (hierarchicalParentChildCubeLaw child) := by
  unfold hierarchicalParentChildCubeLaw
  exact Measure.isProbabilityMeasure_map
    (continuous_hierarchicalParentChildEmbedding child).measurable.aemeasurable

/-- Coordinate-space form of the same embedded uniform sampling law. -/
theorem hierarchicalParentChildCubeLaw_eq_map_coordinates (child : Fin 2) :
    hierarchicalParentChildCubeLaw child =
      Measure.map (fun w : FeatureVector 2 => hierarchicalParentChildCode child (w 0) (w 1))
        (uniformCubeCoordinateLaw 2) := by
  rw [hierarchicalParentChildCubeLaw, uniformCubeCoefficientLaw,
    Measure.map_map (continuous_hierarchicalParentChildEmbedding child).measurable
      (representationToEuclidean 2).continuous.measurable]
  rfl

/-- An inverse decoder that is feasible almost everywhere on an actual cube
component is feasible everywhere on its open parent-child square. -/
theorem inverse_feasible_on_open_square_of_ae_cube
    (C : Matrix (Fin 3) (Fin 3) ℝ) (child : Fin 2)
    (hae : ∀ᵐ v ∂hierarchicalParentChildCubeLaw child,
      (∀ j, 0 ≤ C.mulVec v j) ∧ (nonzeroSupport (C.mulVec v)).card ≤ 2) :
    ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
      (∀ j, 0 ≤ C.mulVec (hierarchicalParentChildCode child a b) j) ∧
        (nonzeroSupport (C.mulVec (hierarchicalParentChildCode child a b))).card ≤ 2 := by
  let F : Set (FeatureVector 3) :=
    {v | (∀ j, 0 ≤ C.mulVec v j) ∧ (nonzeroSupport (C.mulVec v)).card ≤ 2}
  have hF : IsClosed F := (isClosed_nonnegative_sparse_codes 3 2).preimage
    C.mulVecLin.continuous_of_finiteDimensional
  have heuc : ∀ᵐ w ∂uniformCubeCoefficientLaw 2,
      hierarchicalParentChildEmbedding child w ∈ F :=
    (ae_map_iff (continuous_hierarchicalParentChildEmbedding child).measurable.aemeasurable
      hF.measurableSet).mp hae
  have hpre : IsClosed ((hierarchicalParentChildEmbedding child) ⁻¹' F) :=
    hF.preimage (continuous_hierarchicalParentChildEmbedding child)
  have hcoord : ∀ᵐ w ∂uniformCubeCoordinateLaw 2,
      hierarchicalParentChildEmbedding child (representationToEuclidean 2 w) ∈ F :=
    (ae_map_iff (representationToEuclidean 2).continuous.measurable.aemeasurable
      hpre.measurableSet).mp heuc
  intro a ha b hb
  have h := closed_property_on_open_cube_of_ae 2
    (hpre.preimage (representationToEuclidean 2).continuous) hcoord ![a, b] (by
      intro j
      fin_cases j
      · exact ha
      · exact hb)
  exact h

/-- Zero actual reconstruction loss at an invertible dictionary forces the
actual code to equal the matrix inverse applied to the source, almost everywhere. -/
theorem ae_eq_inverse_of_actualPopulationSquaredLoss_eq_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z u : Ω → FeatureVector 3)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hdet : B.det ≠ 0)
    (hz : Measurable z) (hu : Measurable u)
    (hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u = 0) :
    ∀ᵐ ω ∂μ, u ω = B⁻¹.mulVec (z ω) := by
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
    nlinarith [sq_nonneg ‖representationToEuclidean 3 (z ω) -
      representationToEuclidean 3 (B.mulVec (u ω))‖,
      norm_nonneg (representationToEuclidean 3 (z ω) -
        representationToEuclidean 3 (B.mulVec (u ω)))]
  have hexact : z ω = B.mulVec (u ω) :=
    (representationToEuclidean 3).injective (sub_eq_zero.mp (norm_eq_zero.mp hnorm))
  rw [hexact, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Positive domination of the two actual cube components transfers the
almost-everywhere inverse constraints to each component. The preceding
closed-set result then supplies the whole open-square hypotheses. -/
theorem inverse_open_squares_of_zero_loss_and_cube_domination
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z u : Ω → FeatureVector 3)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hdet : B.det ≠ 0)
    (hz : Measurable z) (hu : Measurable u)
    (hcode : ∀ᵐ ω ∂μ, (∀ j, 0 ≤ u ω j) ∧ (nonzeroSupport (u ω)).card ≤ 2)
    (hdom : ∀ child : Fin 2, ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal c • hierarchicalParentChildCubeLaw child ≤ Measure.map z μ)
    (hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u = 0) :
    ∀ child : Fin 2, ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
      (∀ j, 0 ≤ B⁻¹.mulVec (hierarchicalParentChildCode child a b) j) ∧
        (nonzeroSupport (B⁻¹.mulVec (hierarchicalParentChildCode child a b))).card ≤ 2 := by
  have heq := ae_eq_inverse_of_actualPopulationSquaredLoss_eq_zero μ z u B hdet hz hu hloss
  have hclosed : IsClosed {v : FeatureVector 3 |
      (∀ j, 0 ≤ B⁻¹.mulVec v j) ∧ (nonzeroSupport (B⁻¹.mulVec v)).card ≤ 2} :=
    (isClosed_nonnegative_sparse_codes 3 2).preimage
      B⁻¹.mulVecLin.continuous_of_finiteDimensional
  have hlaw : ∀ᵐ v ∂Measure.map z μ,
      (∀ j, 0 ≤ B⁻¹.mulVec v j) ∧ (nonzeroSupport (B⁻¹.mulVec v)).card ≤ 2 := by
    apply (ae_map_iff hz.aemeasurable hclosed.measurableSet).mpr
    filter_upwards [heq, hcode] with ω hω hfeas
    rwa [← hω]
  intro child
  obtain ⟨c, hc, hcle⟩ := hdom child
  apply inverse_feasible_on_open_square_of_ae_cube B⁻¹ child
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hc).ne').mp
    (ae_mono hcle hlaw)

/-- Every invertible zero-loss nonnegative two-sparse decoder recovers all
three hierarchical presence events through one common permutation. The
hypotheses concern actual loss and domination by the actual sampling laws;
no decoder pattern, exact reconstruction, or presence conclusion is supplied. -/
theorem exists_hierarchical_presence_permutation_of_zero_loss
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z u : Ω → FeatureVector 3)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hdet : B.det ≠ 0)
    (hz : Measurable z) (hu : Measurable u)
    (hcode : ∀ᵐ ω ∂μ, (∀ j, 0 ≤ u ω j) ∧ (nonzeroSupport (u ω)).card ≤ 2)
    (hsource : ∀ᵐ ω ∂μ, (∀ j, 0 ≤ z ω j) ∧
      (z ω 0 = 0 → z ω 1 = 0 ∧ z ω 2 = 0))
    (hdom : ∀ child : Fin 2, ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal c • hierarchicalParentChildCubeLaw child ≤ Measure.map z μ)
    (hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u = 0) :
    ∃ p : Equiv.Perm (Fin 3), ∀ᵐ ω ∂μ, ∀ j, 0 < u ω (p j) ↔ 0 < z ω j := by
  have hCdet : B⁻¹.det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det B (isUnit_iff_ne_zero.mpr hdet)).ne_zero
  have hpatch := inverse_open_squares_of_zero_loss_and_cube_domination
    μ z u B hdet hz hu hcode hdom hloss
  obtain ⟨p, _, _, _, _, hp⟩ :=
    exists_hierarchical_inverse_pattern_of_open_squares B⁻¹ hCdet hpatch
  refine ⟨p, ?_⟩
  filter_upwards [ae_eq_inverse_of_actualPopulationSquaredLoss_eq_zero μ z u B hdet hz hu hloss,
    hsource] with ω heq hω
  rw [heq]
  exact hp (z ω) hω.1 hω.2

/-- The paper's positive-margin width-three feasible class supplies
invertibility; it need not be assumed separately at the population endpoint. -/
theorem exists_hierarchical_presence_permutation_of_feasible_zero_loss
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z u : Ω → FeatureVector 3)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hz : Measurable z) (hfeas : IsFeasibleRecoveryPair B u γ 2)
    (hsource : ∀ᵐ ω ∂μ, (∀ j, 0 ≤ z ω j) ∧
      (z ω 0 = 0 → z ω 1 = 0 ∧ z ω 2 = 0))
    (hdom : ∀ child : Fin 2, ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal c • hierarchicalParentChildCubeLaw child ≤ Measure.map z μ)
    (hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) z B u = 0) :
    ∃ p : Equiv.Perm (Fin 3), ∀ᵐ ω ∂μ, ∀ j, 0 < u ω (p j) ↔ 0 < z ω j := by
  have hinj : Function.Injective B.mulVec := by
    intro v w heq
    apply sub_eq_zero.mp
    apply hfeas.2.1.kernel_eq_zero hγ (v - w)
    · have hcard := Finset.card_le_univ (nonzeroSupport (v - w))
      simpa only [Fintype.card_fin] using hcard.trans (show 3 ≤ 2 * 2 by norm_num)
    · rw [Matrix.mulVec_sub, heq, sub_self]
  have hdet : B.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero
  apply exists_hierarchical_presence_permutation_of_zero_loss μ z u B hdet hz hfeas.2.2.1
    (Filter.Eventually.of_forall fun ω => ⟨hfeas.2.2.2.2 ω, hfeas.2.2.2.1 ω⟩)
    hsource hdom hloss

end PKG26AtomicFeatures
