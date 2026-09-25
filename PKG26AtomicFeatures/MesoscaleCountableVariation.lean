import PKG26AtomicFeatures.CountableCoefficientLaw
import PKG26AtomicFeatures.CountablePopulationLift
import PKG26AtomicFeatures.MesoscaleVariationPopulation
import PKG26AtomicFeatures.HierarchicalTopologicalSupport
import PKG26AtomicFeatures.SparseCubeRetraction
import PKG26AtomicFeatures.PositivePopulationScaling

/-!
# A countable mesoscale population on any surjective source domain

The variation component has countably many atoms dense in the open square.
The resulting actual hierarchical mixture retains open-square topological
support, and positive scaling places it in the sparse source cube. Its
countable concentration permits a probability lift through any measurable
surjection onto that cube, without assuming a measurable section.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal Matrix

theorem denseCountableCubeCoefficientLaw_ae_pos_le_one (K : ℕ) :
    ∀ᵐ q ∂denseCountableCubeCoefficientLaw K, ∀ j, 0 < q j ∧ q j ≤ 1 :=
  (denseCountableCubeCoefficientLaw_ae_coordinates K).mono fun _ h j =>
    ⟨(h j).1, (h j).2.le⟩

private theorem countably_supported_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (h : ∃ S : Set X, S.Countable ∧ ∀ᵐ x ∂μ, x ∈ S) :
    ∃ T : Set Y, T.Countable ∧ ∀ᵐ y ∂Measure.map f μ, y ∈ T := by
  obtain ⟨S, hS, hae⟩ := h
  refine ⟨f '' S, hS.image f, ?_⟩
  apply (ae_map_iff hf.aemeasurable (hS.image f).measurableSet).mpr
  exact hae.mono fun x hx => Set.mem_image_of_mem f hx

private theorem countably_supported_add_smul
    {Y : Type*} [MeasurableSpace Y] (μ ν : Measure Y) (a b : ℝ≥0∞)
    (hμ : ∃ S : Set Y, S.Countable ∧ ∀ᵐ y ∂μ, y ∈ S)
    (hν : ∃ S : Set Y, S.Countable ∧ ∀ᵐ y ∂ν, y ∈ S) :
    ∃ S : Set Y, S.Countable ∧ ∀ᵐ y ∂a • μ + b • ν, y ∈ S := by
  obtain ⟨S, hS, haeS⟩ := hμ
  obtain ⟨T, hT, haeT⟩ := hν
  refine ⟨S ∪ T, hS.union hT, ?_⟩
  rw [ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (haeS.mono fun _ h => Or.inl h) _,
    Measure.ae_smul_measure (haeT.mono fun _ h => Or.inr h) _⟩

/-- The unscaled mixture with the concrete countable variation law. -/
noncomputable def mesoscaleCountablePopulationLaw (δ θ H η : ℝ) :
    Measure (FeatureVector 3) :=
  mesoscalePopulationLaw_withVariation (denseCountableCubeCoefficientLaw 2) δ θ H η

theorem mesoscaleCountablePopulationLaw_isProbabilityMeasure (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (mesoscaleCountablePopulationLaw δ θ H η) :=
  mesoscalePopulationLaw_isProbabilityMeasure_withVariation _ δ θ H η hδ hδone hθ hθone

theorem mesoscalePairLaw_countably_supported_withVariation
    (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν]
    (hν : ∃ S : Set (EuclideanRepresentation 2), S.Countable ∧ ∀ᵐ q ∂ν, q ∈ S)
    (δ θ H η : ℝ) :
    ∃ S : Set (EuclideanRepresentation 2), S.Countable ∧
      ∀ᵐ q ∂mesoscalePairLaw_withVariation ν δ θ H η, q ∈ S := by
  have hdirac (q : EuclideanRepresentation 2) :
      ∃ S : Set (EuclideanRepresentation 2), S.Countable ∧ ∀ᵐ v ∂Measure.dirac q, v ∈ S :=
    ⟨{q}, Set.countable_singleton q, by simp⟩
  have htwo := countably_supported_add_smul (Measure.dirac mesoscaleDominantPair)
    (Measure.dirac (mesoscaleRarePair H η))
    (ENNReal.ofReal ((1 - θ) * (1 - δ))) (ENNReal.ofReal ((1 - θ) * δ))
    (hdirac _) (hdirac _)
  simpa only [one_smul] using countably_supported_add_smul _ ν 1 (ENNReal.ofReal θ) htwo hν

theorem mesoscaleCountablePopulationLaw_countably_supported (δ θ H η : ℝ) :
    ∃ S : Set (FeatureVector 3), S.Countable ∧
      ∀ᵐ z ∂mesoscaleCountablePopulationLaw δ θ H η, z ∈ S := by
  have hpair := mesoscalePairLaw_countably_supported_withVariation _
    (denseCountableCubeCoefficientLaw_countably_supported 2) δ θ H η
  exact countably_supported_add_smul _ _ (1 / 2) (1 / 2)
    (countably_supported_map _ _ (measurable_mesoscalePlaneEmbedding 0) hpair)
    (countably_supported_map _ _ (measurable_mesoscalePlaneEmbedding 1) hpair)

/-- Every open parent-child square lies in the actual mixture's support.
The positive variation weight is used directly in the mixture formula. -/
theorem mesoscalePopulationLaw_hasParentChildSquareSupport_withVariation
    (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν]
    (hν : ∀ q : EuclideanRepresentation 2, (∀ j, q j ∈ Ioo (0 : ℝ) 1) → q ∈ ν.support)
    (δ θ H η : ℝ) (hθ : 0 < θ) :
    HasParentChildSquareSupport (mesoscalePopulationLaw_withVariation ν δ θ H η) := by
  intro child a b ha hb
  let q : EuclideanRepresentation 2 := representationToEuclidean 2 ![a, b]
  have hq : q ∈ ν.support := hν q (by
    intro j
    fin_cases j
    · simpa [q, representationToEuclidean] using ha
    · simpa [q, representationToEuclidean] using hb)
  have hembed : mesoscalePlaneEmbedding child q = hierarchicalParentChildCode child a b := by
    rw [mesoscalePlaneEmbedding_eq_hierarchicalParentChildEmbedding]
    rfl
  rw [Measure.support_eq_forall_isOpen]
  intro U hwU hU
  have hpre : 0 < ν (mesoscalePlaneEmbedding child ⁻¹' U) := by
    apply (Measure.mem_support_iff_forall q).mp hq
    have hc : Continuous (mesoscalePlaneEmbedding child) := by
      rw [mesoscalePlaneEmbedding_eq_hierarchicalParentChildEmbedding]
      exact continuous_hierarchicalParentChildEmbedding child
    exact (hU.preimage hc).mem_nhds (by simpa [Set.mem_preimage, hembed] using hwU)
  have hvar : ENNReal.ofReal θ • ν ≤ mesoscalePairLaw_withVariation ν δ θ H η :=
    Measure.le_add_left le_rfl
  have hp : 0 < mesoscalePairLaw_withVariation ν δ θ H η
      (mesoscalePlaneEmbedding child ⁻¹' U) := by
    apply (ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr hθ, hpre⟩).trans_le
    exact hvar _
  have hmap : 0 < (Measure.map (mesoscalePlaneEmbedding child)
      (mesoscalePairLaw_withVariation ν δ θ H η)) U := by
    rwa [Measure.map_apply (measurable_mesoscalePlaneEmbedding child) hU.measurableSet]
  have hhalf : 0 < (1 / 2 : ℝ≥0∞) *
      (Measure.map (mesoscalePlaneEmbedding child) (mesoscalePairLaw_withVariation ν δ θ H η)) U :=
    ENNReal.mul_pos_iff.mpr ⟨by norm_num, hmap⟩
  apply hhalf.trans_le
  simp only [mesoscalePopulationLaw_withVariation, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  fin_cases child
  · exact le_add_right le_rfl
  · exact le_add_left le_rfl

theorem mesoscaleCountablePopulationLaw_hasParentChildSquareSupport (δ θ H η : ℝ)
    (hθ : 0 < θ) : HasParentChildSquareSupport (mesoscaleCountablePopulationLaw δ θ H η) :=
  mesoscalePopulationLaw_hasParentChildSquareSupport_withVariation _
    (mem_denseCountableCubeCoefficientLaw_support 2) δ θ H η hθ

/-- Positive common scaling places the actual countable population in the
unit cube while retaining its two-coordinate support pattern. -/
noncomputable def mesoscaleCountableScaledPopulationLaw (δ θ H η : ℝ) :
    Measure (FeatureVector 3) :=
  Measure.map (mesoscaleCoefficientScaling H) (mesoscaleCountablePopulationLaw δ θ H η)

theorem mesoscaleCountableScaledPopulationLaw_isProbabilityMeasure (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (mesoscaleCountableScaledPopulationLaw δ θ H η) := by
  letI := mesoscaleCountablePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  exact Measure.isProbabilityMeasure_map (measurable_mesoscaleCoefficientScaling H).aemeasurable

theorem mesoscaleCountableScaledPopulationLaw_countably_supported (δ θ H η : ℝ) :
    ∃ S : Set (FeatureVector 3), S.Countable ∧
      ∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, z ∈ S :=
  countably_supported_map _ _ (measurable_mesoscaleCoefficientScaling H)
    (mesoscaleCountablePopulationLaw_countably_supported δ θ H η)

theorem mesoscaleCountableScaledPopulationLaw_ae_sparseUnitCube (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) (hηone : η ≤ 1) :
    ∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, z ∈ SparseUnitCube 3 2 := by
  apply (ae_map_iff (measurable_mesoscaleCoefficientScaling H).aemeasurable
    (measurableSet_sparseUnitCube 3 2)).mpr
  filter_upwards [mesoscalePopulationLaw_ae_bounds_withVariation _
      (denseCountableCubeCoefficientLaw_ae_pos_le_one 2) δ θ H η hH hη hηone,
    mesoscalePopulationLaw_ae_support_card_withVariation _
      (denseCountableCubeCoefficientLaw_ae_pos_le_one 2) δ θ H η (by linarith) hη]
      with z hb hs
  have hHpos : 0 < H + 1 := by linarith
  have hscale : (1 / (H + 1) : ℝ) ≠ 0 := by positivity
  constructor
  · rw [mesoscaleCoefficientScaling, nonzeroSupport_smul_eq _ hscale, hs]
  · intro j
    change 0 ≤ (1 / (H + 1)) * z j ∧ (1 / (H + 1)) * z j ≤ 1
    constructor
    · exact mul_nonneg (by positivity) (hb j).1
    · rw [one_div, ← div_eq_inv_mul]
      exact (div_le_one hHpos).mpr (hb j).2

/-- The actual scaled mixture lifts to every measurable source map whose
range is the full sparse unit cube. Countable choice suffices for the lift. -/
theorem exists_mesoscaleCountableScaledPopulationLaw_lift
    {X : Type*} [MeasurableSpace X] (z : X → FeatureVector 3) (hz : Measurable z)
    (hrange : Set.range z = SparseUnitCube 3 2) (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 1 ≤ H) (hη : 0 < η) (hηone : η ≤ 1) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      Measure.map z μ = mesoscaleCountableScaledPopulationLaw δ θ H η := by
  letI := mesoscaleCountableScaledPopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  apply exists_probability_lift_of_countably_supported _ z hz
    (mesoscaleCountableScaledPopulationLaw_countably_supported δ θ H η)
  simpa only [hrange] using
    mesoscaleCountableScaledPopulationLaw_ae_sparseUnitCube δ θ H η hH hη hηone

end PKG26AtomicFeatures
