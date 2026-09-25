import PKG26AtomicFeatures.MesoscaleVariationPopulation
import PKG26AtomicFeatures.MesoscaleCovariance

/-!
# Actual covariance for arbitrary positive bounded variation

Fair child choice gives the symmetric covariance structure independently of
the variation law. The dominant positive atom forces a strictly positive
parent-child cross moment. Finite moments follow from the bounded primitive
variation law, so the actual rank-one optimizer theorem applies.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped BigOperators InnerProductSpace

variable (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν]

noncomputable def mesoscaleParentSecondMoment_withVariation (δ θ H η : ℝ) : ℝ :=
  ∫ z, z 0 ^ 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η

noncomputable def mesoscaleParentChildMoment_withVariation (δ θ H η : ℝ) : ℝ :=
  ∫ z, z 0 * z 1 ∂mesoscalePopulationLaw_withVariation ν δ θ H η

noncomputable def mesoscaleChildSecondMoment_withVariation (δ θ H η : ℝ) : ℝ :=
  ∫ z, z 1 ^ 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η

theorem integrable_mesoscale_coordinate_product_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ) (i j : Fin 3) :
    Integrable (fun z => z i * z j) (mesoscalePopulationLaw_withVariation ν δ θ H η) :=
  integrable_coordinate_product_of_secondMoment _
    (integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η) i j

theorem integrable_mesoscalePlane_coordinate_product_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (k : Fin 2) (i j : Fin 3) :
    Integrable (fun q => mesoscalePlaneEmbedding k q i * mesoscalePlaneEmbedding k q j)
      (ν) := by
  apply (integrable_mesoscalePlane_secondMoment_withVariation ν hν k).mono'
    ((((measurable_pi_apply i).comp (measurable_mesoscalePlaneEmbedding k)).mul
      ((measurable_pi_apply j).comp (measurable_mesoscalePlaneEmbedding k))).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun q =>
    coordinate_product_norm_le_euclidean_sq (mesoscalePlaneEmbedding k q) i j

/-- The two children never occur in the same input, so their cross moment vanishes. -/
theorem mesoscale_child_cross_moment_zero_withVariation (δ θ H η : ℝ) :
    (∫ z, z 1 * z 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η) = 0 := by
  have hae : ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, z 1 * z 2 = 0 := by
    apply mesoscalePopulationLaw_ae_of_planes_withVariation ν δ θ H η _
      (measurableSet_eq_fun ((measurable_pi_apply 1).mul (measurable_pi_apply 2)) measurable_const)
    intro k
    filter_upwards [] with q
    fin_cases k <;> simp [mesoscalePlaneEmbedding, Matrix.cons_val_two]
  simpa using integral_congr_ae hae

/-- Swapping the children preserves every measurable expectation. -/
theorem integral_mesoscale_swap_children_withVariation (δ θ H η : ℝ)
    (g : FeatureVector 3 → ℝ) (hg : Measurable g) :
    (∫ z, g (mesoscaleSwapChildren z) ∂mesoscalePopulationLaw_withVariation ν δ θ H η) =
      ∫ z, g z ∂mesoscalePopulationLaw_withVariation ν δ θ H η := by
  rw [← integral_map measurable_mesoscaleSwapChildren.aemeasurable hg.aestronglyMeasurable,
    mesoscalePopulationLaw_swap_children_withVariation ν]

/-- All nine matrix entries are derived from the actual sampling law. -/
theorem mesoscale_coordinate_second_moment_withVariation (δ θ H η : ℝ) (i j : Fin 3) :
    (∫ z, z i * z j ∂mesoscalePopulationLaw_withVariation ν δ θ H η) =
      symmetricFamilyCovariance (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
        (mesoscaleParentChildMoment_withVariation ν δ θ H η) (mesoscaleChildSecondMoment_withVariation ν δ θ H η) i j := by
  have h02 := integral_mesoscale_swap_children_withVariation ν δ θ H η (fun z => z 0 * z 1)
    ((measurable_pi_apply 0).mul (measurable_pi_apply 1))
  have h22 := integral_mesoscale_swap_children_withVariation ν δ θ H η (fun z => z 1 ^ 2)
    ((measurable_pi_apply 1).pow_const 2)
  simp only [mesoscaleSwapChildren, Matrix.cons_val_zero, Matrix.cons_val_one] at h02 h22
  fin_cases i <;> fin_cases j
  · change (∫ z, z 0 * z 0 ∂mesoscalePopulationLaw_withVariation ν δ θ H η) = ∫ z, z 0 ^ 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η
    simp only [pow_two]
  · rfl
  · exact h02
  · change (∫ z, z 1 * z 0 ∂mesoscalePopulationLaw_withVariation ν δ θ H η) = ∫ z, z 0 * z 1 ∂mesoscalePopulationLaw_withVariation ν δ θ H η
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  · change (∫ z, z 1 * z 1 ∂mesoscalePopulationLaw_withVariation ν δ θ H η) = ∫ z, z 1 ^ 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η
    simp only [pow_two]
  · exact mesoscale_child_cross_moment_zero_withVariation ν δ θ H η
  · change (∫ z, z 2 * z 0 ∂mesoscalePopulationLaw_withVariation ν δ θ H η) = ∫ z, z 0 * z 1 ∂mesoscalePopulationLaw_withVariation ν δ θ H η
    calc
      _ = ∫ z, z 0 * z 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η :=
        integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
      _ = _ := h02
  · change (∫ z, z 2 * z 1 ∂mesoscalePopulationLaw_withVariation ν δ θ H η) = 0
    calc
      _ = ∫ z, z 1 * z 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η :=
        integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
      _ = 0 := mesoscale_child_cross_moment_zero_withVariation ν δ θ H η
  · change (∫ z, z 2 * z 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η) = ∫ z, z 1 ^ 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η
    simpa only [pow_two] using h22

/-- The complete quadratic moment identity for the actual population,
with no assumed covariance or eigenvector data. -/
theorem mesoscalePopulationLaw_quadratic_moment_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (v : EuclideanRepresentation 3) :
    (∫ z, inner ℝ v (representationToEuclidean 3 z) ^ 2 ∂mesoscalePopulationLaw_withVariation ν δ θ H η) =
      inner ℝ v (symmetricFamilyCovarianceAction (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
        (mesoscaleParentChildMoment_withVariation ν δ θ H η) (mesoscaleChildSecondMoment_withVariation ν δ θ H η) v) := by
  have hexpand (z : FeatureVector 3) :
      inner ℝ v (representationToEuclidean 3 z) ^ 2 =
        ∑ i : Fin 3, ∑ j : Fin 3, (v i * v j) * (z i * z j) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    norm_num [representationToEuclidean, real_inner_eq_re_inner, RCLike.inner_apply]
    ring
  simp_rw [hexpand]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (integrable_mesoscale_coordinate_product_withVariation ν hν δ θ H η i j).const_mul (v i * v j)))]
  simp_rw [integral_finset_sum _ (fun j _ =>
    (integrable_mesoscale_coordinate_product_withVariation ν hν δ θ H η _ j).const_mul (v _ * v j)),
    integral_const_mul, mesoscale_coordinate_second_moment_withVariation ν]
  simp only [symmetricFamilyCovarianceAction, symmetricFamilyCovariance, PiLp.inner_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [representationToEuclidean, real_inner_eq_re_inner, RCLike.inner_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

/-- The dominant atoms provide a strict positive parent-child moment;
all other mixture components contribute nonnegative amounts. -/
theorem mesoscaleParentChildMoment_pos_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η) : 0 < mesoscaleParentChildMoment_withVariation ν δ θ H η := by
  have hcube (k : Fin 2) : 0 ≤
      ∫ q, mesoscalePlaneEmbedding k q 0 * mesoscalePlaneEmbedding k q 1
        ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [variationLaw_ae_bounds ν hν] with q hq
    fin_cases k <;> simpa [mesoscalePlaneEmbedding, Matrix.cons_val_two] using
      (mul_nonneg (hq 0).1 (hq 1).1)
  have heq := integral_mesoscalePopulationLaw_withVariation ν δ θ H η hδ hδone.le hθ hθone.le
    ((measurable_pi_apply 0).mul (measurable_pi_apply 1))
    (fun k => integrable_mesoscalePlane_coordinate_product_withVariation ν hν k 0 1)
  change mesoscaleParentChildMoment_withVariation ν δ θ H η = _ at heq
  norm_num [mesoscalePlaneEmbedding, mesoscaleDominantPair, mesoscaleRarePair,
    representationToEuclidean, Matrix.cons_val_two] at heq
  have hθgap : 0 < 1 - θ := sub_pos.mpr hθone
  have hδgap : 0 < 1 - δ := sub_pos.mpr hδone
  have hdominant : 0 < (1 - θ) * (1 - δ) / 2 * (1 / 20 : ℝ) := by positivity
  have hrare : 0 ≤ (1 - θ) * δ / 2 * (H * η) := by positivity
  have hcontinuous := mul_nonneg (show 0 ≤ θ / 2 by positivity) (add_nonneg (hcube 0) (hcube 1))
  norm_num [mesoscalePlaneEmbedding, Matrix.cons_val_two] at hcontinuous
  linarith

/-- The population coefficients are nonnegative almost everywhere. -/
theorem mesoscalePopulationLaw_ae_nonneg_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, ∀ j, 0 ≤ representationToEuclidean 3 z j := by
  filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence_withVariation ν hν δ θ H η hH hη] with z hz
  rcases hz with ⟨hp, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ <;>
    intro j <;> fin_cases j <;> change 0 ≤ z _ <;> positivity

/-- Every actual width-one global optimum of this explicit population has
the positive, child-symmetric leading column determined by its true moments. -/
theorem mesoscalePopulationLaw_rank_one_minimizer_column_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 1) ℝ)
    (hmin : IsNonnegativeRankOnePopulationMinimizer
      (mesoscalePopulationLaw_withVariation ν δ θ H η) (representationToEuclidean 3) B) :
    representationToEuclidean 3 (B.col 0) =
      symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
        (mesoscaleParentChildMoment_withVariation ν δ θ H η) (mesoscaleChildSecondMoment_withVariation ν δ θ H η) := by
  exact hmin.column_eq_positive_leading (representationToEuclidean 3).continuous.measurable
    (integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η) _ _ _
    (mesoscaleParentChildMoment_pos_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη)
    (mesoscalePopulationLaw_quadratic_moment_withVariation ν hν δ θ H η)
    (mesoscalePopulationLaw_ae_nonneg_withVariation ν hν δ θ H η hH hη)


end PKG26AtomicFeatures
