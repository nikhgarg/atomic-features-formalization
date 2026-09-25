import PKG26AtomicFeatures.MesoscaleVariationCovariance
import PKG26AtomicFeatures.MesoscaleWidthOneRecovery

/-!
# Width-one recovery with arbitrary positive bounded variation

Fair child choice and positivity determine the exact F1 table at the actual
rank-one optimum. The variation component may have arbitrary dependence,
atoms, or a density. Its only premises here are probability and strictly
positive bounded coordinates.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators InnerProductSpace Matrix

variable (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν]

/-- Every measurable event invariant under the actual child swap has half
its probability on each child. Balance is derived from the population's
pushforward symmetry and its almost-sure exclusive child presence. -/
theorem mesoscale_symmetric_event_child_balance_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (E : Set (FeatureVector 3)) (hE : MeasurableSet E)
    (hsym : ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η,
      mesoscaleSwapChildren z ∈ E ↔ z ∈ E) :
    ∀ k : Fin 2, (mesoscalePopulationLaw_withVariation ν δ θ H η).real ({z | 0 < z k.succ} ∩ E) =
      (mesoscalePopulationLaw_withVariation ν δ θ H η).real E / 2 := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure_withVariation ν δ θ H η hδ hδone hθ hθone
  have hpre : mesoscaleSwapChildren ⁻¹' ({z : FeatureVector 3 | 0 < z 1} ∩ E)
      =ᵐ[mesoscalePopulationLaw_withVariation ν δ θ H η] ({z | 0 < z 2} ∩ E : Set (FeatureVector 3)) := by
    filter_upwards [hsym] with z hz
    apply propext
    change (0 < mesoscaleSwapChildren z 1 ∧ mesoscaleSwapChildren z ∈ E) ↔
      0 < z 2 ∧ z ∈ E
    rw [hz]
    rfl
  have hequal := map_measureReal_apply (μ := mesoscalePopulationLaw_withVariation ν δ θ H η)
    (s := {z : FeatureVector 3 | 0 < z 1} ∩ E) measurable_mesoscaleSwapChildren
    ((measurableSet_lt measurable_const (measurable_pi_apply (1 : Fin 3))).inter hE)
  rw [mesoscalePopulationLaw_swap_children_withVariation ν, measureReal_congr hpre] at hequal
  have hdiff : (E \ {z : FeatureVector 3 | 0 < z 1}) =ᵐ[mesoscalePopulationLaw_withVariation ν δ θ H η]
      ({z | 0 < z 2} ∩ E : Set (FeatureVector 3)) := by
    filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence_withVariation ν hν δ θ H η hH hη] with z hz
    apply propext
    change (z ∈ E ∧ ¬ 0 < z 1) ↔ 0 < z 2 ∧ z ∈ E
    rcases hz.2 with h | h
    · simp [h.1, h.2]
    · simp [h.1, h.2]
  have hsum := measureReal_inter_add_diff (μ := mesoscalePopulationLaw_withVariation ν δ θ H η) (s := E)
    (t := {z : FeatureVector 3 | 0 < z 1}) (measurableSet_lt measurable_const (measurable_pi_apply (1 : Fin 3)))
  rw [Set.inter_comm E] at hsum
  have hdiffReal : (mesoscalePopulationLaw_withVariation ν δ θ H η).real (E \ {z : FeatureVector 3 | 0 < z 1}) =
      (mesoscalePopulationLaw_withVariation ν δ θ H η).real ({z | 0 < z 2} ∩ E) := measureReal_congr hdiff
  intro k
  fin_cases k
  · change (mesoscalePopulationLaw_withVariation ν δ θ H η).real ({z | 0 < z 1} ∩ E) = _
    linarith
  · change (mesoscalePopulationLaw_withVariation ν δ θ H η).real ({z | 0 < z 2} ∩ E) = _
    linarith

/-- An actual measurable symmetric positive scalar code has exactly the
width-one F1 table. Neither threshold balance nor any F1 score is assumed. -/
theorem mesoscale_F1_table_of_symmetric_positive_scalar_code_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (u : FeatureVector 3 → FeatureVector 1) (hu : Measurable u)
    (hsym : ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, u (mesoscaleSwapChildren z) 0 = u z 0)
    (hpositive : ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, 0 < u z 0) :
    singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z 0} u = 1 ∧
      ∀ k : Fin 2, singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η)
        {z | 0 < z k.succ} u = 2 / 3 := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure_withVariation ν δ θ H η hδ hδone hθ hθone
  have hfull : (mesoscalePopulationLaw_withVariation ν δ θ H η).real {z | 0 < u z 0} = 1 := by
    have hevent : {z | 0 < u z 0} =ᵐ[mesoscalePopulationLaw_withVariation ν δ θ H η]
        (Set.univ : Set (FeatureVector 3)) := by
      filter_upwards [hpositive] with z hz
      exact propext (iff_true_intro hz)
    rw [measureReal_congr hevent, probReal_univ]
  constructor
  · apply singleCoordinateF1Sup_eq_one_of_presence_ae
      (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z 0} u 0
    · filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence_withVariation ν hν δ θ H η hH hη,
        hpositive] with z hz hu
      exact propext ⟨fun _ => hu, fun _ => hz.1⟩
    · rw [mesoscalePopulationLaw_prevalence_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη]
      norm_num
  · intro k
    have htruth : (mesoscalePopulationLaw_withVariation ν δ θ H η).real {z | 0 < z k.succ} = 1 / 2 := by
      rw [mesoscalePopulationLaw_prevalence_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη]
      simp only [Fin.succ_ne_zero, ↓reduceIte]
    apply singleCoordinateF1Sup_eq_two_thirds_of_balanced_thresholds
      (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z k.succ} u
    · rw [htruth]
      norm_num
    · rw [hfull, htruth]
      norm_num
    · intro t _
      exact mesoscale_symmetric_event_child_balance_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη
        {z | t < u z 0}
        (measurableSet_lt measurable_const ((measurable_pi_apply 0).comp hu))
        (hsym.mono fun z hz => by
          change (t < u (mesoscaleSwapChildren z) 0) ↔ t < u z 0
          rw [hz]) k

/-- A coordinatewise positive direction has positive actual linear code
almost everywhere under the hierarchical population. -/
theorem mesoscale_inner_pos_ae_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η)
    (w : EuclideanRepresentation 3) (hw : ∀ j, 0 < w j) :
    ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η,
      0 < inner ℝ w (representationToEuclidean 3 z) := by
  filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence_withVariation ν hν δ θ H η hH hη] with z hz
  rw [mesoscale_inner_coordinates]
  have hp := mul_pos (hw 0) hz.1
  rcases hz.2 with h | h
  · rw [h.2, mul_zero, add_zero]
    exact add_pos hp (mul_pos (hw 1) h.1)
  · rw [h.1, mul_zero, add_zero]
    exact add_pos hp (mul_pos (hw 2) h.2)

/-- In particular, every strictly positive child-symmetric linear scalar
code has the exact parent/child F1 table on the actual population. -/
theorem mesoscale_F1_table_of_positive_symmetric_linear_code_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (w : EuclideanRepresentation 3) (hw : ∀ j, 0 < w j) (hsym : w 1 = w 2) :
    singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z 0}
      (fun z (_ : Fin 1) => inner ℝ w (representationToEuclidean 3 z)) = 1 ∧
      ∀ k : Fin 2, singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η)
        {z | 0 < z k.succ}
        (fun z (_ : Fin 1) => inner ℝ w (representationToEuclidean 3 z)) = 2 / 3 := by
  apply mesoscale_F1_table_of_symmetric_positive_scalar_code_withVariation ν hν δ θ H η
    hδ hδone hθ hθone hH hη
  · apply measurable_pi_lambda
    intro j
    exact (continuous_const.inner (representationToEuclidean 3).continuous).measurable
  · exact Filter.Eventually.of_forall (mesoscale_inner_swap_children w hsym)
  · exact mesoscale_inner_pos_ae_withVariation ν hν δ θ H η hH hη w hw

/-- Every actual width-one global pair optimum has the population's
positive leading column, and its actual scalar encoder is the corresponding
unclipped linear score almost everywhere. -/
theorem mesoscale_width_one_optimal_pair_leading_code_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    representationToEuclidean 3 (B.col 0) =
      symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
        (mesoscaleParentChildMoment_withVariation ν δ θ H η) (mesoscaleChildSecondMoment_withVariation ν δ θ H η) ∧
    ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, u z 0 = inner ℝ
      (symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
        (mesoscaleParentChildMoment_withVariation ν δ θ H η) (mesoscaleChildSecondMoment_withVariation ν δ θ H η))
      (representationToEuclidean 3 z) := by
  have hsecond := integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η
  have hmin := actual_width_one_optimal_pair_is_rank_one_minimizer
    (mesoscalePopulationLaw_withVariation ν δ θ H η) hsecond B u hopt
  refine ⟨mesoscalePopulationLaw_rank_one_minimizer_column_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη B hmin, ?_⟩
  have hcanonical := hopt.ae_eq_nonnegativeLeastSquaresEncoder (by norm_num) (by norm_num)
    (by simpa only [Matrix.one_mulVec, id_eq] using (representationToEuclidean 3).continuous.measurable)
    (by simpa only [Matrix.one_mulVec, id_eq] using hsecond.lintegral_lt_top)
  have hscore := hmin.ae_code_eq_positive_leading_score
    (representationToEuclidean 3).continuous.measurable hsecond _ _ _
    (mesoscaleParentChildMoment_pos_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη)
    (mesoscalePopulationLaw_quadratic_moment_withVariation ν hν δ θ H η)
    (mesoscalePopulationLaw_ae_nonneg_withVariation ν hν δ θ H η hH hη)
    (1 / 2) (by norm_num) (hopt.1.2.1.global_bound_of_width_le (by norm_num))
  filter_upwards [hcanonical, hscore] with z hz hscorez
  have hz0 := congrArg (fun v : FeatureVector 1 => v 0) hz
  simp only [nonnegativeLeastSquaresEncoder, Function.comp_apply, Matrix.one_mulVec, id_eq] at hz0
  exact hz0.trans hscorez

/-- The complete width-one feature table for every actual globally optimal
feasible pair. Covariance, leading direction, canonical encoding, positivity,
and symmetry are all derived from the primitive population and optimality. -/
theorem mesoscale_width_one_optimal_pair_F1_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z 0} u = 1 ∧
      ∀ k : Fin 2, singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η)
        {z | 0 < z k.succ} u = 2 / 3 := by
  let w := symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
    (mesoscaleParentChildMoment_withVariation ν δ θ H η) (mesoscaleChildSecondMoment_withVariation ν δ θ H η)
  have hcode : ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η,
      u z 0 = inner ℝ w (representationToEuclidean 3 z) :=
    (mesoscale_width_one_optimal_pair_leading_code_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη B u hopt).2
  have hscoremeas : Measurable (fun z => inner ℝ w (representationToEuclidean 3 z)) :=
    measurable_const.inner (representationToEuclidean 3).continuous.measurable
  have hswapcode : ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η,
      u (mesoscaleSwapChildren z) 0 = inner ℝ w (representationToEuclidean 3 (mesoscaleSwapChildren z)) := by
    apply (ae_map_iff measurable_mesoscaleSwapChildren.aemeasurable
      (measurableSet_eq_fun ((measurable_pi_apply 0).comp hopt.1.2.2.1) hscoremeas)).mp
    simpa only [mesoscalePopulationLaw_swap_children_withVariation ν] using hcode
  have hw : ∀ j, 0 < w j := symmetricFamilyLeadingDirection_pos _ _ _
    (mesoscaleParentChildMoment_pos_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη)
  apply mesoscale_F1_table_of_symmetric_positive_scalar_code_withVariation ν hν δ θ H η hδ hδone.le hθ hθone.le
    hH hη u hopt.1.2.2.1
  · filter_upwards [hcode, hswapcode] with z hz hsz
    rw [hz, hsz]
    exact mesoscale_inner_swap_children w (symmetricFamilyLeadingDirection_child_symmetry _ _ _) z
  · filter_upwards [hcode, mesoscale_inner_pos_ae_withVariation ν hν δ θ H η hH hη w hw] with z hz hpos
    rwa [hz]

/-- The positive leading dictionary and its actual clipped encoder attain
the global width-one optimum for the primitive mesoscale population. -/
theorem mesoscale_leading_width_one_pair_optimal_withVariation (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η) :
    let B := oneColumnDictionary
      (symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
        (mesoscaleParentChildMoment_withVariation ν δ θ H η) (mesoscaleChildSecondMoment_withVariation ν δ θ H η))
    IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B (oneColumnClippedFeatureMap B) (1 / 2) 1 2 := by
  apply rank_one_minimizer_clipped_pair_optimal _ (integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η)
  exact leading_isNonnegativeRankOnePopulationMinimizer
    (mesoscalePopulationLaw_withVariation ν δ θ H η) (representationToEuclidean 3)
    (representationToEuclidean 3).continuous.measurable (integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η)
    _ _ _ (mesoscaleParentChildMoment_pos_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη)
    (mesoscalePopulationLaw_quadratic_moment_withVariation ν hν δ θ H η)
    (mesoscalePopulationLaw_ae_nonneg_withVariation ν hν δ θ H η hH hη)


end PKG26AtomicFeatures
