import PKG26AtomicFeatures.MesoscaleCovariance
import PKG26AtomicFeatures.MesoscaleSymmetricPredictions

/-!
# The actual width-one recovery table for the mesoscale population

Global optimality is imposed on the paper's actual normalized, stable,
nonnegative two-sparse dictionary/encoder pairs. Every unit one-column
dictionary is feasible with its clipped scalar encoder. Consequently the
actual pair optimum minimizes the rank-one NNLS risk, its column is the
positive symmetric leading direction, and its actual encoder equals that
linear score almost everywhere. The feature table follows without supplying
any of these intermediate conclusions as assumptions.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

/-- A unit single column has the paper's half margin at every sparsity order. -/
theorem one_column_unit_half_stable {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) (s : ℕ) :
    SparseLowerStable B (1 / 2) s := by
  intro v hv
  exact (mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (norm_nonneg _)).trans (one_column_unit_stable B hunit s v hv)

/-- The actual one-dimensional nonnegative least-squares encoder written
as the clipped inner product of its dictionary column and input. -/
noncomputable def oneColumnClippedFeatureMap {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) (x : FeatureVector d) : FeatureVector 1 :=
  fun _ => nonnegativeRankOneCode (representationToEuclidean d (B.col 0))
    (representationToEuclidean d x)

theorem measurable_oneColumnClippedFeatureMap {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) : Measurable (oneColumnClippedFeatureMap B) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_const.max (measurable_const.inner
    (representationToEuclidean d).continuous.measurable)

/-- Every unit rank-one dictionary is an admissible competitor in the
actual half-stable, two-sparse recovery-pair optimization. -/
theorem oneColumnClippedFeatureMap_feasible {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) :
    IsFeasibleRecoveryPair B (oneColumnClippedFeatureMap B) (1 / 2) 2 := by
  refine ⟨hunit, one_column_unit_half_stable B hunit 4,
    measurable_oneColumnClippedFeatureMap B, ?_, ?_⟩
  · intro x
    have h := Finset.card_le_univ (nonzeroSupport (oneColumnClippedFeatureMap B x))
    exact (by simpa only [Fintype.card_fin] using h : _ ≤ 1).trans (by norm_num)
  · intro x j
    exact le_max_left _ _

/-- The explicit clipped competitor's actual ENNReal loss is the real
rank-one risk, with integrability derived from the actual input second moment. -/
theorem actualPopulationSquaredLoss_oneColumnClippedFeatureMap {d : ℕ}
    (μ : Measure (FeatureVector d))
    (hsecond : Integrable (fun x => ‖representationToEuclidean d x‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) :
    actualPopulationSquaredLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) id B
      (oneColumnClippedFeatureMap B) =
      ENNReal.ofReal (nonnegativeRankOnePopulationRisk μ (representationToEuclidean d) B) := by
  simp only [actualPopulationSquaredLoss, Matrix.one_mulVec, id_eq,
    one_column_euclidean_mulVec, oneColumnClippedFeatureMap, nonnegativeRankOnePopulationRisk]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_nonnegativeRankOne_residual μ (representationToEuclidean d)
      (representationToEuclidean d).continuous.measurable hsecond B hunit)
    (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm

/-- The actual pair comparison reaches every unit one-column dictionary,
so its dictionary minimizes the actual rank-one NNLS population objective. -/
theorem actual_width_one_optimal_pair_is_rank_one_minimizer {d : ℕ}
    (μ : Measure (FeatureVector d))
    (hsecond : Integrable (fun x => ‖representationToEuclidean d x‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin 1) ℝ) (u : FeatureVector d → FeatureVector 1)
    (hopt : IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ)
      id B u (1 / 2) 1 2) :
    IsNonnegativeRankOnePopulationMinimizer μ (representationToEuclidean d) B := by
  refine ⟨hopt.1.1, ?_⟩
  intro C hC
  have hmin : actualPopulationSquaredLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) id B
      (oneColumnClippedFeatureMap B) ≤
      actualPopulationSquaredLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) id B u := by
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    simpa only [Matrix.one_mulVec, id_eq, oneColumnClippedFeatureMap] using
      (nonnegativeRankOneCode_isMinimizer B hopt.1.1 (representationToEuclidean d x)).2
        (u x) (hopt.1.2.2.2.2 x)
  have hcomp := hopt.2 C (oneColumnClippedFeatureMap C) (oneColumnClippedFeatureMap_feasible C hC)
  simp only [ENNReal.ofReal_one, one_mul] at hcomp
  have hle := hmin.trans hcomp
  rw [actualPopulationSquaredLoss_oneColumnClippedFeatureMap μ hsecond B hopt.1.1,
    actualPopulationSquaredLoss_oneColumnClippedFeatureMap μ hsecond C hC] at hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  have hnn (D : Matrix (Fin d) (Fin 1) ℝ) :
      0 ≤ nonnegativeRankOnePopulationRisk μ (representationToEuclidean d) D :=
    integral_nonneg fun _ => sq_nonneg _
  simpa only [ENNReal.toReal_ofReal (hnn B), ENNReal.toReal_ofReal (hnn C)] using hreal

/-- Every actual width-one global pair optimum has the population's
positive leading column, and its actual scalar encoder is the corresponding
unclipped linear score almost everywhere. -/
theorem mesoscale_width_one_optimal_pair_leading_code
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    representationToEuclidean 3 (B.col 0) =
      symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment δ θ H η)
        (mesoscaleParentChildMoment δ θ H η) (mesoscaleChildSecondMoment δ θ H η) ∧
    ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, u z 0 = inner ℝ
      (symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment δ θ H η)
        (mesoscaleParentChildMoment δ θ H η) (mesoscaleChildSecondMoment δ θ H η))
      (representationToEuclidean 3 z) := by
  have hsecond := integrable_mesoscalePopulation_secondMoment δ θ H η
  have hmin := actual_width_one_optimal_pair_is_rank_one_minimizer
    (mesoscalePopulationLaw δ θ H η) hsecond B u hopt
  refine ⟨mesoscalePopulationLaw_rank_one_minimizer_column δ θ H η hδ hδone hθ hθone hH hη B hmin, ?_⟩
  have hcanonical := hopt.ae_eq_nonnegativeLeastSquaresEncoder (by norm_num) (by norm_num)
    (by simpa only [Matrix.one_mulVec, id_eq] using (representationToEuclidean 3).continuous.measurable)
    (by simpa only [Matrix.one_mulVec, id_eq] using hsecond.lintegral_lt_top)
  have hscore := hmin.ae_code_eq_positive_leading_score
    (representationToEuclidean 3).continuous.measurable hsecond _ _ _
    (mesoscaleParentChildMoment_pos δ θ H η hδ hδone hθ hθone hH hη)
    (mesoscalePopulationLaw_quadratic_moment δ θ H η)
    (mesoscalePopulationLaw_ae_nonneg δ θ H η hH hη)
    (1 / 2) (by norm_num) (hopt.1.2.1.global_bound_of_width_le (by norm_num))
  filter_upwards [hcanonical, hscore] with z hz hscorez
  have hz0 := congrArg (fun v : FeatureVector 1 => v 0) hz
  simp only [nonnegativeLeastSquaresEncoder, Function.comp_apply, Matrix.one_mulVec, id_eq] at hz0
  exact hz0.trans hscorez

/-- The complete width-one feature table for every actual globally optimal
feasible pair. Covariance, leading direction, canonical encoding, positivity,
and symmetry are all derived from the primitive population and optimality. -/
theorem mesoscale_width_one_optimal_pair_F1
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u = 1 ∧
      ∀ k : Fin 2, singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η)
        {z | 0 < z k.succ} u = 2 / 3 := by
  let w := symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment δ θ H η)
    (mesoscaleParentChildMoment δ θ H η) (mesoscaleChildSecondMoment δ θ H η)
  have hcode : ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η,
      u z 0 = inner ℝ w (representationToEuclidean 3 z) :=
    (mesoscale_width_one_optimal_pair_leading_code δ θ H η hδ hδone hθ hθone hH hη B u hopt).2
  have hscoremeas : Measurable (fun z => inner ℝ w (representationToEuclidean 3 z)) :=
    measurable_const.inner (representationToEuclidean 3).continuous.measurable
  have hswapcode : ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η,
      u (mesoscaleSwapChildren z) 0 = inner ℝ w (representationToEuclidean 3 (mesoscaleSwapChildren z)) := by
    apply (ae_map_iff measurable_mesoscaleSwapChildren.aemeasurable
      (measurableSet_eq_fun ((measurable_pi_apply 0).comp hopt.1.2.2.1) hscoremeas)).mp
    simpa only [mesoscalePopulationLaw_swap_children] using hcode
  have hw : ∀ j, 0 < w j := symmetricFamilyLeadingDirection_pos _ _ _
    (mesoscaleParentChildMoment_pos δ θ H η hδ hδone hθ hθone hH hη)
  apply mesoscale_F1_table_of_symmetric_positive_scalar_code δ θ H η hδ hδone.le hθ hθone.le
    hH hη u hopt.1.2.2.1
  · filter_upwards [hcode, hswapcode] with z hz hsz
    rw [hz, hsz]
    exact mesoscale_inner_swap_children w (symmetricFamilyLeadingDirection_child_symmetry _ _ _) z
  · filter_upwards [hcode, mesoscale_inner_pos_ae δ θ H η hH hη w hw] with z hz hpos
    rwa [hz]

/-- Conversely, a true global rank-one NNLS dictionary minimizer together
with its explicit clipped encoder is an actual globally optimal feasible pair. -/
theorem rank_one_minimizer_clipped_pair_optimal {d : ℕ}
    (μ : Measure (FeatureVector d))
    (hsecond : Integrable (fun x => ‖representationToEuclidean d x‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin 1) ℝ)
    (hmin : IsNonnegativeRankOnePopulationMinimizer μ (representationToEuclidean d) B) :
    IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ)
      id B (oneColumnClippedFeatureMap B) (1 / 2) 1 2 := by
  refine ⟨oneColumnClippedFeatureMap_feasible B hmin.1, ?_⟩
  intro C v hv
  simp only [ENNReal.ofReal_one, one_mul]
  have hpoint : actualPopulationSquaredLoss μ (1 : Matrix (Fin d) (Fin d) ℝ)
      id C (oneColumnClippedFeatureMap C) ≤
      actualPopulationSquaredLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) id C v := by
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    simpa only [Matrix.one_mulVec, id_eq, oneColumnClippedFeatureMap] using
      (nonnegativeRankOneCode_isMinimizer C hv.1 (representationToEuclidean d x)).2
        (v x) (hv.2.2.2.2 x)
  apply le_trans ?_ hpoint
  rw [actualPopulationSquaredLoss_oneColumnClippedFeatureMap μ hsecond B hmin.1,
    actualPopulationSquaredLoss_oneColumnClippedFeatureMap μ hsecond C hv.1]
  exact ENNReal.ofReal_le_ofReal (hmin.2 C hv.1)

/-- The positive leading dictionary and its actual clipped encoder attain
the global width-one optimum for the primitive mesoscale population. -/
theorem mesoscale_leading_width_one_pair_optimal
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η) :
    let B := oneColumnDictionary
      (symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment δ θ H η)
        (mesoscaleParentChildMoment δ θ H η) (mesoscaleChildSecondMoment δ θ H η))
    IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B (oneColumnClippedFeatureMap B) (1 / 2) 1 2 := by
  apply rank_one_minimizer_clipped_pair_optimal _ (integrable_mesoscalePopulation_secondMoment δ θ H η)
  exact leading_isNonnegativeRankOnePopulationMinimizer
    (mesoscalePopulationLaw δ θ H η) (representationToEuclidean 3)
    (representationToEuclidean 3).continuous.measurable (integrable_mesoscalePopulation_secondMoment δ θ H η)
    _ _ _ (mesoscaleParentChildMoment_pos δ θ H η hδ hδone hθ hθone hH hη)
    (mesoscalePopulationLaw_quadratic_moment δ θ H η)
    (mesoscalePopulationLaw_ae_nonneg δ θ H η hH hη)

/-- Null-set changes to the actual prediction event do not change its F1. -/
theorem populationF1_congr_prediction_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (truth : Set Ω)
    {prediction prediction' : Set Ω} (hprediction : prediction =ᵐ[μ] prediction') :
    populationF1 μ truth prediction = populationF1 μ truth prediction' := by
  have hinter : (truth ∩ prediction : Set Ω) =ᵐ[μ] (truth ∩ prediction' : Set Ω) := by
    filter_upwards [hprediction] with x hx
    exact congrArg (fun p : Prop => x ∈ truth ∧ p) hx
  rw [populationF1, populationF1, measureReal_congr hprediction, measureReal_congr hinter]

/-- Almost-everywhere equality of actual code maps preserves the entire
single-coordinate F1 supremum, for any measure, truth event, and learned width. -/
theorem singleCoordinateF1Sup_congr_code_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (truth : Set Ω) {u v : Ω → Fin m → ℝ} (heq : u =ᵐ[μ] v) :
    singleCoordinateF1Sup μ truth u = singleCoordinateF1Sup μ truth v := by
  have hscore (j : Fin m) (t : ℝ) :
      populationF1 μ truth {x | t < u x j} = populationF1 μ truth {x | t < v x j} := by
    apply populationF1_congr_prediction_ae
    filter_upwards [heq] with x hx
    exact congrArg (fun a : Fin m → ℝ => t < a j) hx
  unfold singleCoordinateF1Sup
  simp_rw [hscore]

end PKG26AtomicFeatures
