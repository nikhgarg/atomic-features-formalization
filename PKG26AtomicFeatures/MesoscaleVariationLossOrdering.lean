import PKG26AtomicFeatures.MesoscaleVariationRisk
import PKG26AtomicFeatures.MesoscaleVariationWidthTwo
import PKG26AtomicFeatures.MesoscaleVariationWidthOne
import PKG26AtomicFeatures.MesoscaleLossOrdering
import PKG26AtomicFeatures.HierarchicalSupportRecovery

/-!
# Strict optimal loss ordering under bounded positive variation

The finite reference gap and an explicit width-two benchmark transfer to every
bounded positive variation law with the same numerical perturbation bound.
Topological support throughout the two parent-child squares rules out zero
loss below width three. The feasible sanitized identity attains zero loss at
width three; no density assumption is used.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal BigOperators

variable (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν]

/-- The benchmark's actual finite population risk. -/
noncomputable def mesoscaleBenchmarkPopulationRisk_withVariation (δ θ H η : ℝ) : ℝ :=
  nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw_withVariation ν δ θ H η)
    (representationToEuclidean 3) mesoscaleBenchmarkDictionary (1 / 2) (by norm_num)
    (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))

theorem mesoscaleBenchmarkPopulationRisk_actual_loss_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id mesoscaleBenchmarkDictionary
      mesoscaleBenchmarkPopulationEncoder = ENNReal.ofReal (mesoscaleBenchmarkPopulationRisk_withVariation ν δ θ H η) := by
  symm
  simpa only [mesoscaleBenchmarkPopulationRisk_withVariation, mesoscaleBenchmarkPopulationEncoder,
    actualPopulationSquaredLoss, euclideanPopulationSquaredLoss, Matrix.one_mulVec, id_eq] using
    ofReal_nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (representationToEuclidean 3).continuous.measurable
      (integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η) mesoscaleBenchmarkDictionary
      (1 / 2) (by norm_num)
      (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))

/-- The actual benchmark risk is below the canonical risk of every unit
width-one dictionary. The gap follows from the primitive calibrated mixture
parameters, not from an assumed risk comparison. -/
theorem mesoscaleBenchmarkPopulationRisk_lt_rank_one_risk_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ))
    (hsmall : δ * η * (2 * H + η) + 2 * θ < (1 - δ) / 10)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) :
    mesoscaleBenchmarkPopulationRisk_withVariation ν δ θ H η <
      nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw_withVariation ν δ θ H η)
        (representationToEuclidean 3) B 1 (by norm_num)
        ((one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num)) := by
  let hlower := (one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num : 1 ≤ 1)
  have hpert1 := abs_le.mp (nnls_mesoscalePopulation_perturbation_withVariation ν hν B 1 (by norm_num)
    hlower δ θ H η hδ hδone.le hθ hθone hH hη hcal)
  have hpert2 := abs_le.mp (nnls_mesoscalePopulation_perturbation_withVariation ν hν mesoscaleBenchmarkDictionary
    (1 / 2) (by norm_num) (mesoscaleBenchmarkDictionary_stable.global_bound_of_width_le (by norm_num))
    δ θ H η hδ hδone.le hθ hθone hH hη hcal)
  have hscale1 := mul_le_mul_of_nonneg_left
    (mesoscaleReference_rank_one_loss_ge B hunit 1 (by norm_num) hlower)
    (sub_nonneg.mpr hδone.le)
  have hscale2 := mul_lt_mul_of_pos_left mesoscaleBenchmark_referenceRisk_lt (sub_pos.mpr hδone)
  change _ < nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw_withVariation ν δ θ H η)
    (representationToEuclidean 3) B 1 (by norm_num) hlower
  have hupper2 := hpert2.2
  change mesoscaleBenchmarkPopulationRisk_withVariation ν δ θ H η -
    (1 - δ) * mesoscaleReferenceNNLSRisk mesoscaleBenchmarkDictionary
      mesoscaleBenchmarkDictionary_stable ≤ _ at hupper2
  nlinarith [hpert1.1, hupper2]

/-- Every nonnegative width-one encoder has at least its canonical NNLS
risk, retaining infinite competing loss through the nonnegative integral. -/
theorem mesoscale_rank_one_canonical_risk_le_actual_loss_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (B : Matrix (Fin 3) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B)
    (u : FeatureVector 3 → FeatureVector 1) (hnonneg : ∀ z j, 0 ≤ u z j) :
    ENNReal.ofReal (nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (representationToEuclidean 3) B 1 (by norm_num)
      ((one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num))) ≤
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u := by
  rw [ofReal_nonnegativeLeastSquaresPopulationRisk _
    (representationToEuclidean 3).continuous.measurable
    (integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η)]
  unfold actualPopulationSquaredLoss euclideanPopulationSquaredLoss
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  simpa only [Matrix.one_mulVec, id_eq, nonnegativeLeastSquaresEncoder, Function.comp_apply] using
    (nonnegativeLeastSquaresCode_isMinimizer B 1 (by norm_num)
      ((one_column_unit_stable B hunit 1).global_bound_of_width_le (by norm_num))
      (representationToEuclidean 3 z)).2 (u z) (hnonneg z)

/-- Every actual width-two global optimum beats every feasible width-one
pair. Width-one optimality is unnecessary for this stronger comparison. -/
theorem mesoscale_width_two_optimum_loss_lt_width_one_feasible_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ))
    (hsmall : δ * η * (2 * H + η) + 2 * θ < (1 - δ) / 10)
    (B₁ : Matrix (Fin 3) (Fin 1) ℝ) (u₁ : FeatureVector 3 → FeatureVector 1)
    (hfeas₁ : IsFeasibleRecoveryPair B₁ u₁ (1 / 2) 2)
    (B₂ : Matrix (Fin 3) (Fin 2) ℝ) (u₂ : FeatureVector 3 → FeatureVector 2)
    (hopt₂ : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ <
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₁ u₁ := by
  have hupper := hopt₂.2 mesoscaleBenchmarkDictionary mesoscaleBenchmarkPopulationEncoder
    mesoscaleBenchmarkPopulationEncoder_feasible
  rw [ENNReal.ofReal_one, one_mul, mesoscaleBenchmarkPopulationRisk_actual_loss_withVariation ν hν] at hupper
  have hgap := mesoscaleBenchmarkPopulationRisk_lt_rank_one_risk_withVariation ν hν δ θ H η
    hδ hδone hθ hθone hH hη hcal hsmall B₁ hfeas₁.1
  have hbase : 0 ≤ mesoscaleBenchmarkPopulationRisk_withVariation ν δ θ H η :=
    integral_nonneg fun _ => sq_nonneg _
  have henn : ENNReal.ofReal (mesoscaleBenchmarkPopulationRisk_withVariation ν δ θ H η) <
      ENNReal.ofReal (nonnegativeLeastSquaresPopulationRisk (mesoscalePopulationLaw_withVariation ν δ θ H η)
        (representationToEuclidean 3) B₁ 1 (by norm_num)
        ((one_column_unit_stable B₁ hfeas₁.1 1).global_bound_of_width_le (by norm_num))) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hbase).mpr hgap
  exact (hupper.trans_lt henn).trans_le
    (mesoscale_rank_one_canonical_risk_le_actual_loss_withVariation ν hν δ θ H η B₁ hfeas₁.1 u₁ hfeas₁.2.2.2.2)


/-- The positive variation law gives a nonnegative two-sparse hierarchical
source almost everywhere, independently of the mixture's topological support. -/
theorem mesoscalePopulationLaw_ae_source_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η,
      (∀ j, 0 ≤ z j) ∧ (nonzeroSupport z).card ≤ 2 ∧
        (z 0 = 0 → z 1 = 0 ∧ z 2 = 0) := by
  filter_upwards [mesoscalePopulationLaw_ae_hierarchicalPresence_withVariation ν hν δ θ H η hH hη,
    mesoscalePopulationLaw_ae_nonneg_withVariation ν hν δ θ H η hH hη] with z hp hn
  exact ⟨hn, hp.support_card.le, fun hz => (hp.1.ne' hz).elim⟩

/-- The sanitized identity attains zero loss for the actual variation mixture. -/
theorem mesoscalePopulationLaw_sanitized_identity_zero_loss_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id 1 (nonnegativeSparseIdentityEncoder 3 2) = 0 :=
  nonnegativeSparseIdentityEncoder_zero_loss_of_ae _
    ((mesoscalePopulationLaw_ae_source_withVariation ν hν δ θ H η hH hη).mono
      fun _ h => ⟨h.1, h.2.1⟩)

/-- The explicit feasible identity pair is a global width-three optimum. -/
theorem mesoscalePopulationLaw_sanitized_identity_isOptimal_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id 1 (nonnegativeSparseIdentityEncoder 3 2) (1 / 2) 1 2 :=
  nonnegativeSparseIdentityEncoder_isOptimal_of_ae _
    ((mesoscalePopulationLaw_ae_source_withVariation ν hν δ θ H η hH hη).mono
      fun _ h => ⟨h.1, h.2.1⟩)

/-- Comparison with the actual identity decoder forces every global
width-three optimum to have zero loss. -/
theorem mesoscalePopulationLaw_width_three_optimum_zero_loss_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 := by
  have h := hopt.2 1 (nonnegativeSparseIdentityEncoder 3 2)
    (nonnegativeSparseIdentityEncoder_feasible 3 2)
  rw [mesoscalePopulationLaw_sanitized_identity_zero_loss_withVariation ν hν δ θ H η hH hη,
    mul_zero] at h
  exact le_antisymm h bot_le

/-- Every optimal width-three decoder recovers all presence events through
one permutation and has the source's expected support under square support. -/
theorem mesoscalePopulationLaw_width_three_optimum_recovery_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (hsupport : HasParentChildSquareSupport (mesoscalePopulationLaw_withVariation ν δ θ H η))
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 ∧
      ∃ p : Equiv.Perm (Fin 3),
        (∀ᵐ z ∂mesoscalePopulationLaw_withVariation ν δ θ H η, ∀ j, 0 < u z (p j) ↔ 0 < z j) ∧
        (∀ j : Fin 3, singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η)
          {z | 0 < z j} u = 1) ∧
        expectedCodeSupportSize (mesoscalePopulationLaw_withVariation ν δ θ H η) u = 2 := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure_withVariation ν δ θ H η hδ hδone hθ hθone
  obtain ⟨hloss, p, hp, hf, hs⟩ := hierarchical_width_three_optimal_recovery_of_support
    (mesoscalePopulationLaw_withVariation ν δ θ H η)
    (mesoscalePopulationLaw_ae_source_withVariation ν hν δ θ H η hH hη) hsupport B u hopt
  refine ⟨hloss, p, hp, hf, hs.trans ?_⟩
  simpa only [Nat.cast_ofNat] using expectedCodeSupportSize_eq_of_ae_card
    (mesoscalePopulationLaw_withVariation ν δ θ H η) id 2
    (mesoscalePopulationLaw_ae_support_card_withVariation ν hν δ θ H η hH hη)

/-- Square support makes the actual width-two optimal loss positive, while
the same perturbation threshold separates width two from every feasible
width-one decoder. All three conclusions concern the actual loss integrals. -/
theorem mesoscale_actual_optimal_losses_strictly_ordered_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hH : 0 < H) (hη : 0 < η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ))
    (hsmall : δ * η * (2 * H + η) + 2 * θ < (1 - δ) / 10)
    (hsupport : HasParentChildSquareSupport (mesoscalePopulationLaw_withVariation ν δ θ H η))
    (B₁ : Matrix (Fin 3) (Fin 1) ℝ) (u₁ : FeatureVector 3 → FeatureVector 1)
    (hopt₁ : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₁ u₁ (1 / 2) 1 2)
    (B₂ : Matrix (Fin 3) (Fin 2) ℝ) (u₂ : FeatureVector 3 → FeatureVector 2)
    (hopt₂ : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ (1 / 2) 1 2)
    (B₃ : Matrix (Fin 3) (Fin 3) ℝ) (u₃ : FeatureVector 3 → FeatureVector 3)
    (hopt₃ : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₃ u₃ (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₃ u₃ = 0 ∧
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₃ u₃ <
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ ∧
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₂ u₂ <
    actualPopulationSquaredLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B₁ u₁ := by
  have hzero := mesoscalePopulationLaw_width_three_optimum_zero_loss_withVariation
    ν hν δ θ H η hH hη B₃ u₃ hopt₃
  refine ⟨hzero, ?_, ?_⟩
  · rw [hzero]
    exact actualPopulationSquaredLoss_pos_of_parent_child_square_support (by norm_num)
      (mesoscalePopulationLaw_withVariation ν δ θ H η) id u₂ B₂ measurable_id
      hopt₂.1.2.2.1 (by simpa only [Measure.map_id] using hsupport)
  · exact mesoscale_width_two_optimum_loss_lt_width_one_feasible_withVariation ν hν δ θ H η
      hδ hδone hθ hθone hH.le hη.le hcal hsmall B₁ u₁ hopt₁.1 B₂ u₂ hopt₂

/-- The explicit positive leading column attains the width-one optimum. -/
theorem exists_mesoscale_width_one_optimal_pair_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η) :
    ∃ (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1),
      IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 := by
  let B := oneColumnDictionary
    (symmetricFamilyLeadingDirection (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
      (mesoscaleParentChildMoment_withVariation ν δ θ H η) (mesoscaleChildSecondMoment_withVariation ν δ θ H η))
  exact ⟨B, oneColumnClippedFeatureMap B,
    mesoscale_leading_width_one_pair_optimal_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη⟩

/-- The optimal infima themselves are strictly ordered. Their attained
representatives are constructed internally, including the zero-loss identity. -/
theorem mesoscale_optimalRecoveryLoss_strictly_ordered_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hθ : 0 ≤ θ) (hθone : θ < 1) (hH : 0 < H) (hη : 0 < η)
    (hcal : δ * H ^ 2 = (3 / 5) * (1 - δ))
    (hsmall : δ * η * (2 * H + η) + 2 * θ < (1 - δ) / 10)
    (hsupport : HasParentChildSquareSupport (mesoscalePopulationLaw_withVariation ν δ θ H η)) :
    optimalRecoveryLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 = 0 ∧
    optimalRecoveryLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 <
    optimalRecoveryLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 2 ∧
    optimalRecoveryLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 2 <
    optimalRecoveryLoss (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 1 := by
  obtain ⟨B₁, u₁, hopt₁⟩ := exists_mesoscale_width_one_optimal_pair_withVariation
    ν hν δ θ H η hδ hδone hθ hθone hH hη
  obtain ⟨B₂, u₂, hopt₂⟩ := exists_mesoscale_width_two_optimal_pair_withVariation ν hν δ θ H η
  have hopt₃ := mesoscalePopulationLaw_sanitized_identity_isOptimal_withVariation ν hν δ θ H η hH hη
  have h := mesoscale_actual_optimal_losses_strictly_ordered_withVariation ν hν δ θ H η
    hδ hδone hθ hθone.le hH hη hcal hsmall hsupport B₁ u₁ hopt₁ B₂ u₂ hopt₂
    1 (nonnegativeSparseIdentityEncoder 3 2) hopt₃
  simpa only [hopt₁.loss_eq_optimalRecoveryLoss, hopt₂.loss_eq_optimalRecoveryLoss,
    hopt₃.loss_eq_optimalRecoveryLoss] using h

end PKG26AtomicFeatures
