import PKG26AtomicFeatures.MesoscaleZeroLossRecovery

/-!
# Attained width-three recovery for the explicit mesoscale law

The identity dictionary uses a globally feasible encoder: it retains
nonnegative two-sparse inputs and returns zero elsewhere. The explicit
population is supported on the retained inputs, giving actual zero loss.
Every globally optimal feasible width-three pair therefore has zero loss
and one common permutation recovering all three presence events and F1 values.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal Matrix

/-- Identity on nonnegative sparse vectors, extended by zero to every other input. -/
noncomputable def nonnegativeSparseIdentityEncoder (d K : ℕ) : FeatureVector d → FeatureVector d := by
  classical
  exact fun z => if (∀ j, 0 ≤ z j) ∧ (nonzeroSupport z).card ≤ K then z else 0

theorem measurable_nonnegativeSparseIdentityEncoder (d K : ℕ) :
    Measurable (nonnegativeSparseIdentityEncoder d K) := by
  classical
  exact Measurable.ite (isClosed_nonnegative_sparse_codes d K).measurableSet
    measurable_id measurable_const

theorem nonnegativeSparseIdentityEncoder_nonneg (d K : ℕ) (z : FeatureVector d) (j : Fin d) :
    0 ≤ nonnegativeSparseIdentityEncoder d K z j := by
  classical
  unfold nonnegativeSparseIdentityEncoder
  split_ifs with h
  · exact h.1 j
  · exact le_rfl

theorem nonnegativeSparseIdentityEncoder_sparse (d K : ℕ) :
    KSparse (K := K) (nonnegativeSparseIdentityEncoder d K) := by
  classical
  intro z
  unfold nonnegativeSparseIdentityEncoder
  split_ifs with h
  · exact h.2
  · simp [nonzeroSupport]

/-- Identity columns have unit genuine Euclidean norm. -/
theorem identityDictionary_unit (d : ℕ) :
    HasUnitEuclideanColumns (1 : Matrix (Fin d) (Fin d) ℝ) := by
  intro j
  have heq : representationToEuclidean d ((1 : Matrix (Fin d) (Fin d) ℝ).col j) =
      EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp [representationToEuclidean, Matrix.col, Matrix.one_apply, EuclideanSpace.single_apply,
      eq_comm]
  rw [heq]
  simp

/-- Identity synthesis is globally stable at every margin at most one. -/
theorem identityDictionary_stable (d s : ℕ) (γ : ℝ) (hγ : γ ≤ 1) :
    SparseLowerStable (1 : Matrix (Fin d) (Fin d) ℝ) γ s := by
  intro z _
  rw [Matrix.one_mulVec]
  exact mul_le_of_le_one_left (norm_nonneg _) hγ

/-- The sanitized identity pair is globally feasible on the full ambient
coefficient space, including inputs outside the population support. -/
theorem nonnegativeSparseIdentityEncoder_feasible (d K : ℕ) :
    IsFeasibleRecoveryPair (1 : Matrix (Fin d) (Fin d) ℝ)
      (nonnegativeSparseIdentityEncoder d K) (1 / 2) K :=
  ⟨identityDictionary_unit d, identityDictionary_stable d (2 * K) (1 / 2) (by norm_num),
    measurable_nonnegativeSparseIdentityEncoder d K, nonnegativeSparseIdentityEncoder_sparse d K,
    nonnegativeSparseIdentityEncoder_nonneg d K⟩

/-- Almost every actual mesoscale input is retained exactly by the globally
feasible sanitized identity encoder. -/
theorem mesoscalePopulationLaw_ae_sanitized_identity (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, nonnegativeSparseIdentityEncoder 3 2 z = z := by
  classical
  filter_upwards [mesoscalePopulationLaw_ae_nonnegative_hierarchy δ θ H η hH hη,
    mesoscalePopulationLaw_ae_support_card δ θ H η hH hη] with z hnonneg hcard
  exact if_pos (show (∀ j, 0 ≤ z j) ∧ (nonzeroSupport z).card ≤ 2 from ⟨hnonneg.1, hcard.le⟩)

/-- The explicit feasible width-three pair has zero actual expected loss. -/
theorem mesoscalePopulationLaw_sanitized_identity_zero_loss (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (nonnegativeSparseIdentityEncoder 3 2) = 0 := by
  unfold actualPopulationSquaredLoss
  calc
    _ = ∫⁻ _ : FeatureVector 3, (0 : ℝ≥0∞) ∂mesoscalePopulationLaw δ θ H η := by
      apply lintegral_congr_ae
      filter_upwards [mesoscalePopulationLaw_ae_sanitized_identity δ θ H η hH hη] with z hz
      simp only [Matrix.one_mulVec, id_eq, hz, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        ENNReal.ofReal_zero]
    _ = 0 := by simp

/-- The source's width-three optimum is attained by an explicit pair. -/
theorem mesoscalePopulationLaw_sanitized_identity_isOptimal (δ θ H η : ℝ)
    (hH : 0 < H) (hη : 0 < η) :
    IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (nonnegativeSparseIdentityEncoder 3 2) (1 / 2) 1 2 := by
  refine ⟨nonnegativeSparseIdentityEncoder_feasible 3 2, ?_⟩
  intro B u _
  rw [mesoscalePopulationLaw_sanitized_identity_zero_loss δ θ H η hH hη]
  exact bot_le

/-- Comparison with the explicit feasible identity pair forces zero loss
at every actual globally optimal width-three pair. -/
theorem mesoscalePopulationLaw_width_three_optimum_zero_loss
    (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hoptimal : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 := by
  have h := hoptimal.2 (1 : Matrix (Fin 3) (Fin 3) ℝ)
    (nonnegativeSparseIdentityEncoder 3 2) (nonnegativeSparseIdentityEncoder_feasible 3 2)
  rw [mesoscalePopulationLaw_sanitized_identity_zero_loss δ θ H η hH hη, mul_zero] at h
  exact le_antisymm h bot_le

/-- Every actual width-three global optimum recovers the three hierarchical
presence events through one permutation and has F1 supremum one for each
feature. Zero loss is a conclusion, not an assumed premise. -/
theorem mesoscalePopulationLaw_width_three_optimum_recovery
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hoptimal : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 ∧
    ∃ p : Equiv.Perm (Fin 3),
      (∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, ∀ j, 0 < u z (p j) ↔ 0 < z j) ∧
      ∀ j : Fin 3, singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z j} u = 1 := by
  have hloss := mesoscalePopulationLaw_width_three_optimum_zero_loss δ θ H η hH hη B u hoptimal
  exact ⟨hloss, mesoscale_zero_loss_presence_and_f1 δ θ H η (1 / 2)
    hδ hδone hθ hθone hH hη (by norm_num) B u hoptimal.1 hloss⟩

end PKG26AtomicFeatures
