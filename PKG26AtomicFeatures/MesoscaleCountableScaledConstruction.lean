import PKG26AtomicFeatures.MesoscaleCountableConstruction
import PKG26AtomicFeatures.OptimalLossScaling
import PKG26AtomicFeatures.SparseCubeRetraction

/-!
# One countable bounded mesoscale population with all three recovery regimes

A common positive coefficient scaling puts the explicit construction in
the sparse unit cube. The actual encoder transport preserves each feasible
optimization problem and every positive-threshold F1 supremum. Exact squared
loss scaling preserves the strict ordering of the three optimal values.
The expected-support secondary minima and countable concentration are
preserved as well. Thus the same primitive tuple supplies all conclusions
and permits lifting to arbitrary measurable source domains.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal

/-- The concrete normalization is the positive-scaling pushforward used
by the general optimizer and feature-score transport theorems. -/
theorem mesoscaleCountableScaledPopulationLaw_eq_scaledSourceLaw (δ θ H η : ℝ) :
    mesoscaleCountableScaledPopulationLaw δ θ H η =
      scaledSourceLaw (1 / (H + 1)) (mesoscaleCountablePopulationLaw δ θ H η) := rfl

/-- Positive scaling preserves the exact parent and exclusive-child pattern. -/
theorem mesoscaleCountableScaledPopulationLaw_ae_hierarchicalPresence (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, MesoscaleHierarchicalPresence z := by
  have hscale : 0 < (1 / (H + 1) : ℝ) := by positivity
  apply (ae_map_iff (measurable_mesoscaleCoefficientScaling H).aemeasurable
    measurableSet_mesoscaleHierarchicalPresence).mpr
  filter_upwards [mesoscaleCountablePopulationLaw_ae_hierarchicalPresence δ θ H η (by linarith) hη]
    with z hz
  rcases hz with ⟨hp, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
  · exact ⟨mul_pos hscale hp, Or.inl ⟨mul_pos hscale h1, by
      change (1 / (H + 1)) * z 2 = 0
      rw [h2, mul_zero]⟩⟩
  · exact ⟨mul_pos hscale hp, Or.inr ⟨by
      change (1 / (H + 1)) * z 1 = 0
      rw [h1, mul_zero], mul_pos hscale h2⟩⟩

theorem mesoscaleCountableScaledPopulationLaw_ae_support_card (δ θ H η : ℝ)
    (hH : 1 ≤ H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, (nonzeroSupport z).card = 2 :=
  (mesoscaleCountableScaledPopulationLaw_ae_hierarchicalPresence δ θ H η hH hη).mono
    fun _ hz => hz.support_card

/-- For each positive feature tolerance, one actual bounded, two-sparse
hierarchical population has attained optima at widths one, two, and three.
Every optimum has the stated feature table, and the actual optimal losses
strictly decrease to zero. All conclusions concern one explicit scaled law. -/
theorem exists_mesoscale_countable_scaled_construction (ε : ℝ) (hε : 0 < ε) :
    ∃ δ θ H η : ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < θ ∧ θ < 1 ∧ 1 ≤ H ∧ 0 < η ∧ η ≤ 1 ∧
      δ + θ ≤ ε / 2 ∧ δ * H ^ 2 = (3 / 5) * (1 - δ) ∧
      IsProbabilityMeasure (mesoscaleCountableScaledPopulationLaw δ θ H η) ∧
      (∃ S : Set (FeatureVector 3), S.Countable ∧
        ∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, z ∈ S) ∧
      (∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, z ∈ SparseUnitCube 3 2) ∧
      (∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, MesoscaleHierarchicalPresence z) ∧
      (∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, (nonzeroSupport z).card = 2) ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        ∃ (B : Matrix (Fin 3) (Fin m) ℝ) (u : FeatureVector 3 → FeatureVector m),
          IsApproximatelyOptimalRecoveryPair (mesoscaleCountableScaledPopulationLaw δ θ H η)
            (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 ∧
          ∀ (C : Matrix (Fin 3) (Fin m) ℝ) (v : FeatureVector 3 → FeatureVector m),
            IsApproximatelyOptimalRecoveryPair (mesoscaleCountableScaledPopulationLaw δ θ H η)
              (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v (1 / 2) 1 2 →
            expectedCodeSupportSize (mesoscaleCountableScaledPopulationLaw δ θ H η) u ≤
              expectedCodeSupportSize (mesoscaleCountableScaledPopulationLaw δ θ H η) v) ∧
      (∀ (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1),
        IsApproximatelyOptimalRecoveryPair (mesoscaleCountableScaledPopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        singleCoordinateF1Sup (mesoscaleCountableScaledPopulationLaw δ θ H η) {z | 0 < z 0} u = 1 ∧
          ∀ k : Fin 2, singleCoordinateF1Sup (mesoscaleCountableScaledPopulationLaw δ θ H η)
            {z | 0 < z k.succ} u = 2 / 3) ∧
      (∀ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
        IsApproximatelyOptimalRecoveryPair (mesoscaleCountableScaledPopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        singleCoordinateF1Sup (mesoscaleCountableScaledPopulationLaw δ θ H η) {z | 0 < z 0} u ≤ 2 / 3 + ε ∧
          ∀ k : Fin 2, 1 - ε ≤ singleCoordinateF1Sup (mesoscaleCountableScaledPopulationLaw δ θ H η)
            {z | 0 < z k.succ} u) ∧
      (∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3),
        IsApproximatelyOptimalRecoveryPair (mesoscaleCountableScaledPopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        actualPopulationSquaredLoss (mesoscaleCountableScaledPopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 ∧
        ∃ p : Equiv.Perm (Fin 3),
          (∀ᵐ z ∂mesoscaleCountableScaledPopulationLaw δ θ H η, ∀ j, 0 < u z (p j) ↔ 0 < z j) ∧
          ∀ j : Fin 3, singleCoordinateF1Sup (mesoscaleCountableScaledPopulationLaw δ θ H η)
            {z | 0 < z j} u = 1) ∧
      optimalRecoveryLoss (mesoscaleCountableScaledPopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 = 0 ∧
      optimalRecoveryLoss (mesoscaleCountableScaledPopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 <
        optimalRecoveryLoss (mesoscaleCountableScaledPopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 2 ∧
      optimalRecoveryLoss (mesoscaleCountableScaledPopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 2 <
        optimalRecoveryLoss (mesoscaleCountableScaledPopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 1 := by
  obtain ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, hbudget, hcal,
    _, _, _, hattain, hone, htwo, hthree, hzero, h32, h21⟩ :=
    exists_mesoscale_countable_unscaled_construction ε hε
  let s : ℝ := 1 / (H + 1)
  have hs : 0 < s := by dsimp [s]; positivity
  have hlaw : mesoscaleCountableScaledPopulationLaw δ θ H η =
      scaledSourceLaw s (mesoscaleCountablePopulationLaw δ θ H η) := rfl
  have hpull {m : ℕ} (B : Matrix (Fin 3) (Fin m) ℝ) (u : FeatureVector 3 → FeatureVector m)
      (hopt : IsApproximatelyOptimalRecoveryPair (mesoscaleCountableScaledPopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
      IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B (scaledFeatureMap s⁻¹ u) (1 / 2) 1 2 := by
    rw [hlaw] at hopt
    exact (isApproximatelyOptimalRecoveryPair_scaledSourceLaw_iff
      (mesoscaleCountablePopulationLaw δ θ H η) B u (1 / 2) 1 s hs).mp hopt
  have hscore {m : ℕ} (u : FeatureVector 3 → FeatureVector m) (hu : Measurable u) (j : Fin 3) :
      singleCoordinateF1Sup (mesoscaleCountableScaledPopulationLaw δ θ H η) {z | 0 < z j} u =
      singleCoordinateF1Sup (mesoscaleCountablePopulationLaw δ θ H η) {z | 0 < z j}
        (scaledFeatureMap s⁻¹ u) := by
    rw [hlaw]
    exact singleCoordinateF1Sup_scaledSourceLaw (mesoscaleCountablePopulationLaw δ θ H η) u hu s hs j
  have hloss (m : ℕ) :
      optimalRecoveryLoss (mesoscaleCountableScaledPopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 m =
      ENNReal.ofReal (s ^ 2) * optimalRecoveryLoss (mesoscaleCountablePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 m := by
    rw [hlaw]
    exact optimalRecoveryLoss_positive_scaling (mesoscaleCountablePopulationLaw δ θ H η) (1 / 2) s hs
  have hfactor : ENNReal.ofReal (s ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hs)).ne'
  refine ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, hbudget, hcal,
    mesoscaleCountableScaledPopulationLaw_isProbabilityMeasure δ θ H η hδ.le hδone.le hθ.le hθone.le,
    mesoscaleCountableScaledPopulationLaw_countably_supported δ θ H η,
    mesoscaleCountableScaledPopulationLaw_ae_sparseUnitCube δ θ H η hH hη hηone,
    mesoscaleCountableScaledPopulationLaw_ae_hierarchicalPresence δ θ H η hH hη,
    mesoscaleCountableScaledPopulationLaw_ae_support_card δ θ H η hH hη, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm hmthree
    obtain ⟨B, u, hopt, htie⟩ := hattain m hm hmthree
    refine ⟨B, scaledFeatureMap s u, ?_, ?_⟩
    · rw [hlaw]
      exact hopt.positive_scaling s hs
    · intro C v hv
      rw [hlaw, expectedCodeSupportSize_positive_scaling _ _ hopt.1.2.2.1 s hs.ne',
        expectedCodeSupportSize_scaledSourceLaw _ _ hv.1.2.2.1 s hs.ne']
      exact htie C (scaledFeatureMap s⁻¹ v) (hpull C v hv)
  · intro B u hopt
    obtain ⟨hp, hc⟩ := hone B (scaledFeatureMap s⁻¹ u) (hpull B u hopt)
    refine ⟨?_, ?_⟩
    · rw [hscore u hopt.1.2.2.1 0]
      exact hp
    · intro k
      rw [hscore u hopt.1.2.2.1 k.succ]
      exact hc k
  · intro B u hopt
    obtain ⟨hp, hc⟩ := htwo B (scaledFeatureMap s⁻¹ u) (hpull B u hopt)
    refine ⟨?_, ?_⟩
    · rw [hscore u hopt.1.2.2.1 0]
      exact hp
    · intro k
      rw [hscore u hopt.1.2.2.1 k.succ]
      exact hc k
  · intro B u hopt
    obtain ⟨huzero, p, hpresence, hf1⟩ := hthree B (scaledFeatureMap s⁻¹ u) (hpull B u hopt)
    refine ⟨?_, p, ?_, ?_⟩
    · rw [hlaw, actualPopulationSquaredLoss_scaledSourceLaw _ B u hopt.1.2.2.1 s hs,
        huzero, mul_zero]
    · rw [hlaw]
      have h := presence_ae_positive_scaling (mesoscaleCountablePopulationLaw δ θ H η)
        (scaledFeatureMap s⁻¹ u) (measurable_scaledFeatureMap s⁻¹ hopt.1.2.2.1) s hs p hpresence
      simpa only [scaledFeatureMap_inverse_right s hs.ne'] using h
    · intro j
      rw [hscore u hopt.1.2.2.1 j]
      exact hf1 j
  · rw [hloss 3, hzero, mul_zero]
  · rw [hloss 3, hloss 2]
    exact ENNReal.mul_lt_mul_right hfactor ENNReal.ofReal_ne_top h32
  · rw [hloss 2, hloss 1]
    exact ENNReal.mul_lt_mul_right hfactor ENNReal.ofReal_ne_top h21

end PKG26AtomicFeatures
