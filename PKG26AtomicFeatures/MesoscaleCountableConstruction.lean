import PKG26AtomicFeatures.MesoscaleCountableVariation
import PKG26AtomicFeatures.MesoscaleVariationWidthOne
import PKG26AtomicFeatures.MesoscaleVariationWidthTwo
import PKG26AtomicFeatures.HierarchicalSupportRecovery
import PKG26AtomicFeatures.MesoscaleVariationLossOrdering

/-!
# A countable mesoscale population with all three recovery regimes

One parameter tuple supplies a countably supported hierarchical population.
All actual primary optima obey the feature table. At each width an actual
primary optimum also minimizes the expected number of nonzero coordinates
among all primary optima. The population is chosen through its primitive
mixture parameters, with no optimizer or recovery conclusions as premises.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

theorem mesoscaleCountablePopulationLaw_ae_hierarchicalPresence
    (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscaleCountablePopulationLaw δ θ H η, MesoscaleHierarchicalPresence z :=
  mesoscalePopulationLaw_ae_hierarchicalPresence_withVariation _
    (denseCountableCubeCoefficientLaw_ae_pos_le_one 2) δ θ H η hH hη

theorem mesoscaleCountablePopulationLaw_ae_source
    (δ θ H η : ℝ) (hH : 0 < H) (hη : 0 < η) :
    ∀ᵐ z ∂mesoscaleCountablePopulationLaw δ θ H η,
      (∀ j, 0 ≤ z j) ∧ (nonzeroSupport z).card ≤ 2 ∧
      (z 0 = 0 → z 1 = 0 ∧ z 2 = 0) := by
  filter_upwards [mesoscalePopulationLaw_ae_nonneg_withVariation _
      (denseCountableCubeCoefficientLaw_ae_pos_le_one 2) δ θ H η hH hη,
    mesoscaleCountablePopulationLaw_ae_hierarchicalPresence δ θ H η hH hη] with z hn hh
  exact ⟨hn, hh.support_card.le, fun hz => (hh.1.ne' hz).elim⟩

/-- Every width-one primary optimum activates its only coordinate almost
surely, so the secondary support criterion is constant on the optimum set. -/
theorem mesoscaleCountable_width_one_optimum_expected_support
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) u = 1 := by
  let ν := denseCountableCubeCoefficientLaw 2
  have hν := denseCountableCubeCoefficientLaw_ae_pos_le_one 2
  letI := mesoscaleCountablePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone.le hθ hθone.le
  have hcode := (mesoscale_width_one_optimal_pair_leading_code_withVariation ν hν δ θ H η
    hδ hδone hθ hθone hH hη B u hopt).2
  have hw := symmetricFamilyLeadingDirection_pos
    (mesoscaleParentSecondMoment_withVariation ν δ θ H η)
    (mesoscaleParentChildMoment_withVariation ν δ θ H η)
    (mesoscaleChildSecondMoment_withVariation ν δ θ H η)
    (mesoscaleParentChildMoment_pos_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη)
  have hpositive := mesoscale_inner_pos_ae_withVariation ν hν δ θ H η hH hη _ hw
  suffices hcard : ∀ᵐ z ∂mesoscaleCountablePopulationLaw δ θ H η,
      (nonzeroSupport (u z)).card = 1 by
    simpa only [Nat.cast_one] using expectedCodeSupportSize_eq_of_ae_card
      (mesoscaleCountablePopulationLaw δ θ H η) u 1 hcard
  filter_upwards [hcode, hpositive] with z hz hp
  have hu : 0 < u z 0 := by rwa [hz]
  have hs : nonzeroSupport (u z) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (mem_nonzeroSupport_iff _ _).mpr hu.ne'
  simp [hs]

theorem exists_mesoscaleCountable_width_one_support_tie_optimum
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η) :
    ∃ (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1),
      IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 ∧
      ∀ (C : Matrix (Fin 3) (Fin 1) ℝ) (v : FeatureVector 3 → FeatureVector 1),
        IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v (1 / 2) 1 2 →
        expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) u ≤
          expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) v := by
  have hopt := mesoscale_leading_width_one_pair_optimal_withVariation _
    (denseCountableCubeCoefficientLaw_ae_pos_le_one 2) δ θ H η hδ hδone hθ hθone hH hη
  refine ⟨_, _, hopt, ?_⟩
  intro C v hv
  rw [mesoscaleCountable_width_one_optimum_expected_support δ θ H η
      hδ hδone hθ hθone hH hη _ _ hopt,
    mesoscaleCountable_width_one_optimum_expected_support δ θ H η
      hδ hδone hθ hθone hH hη C v hv]

theorem mesoscaleCountable_width_three_optimal_recovery
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    actualPopulationSquaredLoss (mesoscaleCountablePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 ∧
      ∃ p : Equiv.Perm (Fin 3),
        (∀ᵐ z ∂mesoscaleCountablePopulationLaw δ θ H η, ∀ j, 0 < u z (p j) ↔ 0 < z j) ∧
        (∀ j : Fin 3, singleCoordinateF1Sup (mesoscaleCountablePopulationLaw δ θ H η)
          {z | 0 < z j} u = 1) ∧
        expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) u =
          expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) id := by
  letI := mesoscaleCountablePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ.le hθone
  exact hierarchical_width_three_optimal_recovery_of_support _
    (mesoscaleCountablePopulationLaw_ae_source δ θ H η hH hη)
    (mesoscaleCountablePopulationLaw_hasParentChildSquareSupport δ θ H η hθ) B u hopt

theorem exists_mesoscaleCountable_width_three_support_tie_optimum
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η) :
    ∃ (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3),
      IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 ∧
      ∀ (C : Matrix (Fin 3) (Fin 3) ℝ) (v : FeatureVector 3 → FeatureVector 3),
        IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v (1 / 2) 1 2 →
        expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) u ≤
          expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) v := by
  have hopt := nonnegativeSparseIdentityEncoder_isOptimal_of_ae _
    ((mesoscaleCountablePopulationLaw_ae_source δ θ H η hH hη).mono fun _ h => ⟨h.1, h.2.1⟩)
  refine ⟨1, nonnegativeSparseIdentityEncoder 3 2, hopt, ?_⟩
  intro C v hv
  obtain ⟨_, _, _, _, hu⟩ := mesoscaleCountable_width_three_optimal_recovery δ θ H η
    hδ hδone hθ hθone hH hη _ _ hopt
  obtain ⟨_, _, _, _, hv⟩ := mesoscaleCountable_width_three_optimal_recovery δ θ H η
    hδ hδone hθ hθone hH hη C v hv
  rw [hu, hv]

/-- One countable population has the all-primary-optimum feature table and
attained primary and secondary optima at every width, with strictly ordered
actual optimal losses. The primitive parameters are chosen internally. -/
theorem exists_mesoscale_countable_unscaled_construction (ε : ℝ) (hε : 0 < ε) :
    ∃ δ θ H η : ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < θ ∧ θ < 1 ∧ 1 ≤ H ∧ 0 < η ∧ η ≤ 1 ∧
      δ + θ ≤ ε / 2 ∧ δ * H ^ 2 = (3 / 5) * (1 - δ) ∧
      IsProbabilityMeasure (mesoscaleCountablePopulationLaw δ θ H η) ∧
      (∃ S : Set (FeatureVector 3), S.Countable ∧
        ∀ᵐ z ∂mesoscaleCountablePopulationLaw δ θ H η, z ∈ S) ∧
      (∀ᵐ z ∂mesoscaleCountablePopulationLaw δ θ H η, MesoscaleHierarchicalPresence z) ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ 3 →
        ∃ (B : Matrix (Fin 3) (Fin m) ℝ) (u : FeatureVector 3 → FeatureVector m),
          IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
            (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 ∧
          ∀ (C : Matrix (Fin 3) (Fin m) ℝ) (v : FeatureVector 3 → FeatureVector m),
            IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
              (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v (1 / 2) 1 2 →
            expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) u ≤
              expectedCodeSupportSize (mesoscaleCountablePopulationLaw δ θ H η) v) ∧
      (∀ (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1),
        IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        singleCoordinateF1Sup (mesoscaleCountablePopulationLaw δ θ H η) {z | 0 < z 0} u = 1 ∧
          ∀ k : Fin 2, singleCoordinateF1Sup (mesoscaleCountablePopulationLaw δ θ H η)
            {z | 0 < z k.succ} u = 2 / 3) ∧
      (∀ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
        IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        singleCoordinateF1Sup (mesoscaleCountablePopulationLaw δ θ H η) {z | 0 < z 0} u ≤ 2 / 3 + ε ∧
          ∀ k : Fin 2, 1 - ε ≤ singleCoordinateF1Sup (mesoscaleCountablePopulationLaw δ θ H η)
            {z | 0 < z k.succ} u) ∧
      (∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3),
        IsApproximatelyOptimalRecoveryPair (mesoscaleCountablePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        actualPopulationSquaredLoss (mesoscaleCountablePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 ∧
        ∃ p : Equiv.Perm (Fin 3),
          (∀ᵐ z ∂mesoscaleCountablePopulationLaw δ θ H η, ∀ j, 0 < u z (p j) ↔ 0 < z j) ∧
          ∀ j : Fin 3, singleCoordinateF1Sup (mesoscaleCountablePopulationLaw δ θ H η) {z | 0 < z j} u = 1) ∧
      optimalRecoveryLoss (mesoscaleCountablePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 = 0 ∧
      optimalRecoveryLoss (mesoscaleCountablePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 3 <
        optimalRecoveryLoss (mesoscaleCountablePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 2 ∧
      optimalRecoveryLoss (mesoscaleCountablePopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 2 <
        optimalRecoveryLoss (mesoscaleCountablePopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id (1 / 2) 2 1 := by
  obtain ⟨κ, hκ, htwo⟩ := exists_mesoscale_width_two_recovery_margin_withVariation
  obtain ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, hbudget, hcal, hsmall, hgap⟩ :=
    exists_mesoscale_common_parameters ε κ hε hκ
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hν := denseCountableCubeCoefficientLaw_ae_pos_le_one 2
  obtain ⟨B₁, u₁, hopt₁, htie₁⟩ := exists_mesoscaleCountable_width_one_support_tie_optimum
    δ θ H η hδ.le hδone hθ.le hθone hHpos hη
  obtain ⟨B₂, u₂, hopt₂, htie₂⟩ :=
    exists_mesoscale_width_two_support_tie_optimum_withVariation _ hν δ θ H η
  obtain ⟨B₃, u₃, hopt₃, htie₃⟩ := exists_mesoscaleCountable_width_three_support_tie_optimum
    δ θ H η hδ.le hδone.le hθ hθone.le hHpos hη
  have hloss := mesoscale_optimalRecoveryLoss_strictly_ordered_withVariation _ hν δ θ H η
    hδ.le hδone hθ.le hθone hHpos hη hcal hgap
    (mesoscaleCountablePopulationLaw_hasParentChildSquareSupport δ θ H η hθ)
  refine ⟨δ, θ, H, η, hδ, hδone, hθ, hθone, hH, hη, hηone, hbudget, hcal,
    mesoscaleCountablePopulationLaw_isProbabilityMeasure δ θ H η hδ.le hδone.le hθ.le hθone.le,
    mesoscaleCountablePopulationLaw_countably_supported δ θ H η,
    mesoscaleCountablePopulationLaw_ae_hierarchicalPresence δ θ H η hHpos hη,
    ?_, ?_, ?_, ?_, hloss.1, hloss.2.1, hloss.2.2⟩
  · intro m hm hmthree
    interval_cases m
    · exact ⟨B₁, u₁, hopt₁, htie₁⟩
    · exact ⟨B₂, u₂, hopt₂, htie₂⟩
    · exact ⟨B₃, u₃, hopt₃, htie₃⟩
  · intro B u hopt
    exact mesoscale_width_one_optimal_pair_F1_withVariation _ hν δ θ H η
      hδ.le hδone hθ.le hθone hHpos hη B u hopt
  · intro B u hopt
    obtain ⟨hchild, hparent, hratio⟩ :=
      htwo _ hν δ θ H η hδ.le hδone hθ.le hθone hHpos hη hcal hsmall.le B u hopt
    refine ⟨(hparent.trans hratio).trans (by linarith), ?_⟩
    intro k
    exact (by linarith : 1 - ε ≤ 1 - 2 * (δ + θ)).trans (hchild k)
  · intro B u hopt
    obtain ⟨hz, p, hp, hf, _⟩ := mesoscaleCountable_width_three_optimal_recovery δ θ H η
      hδ.le hδone.le hθ hθone.le hHpos hη B u hopt
    exact ⟨hz, p, hp, hf⟩

end PKG26AtomicFeatures
