import PKG26AtomicFeatures.HierarchicalTopologicalSupport
import PKG26AtomicFeatures.MesoscaleAllWidthTieBreak

/-!
# Attained exact recovery under hierarchical topological support

The true identity decoder is globally feasible after sanitizing codes outside
the nonnegative sparse domain. It attains zero risk for any two-sparse
nonnegative source law. Topological variation in both parent-child squares
then forces every width-three optimum to preserve all presence events. The
law need not have a density or any absolutely continuous component.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal

/-- A bounded-source assumption is unnecessary for exact identity decoding:
nonnegative sparse coefficients alone give an attained zero-loss pair. -/
theorem nonnegativeSparseIdentityEncoder_zero_loss_of_ae {d K : ℕ}
    (μ : Measure (FeatureVector d))
    (hsource : ∀ᵐ z ∂μ, (∀ j, 0 ≤ z j) ∧ (nonzeroSupport z).card ≤ K) :
    actualPopulationSquaredLoss μ (1 : Matrix (Fin d) (Fin d) ℝ) id 1
      (nonnegativeSparseIdentityEncoder d K) = 0 := by
  have heq : nonnegativeSparseIdentityEncoder d K =ᵐ[μ] id := by
    filter_upwards [hsource] with z hz
    exact if_pos hz
  unfold actualPopulationSquaredLoss
  calc
    _ = ∫⁻ _ : FeatureVector d, (0 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [heq] with z hz
      simp only [Matrix.one_mulVec, id_eq, hz, sub_self, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0), ENNReal.ofReal_zero]
    _ = 0 := by simp

theorem nonnegativeSparseIdentityEncoder_isOptimal_of_ae {d K : ℕ}
    (μ : Measure (FeatureVector d))
    (hsource : ∀ᵐ z ∂μ, (∀ j, 0 ≤ z j) ∧ (nonzeroSupport z).card ≤ K) :
    IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ) id 1
      (nonnegativeSparseIdentityEncoder d K) (1 / 2) 1 K := by
  refine ⟨nonnegativeSparseIdentityEncoder_feasible d K, ?_⟩
  intro B u _
  rw [nonnegativeSparseIdentityEncoder_zero_loss_of_ae μ hsource]
  exact bot_le

/-- Variation throughout both squares implies positive prevalence for each
of the three coordinates, even when the population is purely atomic. -/
theorem HasParentChildSquareSupport.prevalence_pos
    {μ : Measure (FeatureVector 3)} [IsProbabilityMeasure μ]
    (hsupport : HasParentChildSquareSupport μ) (j : Fin 3) :
    0 < μ.real {z | 0 < z j} := by
  have hopen : IsOpen {z : FeatureVector 3 | 0 < z j} :=
    isOpen_lt continuous_const (continuous_apply j)
  have hpoint : ∃ x ∈ μ.support, 0 < x j := by
    fin_cases j
    · refine ⟨hierarchicalParentChildCode 0 (1 / 2) (1 / 2),
        hsupport 0 _ _ (by constructor <;> norm_num) (by constructor <;> norm_num), ?_⟩
      norm_num [hierarchicalParentChildCode, Pi.single_apply, Fin.ext_iff]
    · refine ⟨hierarchicalParentChildCode 0 (1 / 2) (1 / 2),
        hsupport 0 _ _ (by constructor <;> norm_num) (by constructor <;> norm_num), ?_⟩
      norm_num [hierarchicalParentChildCode, Pi.single_apply, Fin.ext_iff]
    · refine ⟨hierarchicalParentChildCode 1 (1 / 2) (1 / 2),
        hsupport 1 _ _ (by constructor <;> norm_num) (by constructor <;> norm_num), ?_⟩
      norm_num [hierarchicalParentChildCode, Pi.single_apply, Fin.ext_iff]
  obtain ⟨x, hx, hxpos⟩ := hpoint
  have hmass := (Measure.mem_support_iff_forall x).mp hx _ (hopen.mem_nhds hxpos)
  exact ENNReal.toReal_pos hmass.ne' (measure_ne_top μ _)

/-- Every width-three optimum recovers all three hierarchical features under
topological variation. Actual zero loss and the common presence permutation
are conclusions, not optimizer certificates supplied as assumptions. -/
theorem hierarchical_width_three_optimal_recovery_of_support
    (μ : Measure (FeatureVector 3)) [IsProbabilityMeasure μ]
    (hsource : ∀ᵐ z ∂μ, (∀ j, 0 ≤ z j) ∧ (nonzeroSupport z).card ≤ 2 ∧
      (z 0 = 0 → z 1 = 0 ∧ z 2 = 0))
    (hsupport : HasParentChildSquareSupport μ)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hopt : IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin 3) (Fin 3) ℝ)
      id B u (1 / 2) 1 2) :
    actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 ∧
      ∃ p : Equiv.Perm (Fin 3),
        (∀ᵐ z ∂μ, ∀ j, 0 < u z (p j) ↔ 0 < z j) ∧
        (∀ j : Fin 3, singleCoordinateF1Sup μ {z | 0 < z j} u = 1) ∧
        expectedCodeSupportSize μ u = expectedCodeSupportSize μ id := by
  have hsparse : ∀ᵐ z ∂μ, (∀ j, 0 ≤ z j) ∧ (nonzeroSupport z).card ≤ 2 :=
    hsource.mono fun _ h => ⟨h.1, h.2.1⟩
  have hloss : actualPopulationSquaredLoss μ (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u = 0 := by
    have h := hopt.2 1 (nonnegativeSparseIdentityEncoder 3 2)
      (nonnegativeSparseIdentityEncoder_feasible 3 2)
    rw [nonnegativeSparseIdentityEncoder_zero_loss_of_ae μ hsparse, mul_zero] at h
    exact le_antisymm h bot_le
  obtain ⟨p, hp⟩ := exists_hierarchical_presence_permutation_of_feasible_zero_loss_and_support
    μ id u B (1 / 2) (by norm_num) measurable_id hopt.1
    (hsource.mono fun _ h => ⟨h.1, h.2.2⟩) (by simpa using hsupport) hloss
  refine ⟨hloss, p, hp, ?_, ?_⟩
  · intro j
    apply singleCoordinateF1Sup_eq_one_of_presence_ae μ {z | 0 < z j} u (p j)
    · filter_upwards [hp] with z hz
      exact propext (hz j).symm
    · exact hsupport.prevalence_pos j
  · apply lintegral_congr_ae
    filter_upwards [hp, hsource] with z hz hs
    congr 1
    exact support_card_eq_of_nonnegative_presence_permutation z (u z) hs.1
      (hopt.1.2.2.2.2 z) p hz

end PKG26AtomicFeatures
