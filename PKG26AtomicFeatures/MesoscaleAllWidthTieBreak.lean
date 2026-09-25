import PKG26AtomicFeatures.MesoscaleSupportTieBreak
import PKG26AtomicFeatures.MesoscaleScaledConstruction

/-!
# Expected-support tie-break attainment at all three mesoscale widths

Every width-one primary optimum has one active coordinate almost surely.
Every width-three primary optimum has exactly the source's two active
coordinates, through its common presence permutation. Their expected-support
tie-breaks are therefore constant across primary optima. Together with compact
secondary attainment at width two, this gives selected optima at all three
widths for the same primitive scaled population.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

/-- Almost-sure constant support cardinality gives its literal expected
value under a probability law. -/
theorem expectedCodeSupportSize_eq_of_ae_card
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → FeatureVector m) (n : ℕ)
    (hcard : ∀ᵐ x ∂μ, (nonzeroSupport (u x)).card = n) :
    expectedCodeSupportSize μ u = n := by
  calc
    _ = ∫⁻ _ : Ω, (n : ℝ≥0∞) ∂μ := lintegral_congr_ae
      (hcard.mono (fun _ h => congrArg (fun n : ℕ => (n : ℝ≥0∞)) h))
    _ = _ := by simp

/-- Common nonzero scaling preserves the exact expected number of active
coordinates, using the actual pushforward law and transported encoder. -/
theorem expectedCodeSupportSize_positive_scaling {d m : ℕ}
    (μ : Measure (FeatureVector d)) (u : FeatureVector d → FeatureVector m)
    (hu : Measurable u) (s : ℝ) (hs : s ≠ 0) :
    expectedCodeSupportSize (scaledSourceLaw s μ) (scaledFeatureMap s u) =
      expectedCodeSupportSize μ u := by
  unfold expectedCodeSupportSize scaledSourceLaw
  rw [lintegral_map (measurable_nonzeroSupport_card _ (measurable_scaledFeatureMap s hu))
    (measurable_const_smul s)]
  simp_rw [scaledFeatureMap_apply_smul s hs, nonzeroSupport_smul_eq s hs]

/-- The inverse-transport identity applies to any actual encoder on the
scaled population. -/
theorem expectedCodeSupportSize_scaledSourceLaw {d m : ℕ}
    (μ : Measure (FeatureVector d)) (u : FeatureVector d → FeatureVector m)
    (hu : Measurable u) (s : ℝ) (hs : s ≠ 0) :
    expectedCodeSupportSize (scaledSourceLaw s μ) u =
      expectedCodeSupportSize μ (scaledFeatureMap s⁻¹ u) := by
  simpa only [scaledFeatureMap_inverse_right s hs] using
    expectedCodeSupportSize_positive_scaling μ (scaledFeatureMap s⁻¹ u)
      (measurable_scaledFeatureMap s⁻¹ hu) s hs

/-- Every actual width-one optimum is positive almost surely, so its
expected support is exactly one. -/
theorem mesoscale_width_one_optimum_expected_support
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    expectedCodeSupportSize (mesoscalePopulationLaw δ θ H η) u = 1 := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone.le hθ hθone.le
  have hcode := (mesoscale_width_one_optimal_pair_leading_code δ θ H η
    hδ hδone hθ hθone hH hη B u hopt).2
  have hw := symmetricFamilyLeadingDirection_pos
    (mesoscaleParentSecondMoment δ θ H η) (mesoscaleParentChildMoment δ θ H η)
    (mesoscaleChildSecondMoment δ θ H η)
    (mesoscaleParentChildMoment_pos δ θ H η hδ hδone hθ hθone hH hη)
  have hpositive := mesoscale_inner_pos_ae δ θ H η hH hη _ hw
  have hcard : ∀ᵐ z ∂mesoscalePopulationLaw δ θ H η, (nonzeroSupport (u z)).card = 1 := by
    filter_upwards [hcode, hpositive] with z hz hp
    have hu : 0 < u z 0 := by rwa [hz]
    have hs : nonzeroSupport (u z) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact (mem_nonzeroSupport_iff _ _).mpr hu.ne'
    simp [hs]
  simpa only [Nat.cast_one] using expectedCodeSupportSize_eq_of_ae_card
    (mesoscalePopulationLaw δ θ H η) u 1 hcard

/-- A presence-preserving coordinate permutation preserves support
cardinality for nonnegative codes. -/
theorem support_card_eq_of_nonnegative_presence_permutation {m : ℕ}
    (z u : FeatureVector m) (hz : ∀ j, 0 ≤ z j) (hu : ∀ j, 0 ≤ u j)
    (p : Equiv.Perm (Fin m)) (hp : ∀ j, 0 < u (p j) ↔ 0 < z j) :
    (nonzeroSupport u).card = (nonzeroSupport z).card := by
  symm
  apply Finset.card_equiv p
  intro j
  simp only [mem_nonzeroSupport_iff]
  rw [ne_iff_lt_or_gt, ne_iff_lt_or_gt]
  have hz' : ¬ z j < 0 := not_lt.mpr (hz j)
  have hu' : ¬ u (p j) < 0 := not_lt.mpr (hu (p j))
  simpa only [hz', hu', false_or] using (hp j).symm

/-- Every actual width-three primary optimum recovers one common presence
permutation, hence uses exactly two coefficients almost surely. -/
theorem mesoscale_width_three_optimum_expected_support
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    expectedCodeSupportSize (mesoscalePopulationLaw δ θ H η) u = 2 := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ.le hθone
  obtain ⟨_, p, hpresence, _⟩ := mesoscalePopulationLaw_width_three_optimum_recovery
    δ θ H η hδ hδone hθ hθone hH hη B u hopt
  apply expectedCodeSupportSize_eq_of_ae_card _ u 2
  filter_upwards [hpresence, mesoscalePopulationLaw_ae_nonneg δ θ H η hH hη,
    mesoscalePopulationLaw_ae_support_card δ θ H η hH hη] with z hp hz hcard
  rw [support_card_eq_of_nonnegative_presence_permutation z (u z) hz (hopt.1.2.2.2.2 z) p hp]
  exact hcard

/-- At width one, positive scaling preserves the constant expected support
of every actual primary optimum. -/
theorem mesoscale_scaled_width_one_optimum_expected_support
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hH : 1 ≤ H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 1) ℝ) (u : FeatureVector 3 → FeatureVector 1)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscaleScaledPopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    expectedCodeSupportSize (mesoscaleScaledPopulationLaw δ θ H η) u = 1 := by
  have hs : 0 < (1 / (H + 1) : ℝ) := by positivity
  rw [mesoscaleScaledPopulationLaw_eq_scaledSourceLaw] at hopt ⊢
  rw [expectedCodeSupportSize_scaledSourceLaw _ u hopt.1.2.2.1 _ hs.ne']
  apply mesoscale_width_one_optimum_expected_support δ θ H η hδ hδone hθ hθone
    (by linarith) hη B
  exact (isApproximatelyOptimalRecoveryPair_scaledSourceLaw_iff _ B u (1 / 2) 1 _ hs).mp hopt

/-- At width three, every actual primary optimum has expected support two
also under the literal scaled source law. -/
theorem mesoscale_scaled_width_three_optimum_expected_support
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hH : 1 ≤ H) (hη : 0 < η)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (u : FeatureVector 3 → FeatureVector 3)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscaleScaledPopulationLaw δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) :
    expectedCodeSupportSize (mesoscaleScaledPopulationLaw δ θ H η) u = 2 := by
  have hs : 0 < (1 / (H + 1) : ℝ) := by positivity
  rw [mesoscaleScaledPopulationLaw_eq_scaledSourceLaw] at hopt ⊢
  rw [expectedCodeSupportSize_scaledSourceLaw _ u hopt.1.2.2.1 _ hs.ne']
  apply mesoscale_width_three_optimum_expected_support δ θ H η hδ hδone hθ hθone
    (by linarith) hη B
  exact (isApproximatelyOptimalRecoveryPair_scaledSourceLaw_iff _ B u (1 / 2) 1 _ hs).mp hopt

/-- The same actual scaled population admits expected-support-minimizing
primary optima at every one of the three learned widths. The secondary
comparison quantifies over every feasible actual primary-optimal pair. -/
theorem exists_mesoscale_scaled_all_width_support_tie_optima
    (δ θ H η : ℝ) (hδ : 0 < δ) (hδone : δ < 1) (hθ : 0 < θ) (hθone : θ < 1)
    (hH : 1 ≤ H) (hη : 0 < η) :
    ∀ m : ℕ, 1 ≤ m → m ≤ 3 →
      ∃ (B : Matrix (Fin 3) (Fin m) ℝ) (u : FeatureVector 3 → FeatureVector m),
        IsApproximatelyOptimalRecoveryPair (mesoscaleScaledPopulationLaw δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 ∧
        ∀ (C : Matrix (Fin 3) (Fin m) ℝ) (v : FeatureVector 3 → FeatureVector m),
          IsApproximatelyOptimalRecoveryPair (mesoscaleScaledPopulationLaw δ θ H η)
            (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v (1 / 2) 1 2 →
          expectedCodeSupportSize (mesoscaleScaledPopulationLaw δ θ H η) u ≤
            expectedCodeSupportSize (mesoscaleScaledPopulationLaw δ θ H η) v := by
  have hs : 0 < (1 / (H + 1) : ℝ) := by positivity
  intro m hm hmthree
  interval_cases m
  · obtain ⟨B, u, hopt⟩ := exists_mesoscale_width_one_optimal_pair δ θ H η
      hδ.le hδone hθ.le hθone (by linarith) hη
    have hscaled : IsApproximatelyOptimalRecoveryPair (mesoscaleScaledPopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B (scaledFeatureMap (1 / (H + 1)) u) (1 / 2) 1 2 := by
      rw [mesoscaleScaledPopulationLaw_eq_scaledSourceLaw]
      exact hopt.positive_scaling _ hs
    refine ⟨B, _, hscaled, ?_⟩
    intro C v hv
    rw [mesoscale_scaled_width_one_optimum_expected_support δ θ H η
        hδ.le hδone hθ.le hθone hH hη B _ hscaled,
      mesoscale_scaled_width_one_optimum_expected_support δ θ H η
        hδ.le hδone hθ.le hθone hH hη C v hv]
  · obtain ⟨B, u, hopt, _, htie⟩ := exists_mesoscale_scaled_width_two_support_tie_optimum
      δ θ H η hδ.le hδone.le hθ.le hθone.le
    exact ⟨B, u, hopt, htie⟩
  · obtain ⟨B, u, hopt⟩ := exists_mesoscale_width_three_optimal_pair δ θ H η (by linarith) hη
    have hscaled : IsApproximatelyOptimalRecoveryPair (mesoscaleScaledPopulationLaw δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B (scaledFeatureMap (1 / (H + 1)) u) (1 / 2) 1 2 := by
      rw [mesoscaleScaledPopulationLaw_eq_scaledSourceLaw]
      exact hopt.positive_scaling _ hs
    refine ⟨B, _, hscaled, ?_⟩
    intro C v hv
    rw [mesoscale_scaled_width_three_optimum_expected_support δ θ H η
        hδ.le hδone.le hθ hθone.le hH hη B _ hscaled,
      mesoscale_scaled_width_three_optimum_expected_support δ θ H η
        hδ.le hδone.le hθ hθone.le hH hη C v hv]

end PKG26AtomicFeatures
