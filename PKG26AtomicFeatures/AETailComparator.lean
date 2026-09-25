import PKG26AtomicFeatures.SparseCodeSanitation
import PKG26AtomicFeatures.SourceTruncationBounds

/-!
# Source truncation under almost-sure coefficient bounds

The population comparator depends only on the source coefficients almost
everywhere. A measurable truncated code can be made pointwise feasible on
its null exceptional set without changing its actual reconstruction loss.
Thus the optimization comparison does not require pointwise restrictions on
unobserved inputs.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The omitted-prevalence bound uses sparsity and unit-cube bounds only
almost everywhere under the actual population. -/
theorem actualPopulationSquaredLoss_source_truncation_le_ae
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (e : Fin m ↪ Fin M)
    (hA : HasUnitEuclideanColumns A) (hz : Measurable z)
    (hsparse : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card ≤ K)
    (hbound : ∀ᵐ x ∂μ, ∀ j, 0 ≤ z x j ∧ z x j ≤ 1) :
    actualPopulationSquaredLoss μ A z (A.submatrix id e) (fun x j => z x (e j)) ≤
      ENNReal.ofReal ((K : ℝ) * omittedFeaturePrevalence μ z (Finset.univ.image e)) := by
  classical
  have hevent (j : Fin M) : μ {x | z x j ≠ 0} = μ {x | 0 < z x j} := by
    apply measure_congr
    filter_upwards [hbound] with x hx
    change (z x j ≠ 0) = (0 < z x j)
    apply propext
    simpa only [ne_comm] using (hx j).1.lt_iff_ne.symm
  unfold actualPopulationSquaredLoss
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((K : ℝ) *
        ((nonzeroSupport (z x) \ Finset.univ.image e).card : ℝ)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hsparse, hbound] with x hs hx
      apply ENNReal.ofReal_le_ofReal
      exact source_truncation_squared_error_le_omitted_count A e (fun j => (hA j).le)
        (z x) hs (fun j => by rw [abs_of_nonneg (hx j).1]; exact (hx j).2)
    _ = ENNReal.ofReal (K : ℝ) *
        ∑ i ∈ Finset.univ \ Finset.univ.image e, μ {x | z x i ≠ 0} := by
      simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg K)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_omitted_support_card μ z hz]
    _ = _ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg K)]
      congr 1
      simp only [omittedFeaturePrevalence, featurePrevalence]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hevent, ofReal_measureReal]

/-- A genuine pointwise-feasible comparator is obtained by changing only
the null exceptional part of the source truncation. -/
theorem IsApproximatelyOptimalRecoveryPair.loss_le_omitted_prevalence_ae
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m)
    (e : Fin m ↪ Fin M) (γ C : ℝ)
    (hopt : IsApproximatelyOptimalRecoveryPair μ A z B u γ C K)
    (hA : HasUnitEuclideanColumns A) (hstable : SparseLowerStable A γ (2 * K))
    (hz : Measurable z)
    (hsparse : ∀ᵐ x ∂μ, (nonzeroSupport (z x)).card ≤ K)
    (hbound : ∀ᵐ x ∂μ, ∀ j, 0 ≤ z x j ∧ z x j ≤ 1)
    (hC : 0 ≤ C) :
    actualPopulationSquaredLoss μ A z B u ≤
      ENNReal.ofReal (C * K * omittedFeaturePrevalence μ z (Finset.univ.image e)) := by
  let trunc : Ω → FeatureVector m := fun x j => z x (e j)
  have htruncMeas : Measurable trunc :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply (e j)).comp hz)
  have htruncSparse : ∀ᵐ x ∂μ, (nonzeroSupport (trunc x)).card ≤ K := by
    filter_upwards [hsparse] with x hx
    exact (restrictSupportCode_card_le e (z x)).trans hx
  have htruncNonneg : ∀ᵐ x ∂μ, ∀ j, 0 ≤ trunc x j :=
    hbound.mono fun _ hx j => (hx (e j)).1
  obtain ⟨code, hcode, hcodeSparse, hcodeNonneg, heq⟩ :=
    exists_pointwise_feasible_code_ae_eq μ trunc htruncMeas htruncSparse htruncNonneg
  have hfeas : IsFeasibleRecoveryPair (A.submatrix id e) code γ K :=
    ⟨hA.subdictionary e, hstable.subdictionary e, hcode, hcodeSparse, hcodeNonneg⟩
  have hcompare := hopt.2 (A.submatrix id e) code hfeas
  rw [actualPopulationSquaredLoss_congr_code_ae μ A z (A.submatrix id e) code trunc heq]
    at hcompare
  have htrunc := actualPopulationSquaredLoss_source_truncation_le_ae μ A z e
    hA hz hsparse hbound
  apply hcompare.trans
  calc
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal
        ((K : ℝ) * omittedFeaturePrevalence μ z (Finset.univ.image e)) :=
      mul_le_mul_right htrunc _
    _ = _ := by rw [← ENNReal.ofReal_mul hC, mul_assoc]

end PKG26AtomicFeatures
