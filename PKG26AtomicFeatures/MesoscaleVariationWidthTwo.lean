import PKG26AtomicFeatures.MesoscaleVariationRisk
import PKG26AtomicFeatures.MesoscaleSupportTieBreak

/-!
# Width-two recovery for arbitrary bounded coefficient variation

One reference-neighborhood margin works uniformly for every strictly
positive bounded probability variation law. Actual optimal encoders agree
with NNLS on the positive-mass dominant atoms. Their strict, distinct-ray
assignments imply the same child and parent F1 bounds under the actual
mixture, without density or topological-support assumptions.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

section Variation

variable (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν]

/-- The exact dominant mixture component gives a real-valued atom mass
bound, uniformly over the remaining probability variation law. -/
theorem mesoscalePopulationLaw_dominant_mass_real_withVariation (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (k : Fin 2) :
    (1 - θ) * (1 - δ) / 2 ≤
      (mesoscalePopulationLaw_withVariation ν δ θ H η).real {mesoscalePlaneEmbedding k mesoscaleDominantPair} := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure_withVariation ν δ θ H η hδ hδone hθ hθone
  have hnonneg : 0 ≤ (1 - θ) * (1 - δ) / 2 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hθone) (sub_nonneg.mpr hδone)) (by norm_num)
  have h := ENNReal.toReal_mono (measure_ne_top (mesoscalePopulationLaw_withVariation ν δ θ H η) _)
    (mesoscalePopulationLaw_dominant_mass_withVariation ν δ θ H η k)
  simpa only [ENNReal.toReal_ofReal hnonneg] using h

/-- Each dominant atom has the mass needed by the F1 argument, as a
consequence of the explicit nonnegative mixture weights. -/
theorem mesoscalePopulationLaw_dominant_mass_lower_withVariation (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (k : Fin 2) :
    (1 - (δ + θ)) / 2 ≤
      (mesoscalePopulationLaw_withVariation ν δ θ H η).real {mesoscalePlaneEmbedding k mesoscaleDominantPair} := by
  have hmass := mesoscalePopulationLaw_dominant_mass_real_withVariation ν δ θ H η hδ hδone hθ hθone k
  nlinarith [mul_nonneg hδ hθ]


/-- A positive coordinate on one dominant point and a zero on the other
already attain a threshold with the stated child F1 lower bound. -/
theorem mesoscale_child_F1_lower_of_dominant_assignment_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (u : FeatureVector 3 → FeatureVector 2) (hu : Measurable u)
    (k j : Fin 2)
    (hactive : 0 < u (mesoscalePlaneEmbedding k mesoscaleDominantPair) j)
    (hinactive : u (mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair) j = 0) :
    1 - 2 * (δ + θ) ≤
      singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z k.succ} u := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure_withVariation ν δ θ H η hδ hδone hθ hθone
  let t : ℝ := u (mesoscalePlaneEmbedding k mesoscaleDominantPair) j / 2
  have ht : 0 < t := div_pos hactive (by norm_num)
  have htactive : t < u (mesoscalePlaneEmbedding k mesoscaleDominantPair) j := by
    dsimp [t]
    linarith
  have htruth : (mesoscalePopulationLaw_withVariation ν δ θ H η).real {z | 0 < z k.succ} = 1 / 2 := by
    rw [mesoscalePopulationLaw_prevalence_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη]
    simp only [Fin.succ_ne_zero, ↓reduceIte]
  have hmass : 1 - (δ + θ) ≤
      (mesoscalePopulationLaw_withVariation ν δ θ H η).real {mesoscalePlaneEmbedding k mesoscaleDominantPair} +
      (mesoscalePopulationLaw_withVariation ν δ θ H η).real
        {mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair} := by
    have h1 := mesoscalePopulationLaw_dominant_mass_lower_withVariation ν δ θ H η hδ hδone hθ hθone k
    have h2 := mesoscalePopulationLaw_dominant_mass_lower_withVariation ν δ θ H η hδ hδone hθ hθone (Fin.rev k)
    linarith
  have hscore := populationF1_ge_of_two_dominant_atoms (mesoscalePopulationLaw_withVariation ν δ θ H η)
    {z | 0 < z k.succ} {z | t < u z j}
    (measurableSet_lt measurable_const (measurable_pi_apply k.succ))
    (measurableSet_lt measurable_const ((measurable_pi_apply j).comp hu)) htruth
    (mesoscalePlaneEmbedding k mesoscaleDominantPair)
    (mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair)
    (show mesoscalePlaneEmbedding k mesoscaleDominantPair ∈
      {z | 0 < z k.succ} ∩ {z | t < u z j} from
      ⟨by
        change 0 < mesoscalePlaneEmbedding k mesoscaleDominantPair k.succ
        rw [(mesoscaleDominantPair_child_values k).1]
        norm_num, htactive⟩)
    (show mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair ∉
      {z | 0 < z k.succ} ∪ {z | t < u z j} from by
        simp only [Set.mem_union, Set.mem_setOf_eq, (mesoscaleDominantPair_child_values k).2,
          hinactive, lt_self_iff_false, false_or]
        exact not_lt.mpr ht.le)
    (δ + θ) (add_nonneg hδ hθ) hmass
  exact hscore.trans (populationF1_le_singleCoordinateF1Sup
    (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z k.succ} u j t ht)


/-- If each learned coordinate misses the opposite dominant atom under
one permutation, no coordinate can achieve a larger parent F1. -/
theorem mesoscale_parent_F1_upper_of_dominant_assignment_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (u : FeatureVector 3 → FeatureVector 2) (p : Equiv.Perm (Fin 2))
    (hinactive : ∀ k : Fin 2,
      u (mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair) (p k) = 0) :
    singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z 0} u ≤
      2 * (1 + (δ + θ)) / (3 + (δ + θ)) := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure_withVariation ν δ θ H η hδ hδone hθ hθone
  apply singleCoordinateF1Sup_parent_le_of_missing_atoms
    (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z 0} u 0
  · simpa using mesoscalePopulationLaw_prevalence_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη 0
  · exact add_nonneg hδ hθ
  · intro j
    refine ⟨mesoscalePlaneEmbedding (Fin.rev (p.symm j)) mesoscaleDominantPair, ?_,
      mesoscalePopulationLaw_dominant_mass_lower_withVariation ν δ θ H η hδ hδone hθ hθone _⟩
    simpa only [p.apply_symm_apply] using hinactive (p.symm j)


/-- The width-two F1 table follows from the actual dominant atom-code
pattern under one learned-coordinate permutation. Both child lower bounds
and the parent upper bound use probabilities derived from the mixture. -/
theorem mesoscale_F1_table_of_dominant_pattern_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (u : FeatureVector 3 → FeatureVector 2) (hu : Measurable u)
    (hpattern : ∃ p : Equiv.Perm (Fin 2), ∀ k : Fin 2,
      0 < u (mesoscalePlaneEmbedding k mesoscaleDominantPair) (p k) ∧
      u (mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair) (p k) = 0) :
    (∀ k : Fin 2, 1 - 2 * (δ + θ) ≤
      singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z k.succ} u) ∧
    singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z 0} u ≤
      2 * (1 + (δ + θ)) / (3 + (δ + θ)) ∧
    2 * (1 + (δ + θ)) / (3 + (δ + θ)) ≤ 2 / 3 + (δ + θ) := by
  obtain ⟨p, hp⟩ := hpattern
  refine ⟨?_, ?_, mesoscale_parent_F1_bound_le δ θ hδ hθ⟩
  · intro k
    exact mesoscale_child_F1_lower_of_dominant_assignment_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη
      u hu k (p k) (hp k).1 (hp k).2
  · exact mesoscale_parent_F1_upper_of_dominant_assignment_withVariation ν hν δ θ H η hδ hδone hθ hθone hH hη
      u p (fun k => (hp k).2)

/-- The actual finite-second-moment variation population has a primary
width-two optimum attaining the expected-support tie-break as well. -/
theorem exists_mesoscale_width_two_support_tie_optimum_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ) :
    ∃ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
      IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 ∧
      ∀ (C : Matrix (Fin 3) (Fin 2) ℝ) (v : FeatureVector 3 → FeatureVector 2),
        IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id C v (1 / 2) 1 2 →
        expectedCodeSupportSize (mesoscalePopulationLaw_withVariation ν δ θ H η) u ≤
          expectedCodeSupportSize (mesoscalePopulationLaw_withVariation ν δ θ H η) v :=
  exists_width_two_optimal_pair_minimizing_expected_support
    (mesoscalePopulationLaw_withVariation ν δ θ H η)
    (integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η)

/-- In particular, actual primary optima exist for the variation law. -/
theorem exists_mesoscale_width_two_optimal_pair_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) (δ θ H η : ℝ) :
    ∃ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
      IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
        (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 := by
  obtain ⟨B, u, hopt, _⟩ := exists_mesoscale_width_two_support_tie_optimum_withVariation ν hν δ θ H η
  exact ⟨B, u, hopt⟩

/-- Primary optimality determines each actual dominant atom's code,
since the atom has positive mass and NNLS is unique almost everywhere. -/
theorem mesoscale_width_two_optimal_pair_dominant_code_withVariation
    (hν : ∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1)
    (δ θ H η : ℝ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2)
    (hopt : IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
      (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2) (k : Fin 2) :
    u (mesoscalePlaneEmbedding k mesoscaleDominantPair) =
      mesoscaleReferenceCode B hopt.1.2.1 k.castSucc := by
  have hsecond := integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η
  have hae := hopt.ae_eq_nonnegativeLeastSquaresEncoder (by norm_num) (by norm_num)
    (by simpa only [Matrix.one_mulVec, id_eq] using (representationToEuclidean 3).continuous.measurable)
    (by simpa only [Matrix.one_mulVec, id_eq] using hsecond.lintegral_lt_top)
  have hmass := mesoscalePopulationLaw_dominant_mass_real_withVariation ν δ θ H η hδ hδone.le hθ hθone.le k
  have hpos : 0 < (mesoscalePopulationLaw_withVariation ν δ θ H η).real
      {mesoscalePlaneEmbedding k mesoscaleDominantPair} :=
    lt_of_lt_of_le (div_pos (mul_pos (sub_pos.mpr hθone) (sub_pos.mpr hδone)) (by norm_num)) hmass
  have hmassne : (mesoscalePopulationLaw_withVariation ν δ θ H η)
      {mesoscalePlaneEmbedding k mesoscaleDominantPair} ≠ 0 := by
    intro hz
    simp [Measure.real, hz] at hpos
  have heq := eq_at_positive_mass_atom_of_ae_eq hae
    (mesoscalePlaneEmbedding k mesoscaleDominantPair) hmassne
  simpa only [nonnegativeLeastSquaresEncoder, Function.comp_apply, Matrix.one_mulVec, id_eq,
    mesoscaleDominantPoint_eq_reference, mesoscaleReferenceCode] using heq

end Variation

/-- One positive margin controls the actual width-two F1 table uniformly
across all bounded positive probability variation laws. The same explicit
risk error is sufficient for every actual globally optimal feasible pair. -/
theorem exists_mesoscale_width_two_recovery_margin_withVariation :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (ν : Measure (EuclideanRepresentation 2)) [IsProbabilityMeasure ν],
      (∀ᵐ q ∂ν, ∀ j, 0 < q j ∧ q j ≤ 1) → ∀ δ θ H η : ℝ,
      0 ≤ δ → δ < 1 → 0 ≤ θ → θ < 1 → 0 < H → 0 < η →
      δ * H ^ 2 = (3 / 5) * (1 - δ) →
      δ * η * (2 * H + η) + 2 * θ ≤ κ * (1 - δ) →
      ∀ (B : Matrix (Fin 3) (Fin 2) ℝ) (u : FeatureVector 3 → FeatureVector 2),
        IsApproximatelyOptimalRecoveryPair (mesoscalePopulationLaw_withVariation ν δ θ H η)
          (1 : Matrix (Fin 3) (Fin 3) ℝ) id B u (1 / 2) 1 2 →
        (∀ k : Fin 2, 1 - 2 * (δ + θ) ≤
          singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z k.succ} u) ∧
        singleCoordinateF1Sup (mesoscalePopulationLaw_withVariation ν δ θ H η) {z | 0 < z 0} u ≤
          2 * (1 + (δ + θ)) / (3 + (δ + θ)) ∧
        2 * (1 + (δ + θ)) / (3 + (δ + θ)) ≤ 2 / 3 + (δ + θ) := by
  obtain ⟨κ, hκ, hlocal⟩ := exists_mesoscale_strict_pattern_perturbation_margin
  refine ⟨κ, hκ, ?_⟩
  intro ν hprob hν δ θ H η hδ hδone hθ hθone hH hη hcal herr B u hopt
  let μ := mesoscalePopulationLaw_withVariation ν δ θ H η
  let B' : MesoscaleReferenceDictionary := ⟨B, hopt.1.1, hopt.1.2.1⟩
  have hden : 0 < 1 - δ := sub_pos.mpr hδone
  let g : MesoscaleReferenceDictionary → ℝ := fun C => widthTwoPopulationRisk μ C / (1 - δ)
  have hclose (C : MesoscaleReferenceDictionary) :
      |g C - mesoscaleReferenceNNLSRisk C.1 C.2.2| ≤ κ := by
    have hpert := nnls_mesoscalePopulation_perturbation_withVariation ν hν C.1 (1 / 2) (by norm_num)
      (C.2.2.global_bound_of_width_le (by norm_num)) δ θ H η hδ hδone.le hθ hθone.le hH.le hη.le hcal
    change |widthTwoPopulationRisk μ C - (1 - δ) * mesoscaleReferenceNNLSRisk C.1 C.2.2| ≤ _ at hpert
    change |widthTwoPopulationRisk μ C / (1 - δ) - mesoscaleReferenceNNLSRisk C.1 C.2.2| ≤ κ
    have hid : widthTwoPopulationRisk μ C / (1 - δ) - mesoscaleReferenceNNLSRisk C.1 C.2.2 =
        (widthTwoPopulationRisk μ C - (1 - δ) * mesoscaleReferenceNNLSRisk C.1 C.2.2) / (1 - δ) := by
      rw [sub_div, mul_div_cancel_left₀ _ hden.ne']
    rw [hid, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    exact hpert.trans herr
  have hmin := actual_width_two_optimal_pair_minimizes_canonical_risk μ
    (integrable_mesoscalePopulation_secondMoment_withVariation ν hν δ θ H η) B u hopt
  have hpattern := hlocal g hclose B' (fun C => div_le_div_of_nonneg_right (hmin C) hden.le)
  obtain ⟨e, he⟩ := hpattern
  have hcode := mesoscale_width_two_optimal_pair_dominant_code_withVariation ν hν δ θ H η
    hδ hδone hθ hθone B u hopt
  apply mesoscale_F1_table_of_dominant_pattern_withVariation ν hν δ θ H η
    hδ hδone.le hθ hθone.le hH hη u hopt.1.2.2.1
  refine ⟨e, ?_⟩
  intro k
  refine ⟨?_, ?_⟩
  · rw [hcode]
    exact (he k).1
  · rw [hcode]
    apply (mesoscaleReferenceCode_isNNLS B hopt.1.2.1 (Fin.rev k).castSucc).eq_zero_of_columnResidual_neg
    apply (he (Fin.rev k)).2
    intro heq
    have hkr : k = Fin.rev k := e.injective heq
    fin_cases k <;> norm_num [Fin.rev] at hkr

end PKG26AtomicFeatures
