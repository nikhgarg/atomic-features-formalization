import PKG26AtomicFeatures.MesoscalePopulationModel
import PKG26AtomicFeatures.DominantAtomF1

/-!
# Width-two feature scores from the actual dominant-atom assignments

The explicit mesoscale population puts at least `(1-δ-θ)/2` at each
of its two dominant points. A common permutation assigning the two points
to different positive learned coordinates gives high child F1 and bounds
every positive-threshold prediction of the always-present parent.
Only the actual atom-code assignments are assumed, not event probabilities
or feature scores.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal Matrix

/-- Each dominant atom has the mass needed by the F1 argument, as a
consequence of the explicit nonnegative mixture weights. -/
theorem mesoscalePopulationLaw_dominant_mass_lower (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (k : Fin 2) :
    (1 - (δ + θ)) / 2 ≤
      (mesoscalePopulationLaw δ θ H η).real {mesoscalePlaneEmbedding k mesoscaleDominantPair} := by
  have hmass := mesoscalePopulationLaw_dominant_mass_real δ θ H η hδ hδone hθ hθone k
  nlinarith [mul_nonneg hδ hθ]

/-- Each dominant point has coefficient one in its own child, while the
other dominant point has zero in that child. -/
theorem mesoscaleDominantPair_child_values (k : Fin 2) :
    mesoscalePlaneEmbedding k mesoscaleDominantPair k.succ = 1 ∧
      mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair k.succ = 0 := by
  fin_cases k <;>
    norm_num [mesoscalePlaneEmbedding, mesoscaleDominantPair, representationToEuclidean,
      Matrix.cons_val_two, Fin.rev, Fin.succ]

/-- A positive coordinate on one dominant point and a zero on the other
already attain a threshold with the stated child F1 lower bound. -/
theorem mesoscale_child_F1_lower_of_dominant_assignment
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (u : FeatureVector 3 → FeatureVector 2) (hu : Measurable u)
    (k j : Fin 2)
    (hactive : 0 < u (mesoscalePlaneEmbedding k mesoscaleDominantPair) j)
    (hinactive : u (mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair) j = 0) :
    1 - 2 * (δ + θ) ≤
      singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z k.succ} u := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  let t : ℝ := u (mesoscalePlaneEmbedding k mesoscaleDominantPair) j / 2
  have ht : 0 < t := div_pos hactive (by norm_num)
  have htactive : t < u (mesoscalePlaneEmbedding k mesoscaleDominantPair) j := by
    dsimp [t]
    linarith
  have htruth : (mesoscalePopulationLaw δ θ H η).real {z | 0 < z k.succ} = 1 / 2 := by
    rw [mesoscalePopulationLaw_prevalence δ θ H η hδ hδone hθ hθone hH hη]
    simp only [Fin.succ_ne_zero, ↓reduceIte]
  have hmass : 1 - (δ + θ) ≤
      (mesoscalePopulationLaw δ θ H η).real {mesoscalePlaneEmbedding k mesoscaleDominantPair} +
      (mesoscalePopulationLaw δ θ H η).real
        {mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair} := by
    have h1 := mesoscalePopulationLaw_dominant_mass_lower δ θ H η hδ hδone hθ hθone k
    have h2 := mesoscalePopulationLaw_dominant_mass_lower δ θ H η hδ hδone hθ hθone (Fin.rev k)
    linarith
  have hscore := populationF1_ge_of_two_dominant_atoms (mesoscalePopulationLaw δ θ H η)
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
    (mesoscalePopulationLaw δ θ H η) {z | 0 < z k.succ} u j t ht)

/-- If each learned coordinate misses the opposite dominant atom under
one permutation, no coordinate can achieve a larger parent F1. -/
theorem mesoscale_parent_F1_upper_of_dominant_assignment
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (u : FeatureVector 3 → FeatureVector 2) (p : Equiv.Perm (Fin 2))
    (hinactive : ∀ k : Fin 2,
      u (mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair) (p k) = 0) :
    singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u ≤
      2 * (1 + (δ + θ)) / (3 + (δ + θ)) := by
  letI := mesoscalePopulationLaw_isProbabilityMeasure δ θ H η hδ hδone hθ hθone
  apply singleCoordinateF1Sup_parent_le_of_missing_atoms
    (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u 0
  · simpa using mesoscalePopulationLaw_prevalence δ θ H η hδ hδone hθ hθone hH hη 0
  · exact add_nonneg hδ hθ
  · intro j
    refine ⟨mesoscalePlaneEmbedding (Fin.rev (p.symm j)) mesoscaleDominantPair, ?_,
      mesoscalePopulationLaw_dominant_mass_lower δ θ H η hδ hδone hθ hθone _⟩
    simpa only [p.apply_symm_apply] using hinactive (p.symm j)

/-- The rational parent bound is at most the simpler table expression. -/
theorem mesoscale_parent_F1_bound_le (δ θ : ℝ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) :
    2 * (1 + (δ + θ)) / (3 + (δ + θ)) ≤ 2 / 3 + (δ + θ) := by
  rw [div_le_iff₀ (by linarith : 0 < 3 + (δ + θ))]
  nlinarith [sq_nonneg (δ + θ)]

/-- The width-two F1 table follows from the actual dominant atom-code
pattern under one learned-coordinate permutation. Both child lower bounds
and the parent upper bound use probabilities derived from the mixture. -/
theorem mesoscale_F1_table_of_dominant_pattern
    (δ θ H η : ℝ)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hH : 0 < H) (hη : 0 < η)
    (u : FeatureVector 3 → FeatureVector 2) (hu : Measurable u)
    (hpattern : ∃ p : Equiv.Perm (Fin 2), ∀ k : Fin 2,
      0 < u (mesoscalePlaneEmbedding k mesoscaleDominantPair) (p k) ∧
      u (mesoscalePlaneEmbedding (Fin.rev k) mesoscaleDominantPair) (p k) = 0) :
    (∀ k : Fin 2, 1 - 2 * (δ + θ) ≤
      singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z k.succ} u) ∧
    singleCoordinateF1Sup (mesoscalePopulationLaw δ θ H η) {z | 0 < z 0} u ≤
      2 * (1 + (δ + θ)) / (3 + (δ + θ)) ∧
    2 * (1 + (δ + θ)) / (3 + (δ + θ)) ≤ 2 / 3 + (δ + θ) := by
  obtain ⟨p, hp⟩ := hpattern
  refine ⟨?_, ?_, mesoscale_parent_F1_bound_le δ θ hδ hθ⟩
  · intro k
    exact mesoscale_child_F1_lower_of_dominant_assignment δ θ H η hδ hδone hθ hθone hH hη
      u hu k (p k) (hp k).1 (hp k).2
  · exact mesoscale_parent_F1_upper_of_dominant_assignment δ θ H η hδ hδone hθ hθone hH hη
      u p (fun k => (hp k).2)

end PKG26AtomicFeatures
