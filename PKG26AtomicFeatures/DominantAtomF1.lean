import PKG26AtomicFeatures.FeatureF1Supremum
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Feature scores controlled by two dominant atoms

Two correctly classified atoms with total mass at least `1-t` leave at most
`t` classification error. If a coordinate vanishes at an atom of mass at
least `(1-t)/2`, its positive predictions occupy at most `(1+t)/2` of the
population. These statements concern actual prediction events and do not
assume any F1 score or optimizing threshold.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped symmDiff

theorem probability_event_le_of_missing_atom
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (a : Ω)
    (ha : a ∉ E) (w : ℝ) (hmass : w ≤ μ.real {a}) :
    μ.real E ≤ 1 - w := by
  have hsub : E ⊆ ({a} : Set Ω)ᶜ := by
    intro x hx hxa
    exact ha ((Set.mem_singleton_iff.mp hxa) ▸ hx)
  have hle := measureReal_mono (μ := μ) hsub
  rw [measureReal_compl (measurableSet_singleton a), probReal_univ] at hle
  linarith

theorem probability_event_le_of_missing_two_atoms
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (a b : Ω)
    (hab : a ≠ b) (ha : a ∉ E) (hb : b ∉ E)
    (t : ℝ) (hmass : 1 - t ≤ μ.real {a} + μ.real {b}) :
    μ.real E ≤ t := by
  have hsub : E ⊆ (({a} : Set Ω) ∪ {b})ᶜ := by
    intro x hx hxunion
    rcases hxunion with hxa | hxb
    · exact ha ((Set.mem_singleton_iff.mp hxa) ▸ hx)
    · exact hb ((Set.mem_singleton_iff.mp hxb) ▸ hx)
  have hle := measureReal_mono (μ := μ) hsub
  rw [measureReal_compl ((measurableSet_singleton a).union (measurableSet_singleton b)),
    probReal_univ, measureReal_union (by simpa using hab) (measurableSet_singleton b)] at hle
  linarith

/-- A balanced truth label has F1 at least `1-2t` when two dominant atoms
are correctly separated and their total probability is at least `1-t`. -/
theorem populationF1_ge_of_two_dominant_atoms
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (truth prediction : Set Ω)
    (htruth : MeasurableSet truth) (hprediction : MeasurableSet prediction)
    (hbalanced : μ.real truth = 1 / 2)
    (a b : Ω) (ha : a ∈ truth ∩ prediction)
    (hb : b ∉ truth ∪ prediction)
    (t : ℝ) (ht : 0 ≤ t) (hmass : 1 - t ≤ μ.real {a} + μ.real {b}) :
    1 - 2 * t ≤ populationF1 μ truth prediction := by
  have hab : a ≠ b := by
    intro heq
    exact hb (Or.inl (heq ▸ ha.1))
  apply populationF1_ge_of_error_le μ htruth hprediction
    (by rw [hbalanced]; norm_num) (by positivity)
  rw [hbalanced]
  have herror := probability_event_le_of_missing_two_atoms μ (truth ∆ prediction)
    a b hab (by simp [Set.mem_symmDiff, ha.1, ha.2])
    (by simp only [Set.mem_union, not_or] at hb; simp [Set.mem_symmDiff, hb.1, hb.2]) t hmass
  linarith

/-- If every learned coordinate misses a dominant atom, the always-present
parent's best single-coordinate score is bounded uniformly over thresholds. -/
theorem singleCoordinateF1Sup_parent_le_of_missing_atoms
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (truth : Set Ω)
    (code : Ω → Fin m → ℝ) (j : Fin m) (htruth : μ.real truth = 1)
    (t : ℝ) (ht : 0 ≤ t)
    (hmissing : ∀ k : Fin m, ∃ a : Ω, code a k = 0 ∧ (1 - t) / 2 ≤ μ.real {a}) :
    singleCoordinateF1Sup μ truth code ≤ 2 * (1 + t) / (3 + t) := by
  apply singleCoordinateF1Sup_le μ truth code j
  intro k threshold hthreshold
  obtain ⟨a, ha, hmass⟩ := hmissing k
  have hbound := probability_event_le_of_missing_atom μ {x | threshold < code x k}
    a (by simpa only [Set.mem_setOf_eq, ha] using not_lt.mpr hthreshold.le)
    ((1 - t) / 2) hmass
  have hscore := populationF1_parent_le_of_prediction_mass μ truth
    {x | threshold < code x k} htruth
    ((1 + t) / 2) (by positivity) (by linarith)
  have heq : 2 * ((1 + t) / 2) / (1 + (1 + t) / 2) = 2 * (1 + t) / (3 + t) := by
    field_simp
    <;> ring
  rwa [heq] at hscore

end PKG26AtomicFeatures
