import PKG26AtomicFeatures.PositivePopulationScaling
import PKG26AtomicFeatures.MesoscaleWidthOneRecovery
import PKG26AtomicFeatures.MesoscaleSupportTieBreak

/-!
# Feature scores under a measurable population map

Pulling back the truth and code preserves every threshold score, its
single-coordinate supremum, and the actual expected support. Almost-everywhere
agreement is sufficient, so measurable extensions of codes on a countable
coefficient population preserve both optimization objectives and predictions.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal

/-- A measurable population map preserves the complete set of positive-threshold
F1 scores and hence its supremum, including when no threshold attains it. -/
theorem singleCoordinateF1Sup_map_measurable
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {m : ℕ}
    (μ : Measure Ω) (f : Ω → Ξ) (hf : Measurable f)
    (truth : Set Ξ) (ht : MeasurableSet truth)
    (u : Ξ → FeatureVector m) (hu : Measurable u) :
    singleCoordinateF1Sup (Measure.map f μ) truth u =
      singleCoordinateF1Sup μ (f ⁻¹' truth) (u ∘ f) := by
  unfold singleCoordinateF1Sup
  congr 1
  ext r
  simp only [mem_setOf_eq]
  have hscore (j : Fin m) (t : ℝ) :
      populationF1 (Measure.map f μ) truth {q | t < u q j} =
        populationF1 μ (f ⁻¹' truth) {x | t < (u ∘ f) x j} :=
    populationF1_map_measurable μ f hf truth _ ht
      (measurableSet_lt measurable_const ((measurable_pi_apply j).comp hu))
  simp_rw [hscore]

/-- Matching a coefficient-space code almost everywhere suffices to preserve
the source's feature F1, with no global measurability premise on another map
used to represent the source encoder. -/
theorem singleCoordinateF1Sup_eq_of_map_and_ae
    {Ω : Type*} [MeasurableSpace Ω] {M m : ℕ}
    (μ : Measure Ω) (ν : Measure (FeatureVector M))
    (z : Ω → FeatureVector M) (hz : Measurable z) (hmap : Measure.map z μ = ν)
    (u : FeatureVector M → FeatureVector m) (hu : Measurable u)
    (v : Ω → FeatureVector m) (hvu : v =ᵐ[μ] u ∘ z) (i : Fin M) :
    singleCoordinateF1Sup μ {x | 0 < z x i} v =
      singleCoordinateF1Sup ν {q | 0 < q i} u := by
  rw [singleCoordinateF1Sup_congr_code_ae μ _ hvu]
  rw [← hmap, singleCoordinateF1Sup_map_measurable μ z hz _
    (measurableSet_lt measurable_const (measurable_pi_apply i)) u hu]
  rfl

/-- Expected support is an actual nonnegative integral and is preserved by a
measurable pushforward; no finite-moment or probability premise is needed. -/
theorem expectedCodeSupportSize_map_measurable
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {m : ℕ}
    (μ : Measure Ω) (f : Ω → Ξ) (hf : Measurable f)
    (u : Ξ → FeatureVector m) (hu : Measurable u) :
    expectedCodeSupportSize (Measure.map f μ) u =
      expectedCodeSupportSize μ (u ∘ f) := by
  exact lintegral_map (measurable_nonzeroSupport_card u hu) hf

/-- A measurable coefficient population and almost-everywhere code agreement
preserve the sparsity objective used to select among reconstruction optima. -/
theorem expectedCodeSupportSize_eq_of_map_and_ae
    {Ω : Type*} [MeasurableSpace Ω] {M m : ℕ}
    (μ : Measure Ω) (ν : Measure (FeatureVector M))
    (z : Ω → FeatureVector M) (hz : Measurable z) (hmap : Measure.map z μ = ν)
    (u : FeatureVector M → FeatureVector m) (hu : Measurable u)
    (v : Ω → FeatureVector m) (hvu : v =ᵐ[μ] u ∘ z) :
    expectedCodeSupportSize μ v = expectedCodeSupportSize ν u := by
  rw [expectedCodeSupportSize_congr_ae μ hvu, ← hmap,
    expectedCodeSupportSize_map_measurable μ z hz u hu]

end PKG26AtomicFeatures
