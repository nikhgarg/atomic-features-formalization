import PKG26AtomicFeatures.FiniteScaleSupportRecovery

/-!
# A vanishing homogeneous modulus supplies fixed recovery scales

Choose an incidence slab scale and a coordinate-tail scale before the input
space and population. Each active coordinate is a unit homogeneous linear
functional in its support enumeration. Almost-sure nonnegativity converts its
lower-tail event into an absolute slab event. The chosen coefficient cutoff
is at most one; no monotonicity assumption on the modulus is used.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- An active source coordinate inherits the homogeneous modulus at any
positive slab scale above the requested cutoff. Source nonnegativity is
needed only almost everywhere under the actual conditional law. -/
theorem ModulusSparsePopulation.conditional_coordinate_tail_le_of_le
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    {μ : Measure Ω} [IsFiniteMeasure μ] {z : Ω → FeatureVector M} {ψ : ℝ → ℝ}
    (hpop : ModulusSparsePopulation (K := K) μ z ψ)
    (S : ExactSourceSupport M K) (hS : μ (sourceSupportEvent z S.1) ≠ 0)
    (i : Fin M) (hi : i ∈ S.1) (a s : ℝ) (hs : 0 < s) (has : a ≤ s) :
    (sourceSupportConditionalLaw μ z S.1).real {x | z x i ≤ a} ≤ ψ s := by
  classical
  haveI : IsFiniteMeasure (sourceSupportConditionalLaw μ z S.1) := by
    rw [sourceSupportConditionalLaw, if_neg hS]
    exact (μ.restrict (sourceSupportEvent z S.1)).smul_finite (ENNReal.inv_ne_top.mpr hS)
  have himage : i ∈ Finset.univ.image (sourceSupportEnumeration S) := by
    rwa [sourceSupportEnumeration_image]
  obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp himage
  let v : EuclideanRepresentation K := EuclideanSpace.single k (1 : ℝ)
  have hv : ‖v‖ = 1 := by simp [v]
  have hsubset : {x | z x (sourceSupportEnumeration S k) ≤ a} ≤ᵐ[
      sourceSupportConditionalLaw μ z S.1]
      {x | |inner ℝ v (sourceSupportCoordinates z S x)| ≤ s} := by
    filter_upwards [sourceSupportConditionalLaw_ae_of_ae μ z S.1
      hpop.ae_coefficient_bounds] with x hx
    intro hxa
    change |inner ℝ v (sourceSupportCoordinates z S x)| ≤ s
    have hinner : inner ℝ v (sourceSupportCoordinates z S x) =
        z x (sourceSupportEnumeration S k) := by
      simpa [v] using EuclideanSpace.inner_single_left k (1 : ℝ) (sourceSupportCoordinates z S x)
    rw [hinner, abs_of_nonneg (hx (sourceSupportEnumeration S k)).1]
    exact hxa.trans has
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)).trans
    (hpop.conditional_small_ball S hS s hs v hv)

/-- A common vanishing modulus provides one positive incidence scale and one
positive coordinate cutoff at most one, uniformly before all finite input
measures and source populations. The two slab scales are chosen separately;
the coordinate cutoff is reduced by event inclusion, not by monotonicity of
`ψ`. Probability laws are included as a special case of finite measures. -/
theorem exists_finite_scale_population_scales_of_modulus
    (K N : ℕ) (ψ : ℝ → ℝ) (ε : ℝ)
    (hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0)) (hε : 0 < ε) :
    ∃ s₀ a : ℝ, 0 < s₀ ∧ 0 < a ∧ a ≤ 1 ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
        (M : ℕ) (z : Ω → FeatureVector M),
        ModulusSparsePopulation (K := K) μ z ψ →
        FiniteScaleSparsePopulation (K := K) μ z N s₀ a ε := by
  have hscale (r : ℝ) (hr : 0 < r) : ∃ s : ℝ, 0 < s ∧ ψ s ≤ r := by
    have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ψ s < r := hψ.eventually (Iio_mem_nhds hr)
    have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
    obtain ⟨s, hs, hsr⟩ := (hpos.and hsmall).exists
    exact ⟨s, hs, hsr.le⟩
  obtain ⟨s₀, hs₀, hψ₀⟩ := hscale (1 / (4 * ((N : ℝ) + 1))) (by positivity)
  obtain ⟨sF, hsF, hψF⟩ := hscale ε hε
  let a := min sF 1
  have ha : 0 < a := lt_min hsF zero_lt_one
  refine ⟨s₀, a, hs₀, ha, min_le_right _ _, ?_⟩
  intro Ω _ μ _ M z hpop
  refine ⟨hpop.toBoundedSparsePopulation, ?_, ?_⟩
  · intro S hS v hv
    exact (hpop.conditional_small_ball S hS s₀ hs₀ v hv).trans hψ₀
  · intro S hS i hi
    exact (hpop.conditional_coordinate_tail_le_of_le S hS i hi a sF hsF
      (min_le_left _ _)).trans hψF

end PKG26AtomicFeatures
