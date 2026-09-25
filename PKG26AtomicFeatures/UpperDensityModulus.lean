import PKG26AtomicFeatures.ModulusSupportRecovery
import PKG26AtomicFeatures.DensityBoundedCoefficients

/-!
# Upper density bounds supply a common small-ball modulus

The cube's worst homogeneous slab probability tends to zero with the slab
width. Measure domination by a fixed multiple of the cube law multiplies
this same modulus. No lower density bound is needed.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The largest homogeneous slab probability of the reference cube law.
Nonunit directions contribute zero to keep the index type nonempty. -/
noncomputable def uniformCubeSlabModulus (K : ℕ) (s : ℝ) : ℝ := by
  classical
  exact ⨆ v : EuclideanRepresentation K,
    if ‖v‖ = 1 then (uniformCubeCoefficientLaw K).real {z | |inner ℝ v z| ≤ s} else 0

private theorem cubeSlab_bddAbove (K : ℕ) (s : ℝ) :
    BddAbove (Set.range (fun v : EuclideanRepresentation K =>
      if ‖v‖ = 1 then (uniformCubeCoefficientLaw K).real {z | |inner ℝ v z| ≤ s} else 0)) := by
  classical
  refine ⟨1, ?_⟩
  rintro _ ⟨v, rfl⟩
  dsimp only
  split_ifs
  · simpa using (measureReal_mono (Set.subset_univ _) :
      (uniformCubeCoefficientLaw K).real {z | |inner ℝ v z| ≤ s} ≤
        (uniformCubeCoefficientLaw K).real Set.univ)
  · norm_num

theorem uniformCubeSlabModulus_nonneg (K : ℕ) (s : ℝ) :
    0 ≤ uniformCubeSlabModulus K s := by
  classical
  unfold uniformCubeSlabModulus
  exact le_ciSup_of_le (cubeSlab_bddAbove K s) 0 (by simp)

/-- Each unit direction is bounded by the same cube modulus. -/
theorem uniformCube_slab_le_modulus (K : ℕ) (s : ℝ)
    (v : EuclideanRepresentation K) (hv : ‖v‖ = 1) :
    (uniformCubeCoefficientLaw K).real {z | |inner ℝ v z| ≤ s} ≤ uniformCubeSlabModulus K s := by
  classical
  unfold uniformCubeSlabModulus
  simpa only [if_pos hv] using le_ciSup (cubeSlab_bddAbove K s) v

theorem uniformCubeSlabModulus_mono (K : ℕ) : Monotone (uniformCubeSlabModulus K) := by
  classical
  intro s t hst
  unfold uniformCubeSlabModulus
  apply ciSup_le
  intro v
  split_ifs with hv
  · exact (measureReal_mono (fun _ hz => hz.trans hst)).trans
      (uniformCube_slab_le_modulus K t v hv)
  · exact uniformCubeSlabModulus_nonneg K t

/-- Uniform small-slab control on the compact direction sphere makes the
cube modulus vanish as the positive slab width tends to zero. -/
theorem uniformCubeSlabModulus_tendsto_zero (K : ℕ) :
    Tendsto (uniformCubeSlabModulus K) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun s => hb.trans_le (uniformCubeSlabModulus_nonneg K s)
  · intro b hb
    obtain ⟨t, ht, hslab⟩ := densityBoundedCube_uniform_slab_threshold K 1 (b / 2)
      (by norm_num) (by positivity)
    have htbound : uniformCubeSlabModulus K t ≤ b / 2 := by
      classical
      unfold uniformCubeSlabModulus
      apply ciSup_le
      intro v
      split_ifs with hv
      · exact hslab (uniformCubeCoefficientLaw K) (by simp) v hv
      · positivity
    have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < t :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ht)
    filter_upwards [hsmall] with s hs
    exact ((uniformCubeSlabModulus_mono K hs.le).trans htbound).trans_lt (by linarith)

/-- A common upper density bound gives the same vanishing modulus on every
coefficient law, whether or not that density is bounded below. -/
theorem upper_density_slab_le_modulus
    (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (ν : Measure (EuclideanRepresentation K))
    (hν : ν ≤ ENNReal.ofReal C • uniformCubeCoefficientLaw K)
    (s : ℝ) (v : EuclideanRepresentation K) (hv : ‖v‖ = 1) :
    ν.real {z | |inner ℝ v z| ≤ s} ≤ C * uniformCubeSlabModulus K s := by
  have hle := hν {z | |inner ℝ v z| ≤ s}
  rw [Measure.smul_apply, smul_eq_mul] at hle
  have hfinite : ENNReal.ofReal C * uniformCubeCoefficientLaw K {z | |inner ℝ v z| ≤ s} ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono hfinite hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_left (uniformCube_slab_le_modulus K s v hv) hC)

/-- The upper-density modulus is uniform over all source populations and
depends only on the common density bound and fixed sparsity. -/
theorem BoundedSparsePopulation.modulus_of_conditional_upper_density
    {Ω : Type*} [MeasurableSpace Ω] {M K : ℕ}
    {μ : Measure Ω} {z : Ω → FeatureVector M}
    (hpop : BoundedSparsePopulation (K := K) μ z) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
      Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) ≤
        ENNReal.ofReal C • uniformCubeCoefficientLaw K) :
    ModulusSparsePopulation (K := K) μ z (fun s => C * uniformCubeSlabModulus K s) := by
  refine ⟨hpop, ?_⟩
  intro S hS s _hs v hv
  have h := upper_density_slab_le_modulus K C hC _ (hdom S hS) s v hv
  have hmeas : MeasurableSet {z : EuclideanRepresentation K | |inner ℝ v z| ≤ s} :=
    measurableSet_le (continuous_const.inner continuous_id).abs.measurable measurable_const
  simpa only [Measure.real, Measure.map_apply
    (measurable_sourceSupportCoordinates z hpop.measurable S) hmeas] using h

/-- Multiplying the cube modulus by a fixed finite upper density bound
preserves its limit. -/
theorem upperDensitySlabModulus_tendsto_zero (K : ℕ) (C : ℝ) :
    Tendsto (fun s => C * uniformCubeSlabModulus K s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [mul_zero] using tendsto_const_nhds.mul (uniformCubeSlabModulus_tendsto_zero K)

end PKG26AtomicFeatures
