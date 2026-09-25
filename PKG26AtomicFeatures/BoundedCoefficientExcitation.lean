import PKG26AtomicFeatures.FiniteDimensionalCovering
import PKG26AtomicFeatures.PopulationRecovery
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Uniform avoidance of coefficient hyperplanes

For a bounded coefficient law, assigning zero mass to every homogeneous
hyperplane implies a small-slab estimate uniform over all unit directions.
The tolerance depends on the law and the requested probability, not on a
dictionary or its width. This is a probability ingredient for the qualitative
recovery proof, not a recovery theorem by itself.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A continuous scalar statistic with no atom at zero has arbitrarily small
probability in a sufficiently narrow closed slab. -/
theorem exists_positive_slab_threshold
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (f : E → ℝ) (hf : Continuous f)
    (hzero : μ {x | f x = 0} = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ μ {x | |f x| ≤ t} < ε := by
  let s : ℝ → Set E := fun t => {x | |f x| ≤ t}
  have hintersection : (⋂ t > (0 : ℝ), s t) = {x | f x = 0} := by
    ext x
    simp only [mem_iInter, mem_setOf_eq, s]
    constructor
    · intro h
      by_contra hne
      have hp : 0 < |f x| := abs_pos.mpr hne
      have hh := h (|f x| / 2) (half_pos hp)
      linarith
    · intro hx t ht
      simp only [hx, abs_zero]
      exact ht.le
  have hlim : Tendsto (fun t => μ (s t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_measure_biInter_gt (μ := μ) (a := (0 : ℝ))
      (s := s)
      (fun t _ => (isClosed_le hf.abs continuous_const).measurableSet.nullMeasurableSet)
      (fun _ _ _ ht _ hx => hx.trans ht)
      ⟨1, zero_lt_one, measure_ne_top μ _⟩
    simpa only [hintersection, hzero, Function.comp_def] using h
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (s t) < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hμt⟩ := (hpos.and hsmall).exists
  exact ⟨t, ht, hμt⟩

/-- Bounded laws that give zero mass to each homogeneous hyperplane have a
uniform small-slab threshold over the unit sphere. No density bound or
particular parametric distribution is assumed. -/
theorem exists_uniform_slab_threshold_of_bounded
    (K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin K))) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0 < R) (hbounded : ∀ᵐ z ∂μ, ‖z‖ ≤ R)
    (hzero : ∀ v : EuclideanSpace ℝ (Fin K), ‖v‖ = 1 →
      μ {z | inner ℝ v z = 0} = 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ v : EuclideanSpace ℝ (Fin K), ‖v‖ = 1 →
      μ {z | |inner ℝ v z| ≤ t} < ε := by
  classical
  let sphere : Set (EuclideanSpace ℝ (Fin K)) := Metric.sphere 0 1
  have hsphere (v : sphere) : ‖v.1‖ = 1 := by
    simpa only [sphere, Metric.mem_sphere, dist_zero_right] using v.2
  have hpoint (v : sphere) : ∃ t : ℝ, 0 < t ∧
      μ {z | |inner ℝ v.1 z| ≤ t} < ε :=
    exists_positive_slab_threshold μ (fun z => inner ℝ v.1 z)
      (continuous_const.inner continuous_id) (hzero v.1 (hsphere v)) hε
  choose radius hpositive hsmall using hpoint
  obtain ⟨F, hcover⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin K)) 1).elim_finite_subcover
      (fun v : sphere => Metric.ball v.1 (radius v / (2 * R)))
      (fun _ => Metric.isOpen_ball) (by
        intro v hv
        exact mem_iUnion.mpr ⟨⟨v, hv⟩, by
          simpa only [Metric.mem_ball, dist_self] using
            div_pos (hpositive ⟨v, hv⟩) (by positivity : 0 < 2 * R)⟩)
  by_cases hF : F.Nonempty
  · let t : ℝ := F.inf' hF (fun v => radius v / 2)
    have ht : 0 < t := (Finset.lt_inf'_iff hF).mpr (fun v _ => half_pos (hpositive v))
    refine ⟨t, ht, ?_⟩
    intro v hv
    have hvSphere : v ∈ sphere := by
      simpa only [sphere, Metric.mem_sphere, dist_zero_right] using hv
    obtain ⟨w, hw, hvw⟩ := mem_iUnion₂.mp (hcover hvSphere)
    have htw : t ≤ radius w / 2 := Finset.inf'_le _ hw
    have hdist : ‖w.1 - v‖ < radius w / (2 * R) := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hvw
    have hsubset : {z | |inner ℝ v z| ≤ t} ≤ᵐ[μ]
        {z | |inner ℝ w.1 z| ≤ radius w} := by
      filter_upwards [hbounded] with z hz
      intro hvz
      change |inner ℝ v z| ≤ t at hvz
      have hinner : |inner ℝ (w.1 - v) z| ≤ ‖w.1 - v‖ * R :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
      have hmul : ‖w.1 - v‖ * R < radius w / 2 := by
        calc
          ‖w.1 - v‖ * R < (radius w / (2 * R)) * R :=
            mul_lt_mul_of_pos_right hdist hR
          _ = radius w / 2 := by field_simp
      have htriangle : |inner ℝ w.1 z| ≤
          |inner ℝ (w.1 - v) z| + |inner ℝ v z| := by
        calc
          |inner ℝ w.1 z| = |inner ℝ (w.1 - v) z + inner ℝ v z| := by
            rw [inner_sub_left, sub_add_cancel]
          _ ≤ _ := abs_add_le _ _
      exact le_of_lt (lt_of_le_of_lt htriangle (by linarith))
    exact (measure_mono_ae hsubset).trans_lt (hsmall w)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro v hv
    have hvSphere : v ∈ sphere := by
      simpa only [sphere, Metric.mem_sphere, dist_zero_right] using hv
    have := hcover hvSphere
    simp [Finset.not_nonempty_iff_eq_empty.mp hF] at this

end PKG26AtomicFeatures
