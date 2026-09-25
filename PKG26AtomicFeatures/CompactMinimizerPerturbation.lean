import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Uniform objective perturbations preserve neighborhoods of all minimizers

On a compact feasible set, an open neighborhood containing every reference
minimizer contains every minimizer of any sufficiently close objective.
The positive gap on the compact complement is derived by the extreme-value
theorem. Continuity of the perturbed objective is not needed for this
localization claim, and no unique minimizer is assumed.
-/

namespace PKG26AtomicFeatures

open Set

theorem exists_uniform_objective_perturbation_margin
    {E : Type*} [TopologicalSpace E] (K U : Set E) (f : E → ℝ)
    (hK : IsCompact K) (hne : K.Nonempty) (hf : ContinuousOn f K)
    (hU : IsOpen U)
    (hminU : ∀ x ∈ K, (∀ y ∈ K, f x ≤ f y) → x ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : E → ℝ),
      (∀ x ∈ K, |g x - f x| ≤ ε) →
      ∀ x ∈ K, (∀ y ∈ K, g x ≤ g y) → x ∈ U := by
  classical
  by_cases houtside : (K \ U).Nonempty
  · obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne hf
    obtain ⟨b, hb, hbmin⟩ := (hK.diff hU).exists_isMinOn houtside (hf.mono diff_subset)
    have hab : f a < f b := by
      apply lt_of_le_of_ne (hamin hb.1)
      intro heq
      have hbopt : ∀ y ∈ K, f b ≤ f y := by
        intro y hy
        rw [← heq]
        exact hamin hy
      exact hb.2 (hminU b hb.1 hbopt)
    refine ⟨(f b - f a) / 3, by linarith, ?_⟩
    intro g hclose x hx hxopt
    by_contra hxU
    have hb_le : f b ≤ f x := hbmin (show x ∈ K \ U from ⟨hx, hxU⟩)
    have hxa := hxopt a ha
    have hcx := abs_le.mp (hclose x hx)
    have hca := abs_le.mp (hclose a ha)
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro g hclose x hx hxopt
    by_contra hxU
    exact houtside ⟨x, hx, hxU⟩

end PKG26AtomicFeatures
