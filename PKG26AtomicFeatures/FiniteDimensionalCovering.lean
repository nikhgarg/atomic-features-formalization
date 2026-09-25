import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

namespace PKG26AtomicFeatures

/-- Choosing one point of `E` in each ball of radius `r / 2` that meets `E`
turns an external finite cover into an internal `r`-net without increasing
the number of centers. No closedness of `E` is needed. -/
theorem exists_internal_net_of_finite_cover
    {X : Type*} [PseudoMetricSpace X] (E : Set X) (centers : Finset X)
    (r : ℝ)
    (hcover : ∀ x ∈ E, ∃ c ∈ centers, dist x c < r / 2) :
    ∃ F : Finset X, (↑F : Set X) ⊆ E ∧ F.card ≤ centers.card ∧
      ∀ x ∈ E, ∃ y ∈ F, dist x y < r := by
  classical
  let hits := centers.filter fun c => ∃ x ∈ E, dist x c < r / 2
  have hrep (c : hits) : ∃ x : X, x ∈ E ∧ dist x c.1 < r / 2 :=
    (Finset.mem_filter.mp c.2).2
  choose rep hrep using hrep
  refine ⟨hits.attach.image rep, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hrep c).1
  · calc
      (hits.attach.image rep).card ≤ hits.attach.card := Finset.card_image_le
      _ = hits.card := Finset.card_attach
      _ ≤ centers.card := Finset.card_filter_le _ _
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := hcover x hx
    have hchits : c ∈ hits := Finset.mem_filter.mpr ⟨hc, x, hx, hxc⟩
    let c' : hits := ⟨c, hchits⟩
    refine ⟨rep c', Finset.mem_image.mpr ⟨c', Finset.mem_attach _ _, rfl⟩, ?_⟩
    have hcy : dist c (rep c') < r / 2 := by
      simpa only [dist_comm] using (hrep c').2
    have htriangle := dist_triangle x c (rep c')
    linarith

/-- The unit ball in a fixed Euclidean dimension supplies a bound for
internal nets of all of its subsets. The bound is chosen before the subset. -/
theorem exists_uniform_euclidean_internal_net_bound (q : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∀ E : Set (EuclideanSpace ℝ (Fin q)),
      E ⊆ Metric.closedBall 0 1 →
      ∃ F : Finset (EuclideanSpace ℝ (Fin q)),
        (↑F : Set (EuclideanSpace ℝ (Fin q))) ⊆ E ∧ F.card ≤ N ∧
        ∀ x ∈ E, ∃ y ∈ F, dist x y < r := by
  classical
  obtain ⟨centers, _, hfinite, hcover⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin q)) 1).finite_cover_balls
      (half_pos hr)
  refine ⟨hfinite.toFinset.card, fun E hE => ?_⟩
  apply exists_internal_net_of_finite_cover E hfinite.toFinset r
  intro x hx
  have hxc := hcover (hE hx)
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hxc
  obtain ⟨c, hc, hxc⟩ := hxc
  exact ⟨c, hfinite.mem_toFinset.mpr hc, hxc⟩

/-- Unit-ball subsets of subspaces of dimension at most `D` admit internal
`r`-nets whose cardinalities are uniformly bounded in the ambient dimension,
the subspace, and the subset. The subset need not be closed.

For each dimension at most `D`, compactness gives a bound in standard
Euclidean coordinates. Their finite maximum applies to every subspace after
transport through an orthonormal basis. -/
theorem exists_uniform_subspace_internal_net_bound (D : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∀ (d : ℕ) (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      Module.finrank ℝ U ≤ D → ∀ E : Set U,
      E ⊆ Metric.closedBall 0 1 →
      ∃ F : Finset U, (↑F : Set U) ⊆ E ∧ F.card ≤ N ∧
        ∀ x ∈ E, ∃ y ∈ F, dist x y < r := by
  classical
  choose bound hbound using fun q => exists_uniform_euclidean_internal_net_bound q r hr
  refine ⟨(Finset.range (D + 1)).sup bound, ?_⟩
  intro d U hdim E hE
  let e := (stdOrthonormalBasis ℝ U).repr
  have himage : e '' E ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, e.norm_map] using hE hx
  obtain ⟨F, hFE, hcard, hnet⟩ := hbound (Module.finrank ℝ U) (e '' E) himage
  refine ⟨F.image e.symm, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, rfl⟩ := hFE hz
    simpa only [e.symm_apply_apply] using hx
  · exact Finset.card_image_le.trans (hcard.trans
      (Finset.le_sup (f := bound) (Finset.mem_range.mpr (Nat.lt_succ_of_le hdim))))
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet (e x) (Set.mem_image_of_mem e hx)
    refine ⟨e.symm y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    have hdist := e.symm.dist_map (e x) y
    rw [e.symm_apply_apply] at hdist
    exact hdist.trans_lt hxy

end PKG26AtomicFeatures
