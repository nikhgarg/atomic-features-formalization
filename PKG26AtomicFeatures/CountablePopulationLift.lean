import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Lifting countable populations through a measurable source map

A countably supported target law can be lifted by selecting one source
representative for each of its atoms. The chosen representatives need not
form a measurable section on the whole target space. No regularity of the
source measurable space, beyond measurability of the source map, is used.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal

/-- Arbitrary prescribed values on a countable set have a measurable
extension, with one fixed value away from that set. This also handles
representation encoders whose composition with the source is measurable
without assuming that the ambient encoder itself is measurable. -/
theorem exists_measurable_eq_on_countable
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace Z] {S : Set Y} (hS : S.Countable)
    (f : Y → Z) (z₀ : Z) :
    ∃ g : Y → Z, Measurable g ∧ Set.EqOn g f S ∧
      ∀ y ∉ S, g y = z₀ := by
  classical
  let g : Y → Z := fun y => if y ∈ S then f y else z₀
  refine ⟨g, ?_, ?_, ?_⟩
  · apply (measurable_const : Measurable (fun _ : Y => z₀)).measurable_of_countable_ne
    apply hS.mono
    intro y hy
    by_contra hnot
    exact hy (by simp [g, hnot])
  · intro y hy
    simp [g, hy]
  · intro y hy
    simp [g, hy]

/-- Decompose a measure concentrated on a countable set into its actual
singleton masses. The ambient target space need not itself be countable. -/
theorem sum_dirac_eq_of_ae_mem_countable
    {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (ν : Measure Y) {S : Set Y} (hS : S.Countable)
    (hae : ∀ᵐ y ∂ν, y ∈ S) :
    (Measure.sum fun y : S => ν {y.1} • Measure.dirac y.1) = ν := by
  classical
  letI : Countable S := hS.to_subtype
  have hunion : (⋃ y : S, ({y.1} : Set Y)) = S := by
    ext y
    simp
  have hdisj : Pairwise (fun a b : S => Disjoint ({a.1} : Set Y) {b.1}) := by
    intro a b hab
    exact Set.disjoint_singleton.mpr (Subtype.coe_ne_coe.mpr hab)
  calc
    _ = Measure.sum (fun y : S => ν.restrict {y.1}) := by
      simp only [Measure.restrict_singleton]
    _ = ν.restrict (⋃ y : S, ({y.1} : Set Y)) :=
      (Measure.restrict_iUnion hdisj (fun y => measurableSet_singleton y.1)).symm
    _ = ν := by rw [hunion, Measure.restrict_eq_self_of_ae_mem hae]

/-- Lift a target law concentrated on a specified countable subset of the
range. The source may be an arbitrary measurable space. -/
theorem exists_probability_lift_of_countable_subset_range
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (z : X → Y) (hz : Measurable z)
    {S : Set Y} (hS : S.Countable) (hae : ∀ᵐ y ∂ν, y ∈ S)
    (hrange : S ⊆ Set.range z) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ Measure.map z μ = ν := by
  classical
  choose r hr using (fun y : S => hrange y.2)
  let μ : Measure X := Measure.sum fun y : S => ν {y.1} • Measure.dirac (r y)
  have hmap : Measure.map z μ = ν := by
    change Measure.map z (Measure.sum fun y : S => ν {y.1} • Measure.dirac (r y)) = ν
    rw [Measure.map_sum hz.aemeasurable]
    simp_rw [Measure.map_smul, Measure.map_dirac' hz, hr]
    exact sum_dirac_eq_of_ae_mem_countable ν hS hae
  refine ⟨μ, ?_, hmap⟩
  constructor
  have hmass := congrArg (fun η : Measure Y => η Set.univ) hmap
  simpa only [Measure.map_apply hz MeasurableSet.univ, Set.preimage_univ,
    measure_univ] using hmass

/-- A countably supported probability law lifts whenever almost every
target point lies in the measurable source map's range. Surjectivity onto
the source sparse cube is one way to verify this range condition. -/
theorem exists_probability_lift_of_countably_supported
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (z : X → Y) (hz : Measurable z)
    (hcount : ∃ S : Set Y, S.Countable ∧ ∀ᵐ y ∂ν, y ∈ S)
    (hrange : ∀ᵐ y ∂ν, y ∈ Set.range z) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ Measure.map z μ = ν := by
  obtain ⟨S, hS, hae⟩ := hcount
  exact exists_probability_lift_of_countable_subset_range ν z hz
    (hS.mono Set.inter_subset_left) (hae.and hrange) Set.inter_subset_right

end PKG26AtomicFeatures
