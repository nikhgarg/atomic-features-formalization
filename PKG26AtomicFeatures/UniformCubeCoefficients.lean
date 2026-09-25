import PKG26AtomicFeatures.BoundedCoefficientExcitation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The independent uniform coefficient law in the September 18 draft

The coordinate law is Lebesgue measure restricted to the unit cube, hence
the product of independent uniform unit-interval laws. It is transported to
Euclidean coordinates before applying norm and inner-product estimates.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal

/-- Product unit cube in coordinate space. Endpoints have probability zero,
so closed intervals describe the draft's independent `Unif(0,1)` law. -/
def coefficientUnitCube (K : ℕ) : Set (FeatureVector K) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

/-- Independent uniform coefficients before transport to Euclidean space. -/
noncomputable def uniformCubeCoordinateLaw (K : ℕ) : Measure (FeatureVector K) :=
  volume.restrict (coefficientUnitCube K)

theorem measurableSet_coefficientUnitCube (K : ℕ) :
    MeasurableSet (coefficientUnitCube K) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)

theorem volume_coefficientUnitCube (K : ℕ) : volume (coefficientUnitCube K) = 1 := by
  rw [coefficientUnitCube, volume_pi, Measure.pi_pi]
  norm_num

instance uniformCubeCoordinateLaw_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (uniformCubeCoordinateLaw K) := by
  constructor
  simpa only [uniformCubeCoordinateLaw, Measure.restrict_apply_univ] using
    volume_coefficientUnitCube K

/-- The cube law used for Euclidean coefficient estimates. -/
noncomputable def uniformCubeCoefficientLaw (K : ℕ) :
    Measure (EuclideanRepresentation K) :=
  Measure.map (representationToEuclidean K) (uniformCubeCoordinateLaw K)

instance uniformCubeCoefficientLaw_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (uniformCubeCoefficientLaw K) := by
  unfold uniformCubeCoefficientLaw
  exact Measure.isProbabilityMeasure_map
    (representationToEuclidean K).continuous.measurable.aemeasurable

/-- The coordinate-space definition is exactly the finite product of
uniform unit-interval measures, not merely a law with uniform marginals. -/
theorem uniformCubeCoordinateLaw_eq_pi (K : ℕ) :
    uniformCubeCoordinateLaw K =
      Measure.pi (fun _ : Fin K => (volume : Measure ℝ).restrict (Set.Icc 0 1)) := by
  simp only [uniformCubeCoordinateLaw, coefficientUnitCube, volume_pi]
  exact Measure.restrict_pi_pi _ _

theorem uniformCubeCoefficientLaw_ae_norm_le (K : ℕ) :
    ∀ᵐ z ∂uniformCubeCoefficientLaw K, ‖z‖ ≤ (K : ℝ) + 1 := by
  apply (ae_map_iff (representationToEuclidean K).continuous.measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  filter_upwards [ae_restrict_mem (measurableSet_coefficientUnitCube K)] with z hz
  have hz' : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    simpa only [coefficientUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Icc] using hz
  have hsq : ‖representationToEuclidean K z‖ ^ 2 ≤ (K : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin K, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        change (z i) ^ 2 ≤ 1
        nlinarith [(hz' i).1, (hz' i).2]
      _ = K := by simp
  nlinarith [norm_nonneg (representationToEuclidean K z), (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

/-- A nonzero coefficient functional vanishes on a strict linear subspace,
which has zero Lebesgue measure. Restriction to the cube preserves nullity. -/
theorem uniformCubeCoefficientLaw_hyperplane_null
    (K : ℕ) (v : EuclideanRepresentation K) (hv : ‖v‖ = 1) :
    uniformCubeCoefficientLaw K {z | inner ℝ v z = 0} = 0 := by
  let L : FeatureVector K →ₗ[ℝ] ℝ :=
    (innerSL ℝ v).toLinearMap.comp (representationToEuclidean K).toLinearMap
  have hproper : LinearMap.ker L ≠ ⊤ := by
    intro htop
    have hmem : (representationToEuclidean K).symm v ∈ LinearMap.ker L := by
      rw [htop]
      trivial
    have hzero : inner ℝ v v = 0 := by
      simpa [LinearMap.mem_ker, L] using hmem
    rw [real_inner_self_eq_norm_sq, hv] at hzero
    norm_num at hzero
  have hnull : (volume : Measure (FeatureVector K)) (LinearMap.ker L) = 0 :=
    Measure.addHaar_submodule volume (LinearMap.ker L) hproper
  have hmeas : MeasurableSet {z : EuclideanRepresentation K | inner ℝ v z = 0} :=
    measurableSet_eq_fun ((continuous_const.inner continuous_id :
      Continuous fun z : EuclideanRepresentation K => inner ℝ v z).measurable) measurable_const
  rw [uniformCubeCoefficientLaw, Measure.map_apply
    (representationToEuclidean K).continuous.measurable
    hmeas]
  have hbound : uniformCubeCoordinateLaw K (LinearMap.ker L) ≤
      (volume : Measure (FeatureVector K)) (LinearMap.ker L) :=
    Measure.restrict_apply_le _ _
  exact le_antisymm (hbound.trans hnull.le) (zero_le _)

/-- The draft's coefficient law satisfies the uniform small-slab estimate
needed by both subspace incidence and thresholded feature recovery. -/
theorem uniformCubeCoefficientLaw_uniform_slab_threshold
    (K : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
      uniformCubeCoefficientLaw K {z | |inner ℝ v z| ≤ t} < ε := by
  exact exists_uniform_slab_threshold_of_bounded K (uniformCubeCoefficientLaw K)
    (by positivity : (0 : ℝ) < (K : ℝ) + 1)
    (uniformCubeCoefficientLaw_ae_norm_le K)
    (uniformCubeCoefficientLaw_hyperplane_null K) hε

end PKG26AtomicFeatures
