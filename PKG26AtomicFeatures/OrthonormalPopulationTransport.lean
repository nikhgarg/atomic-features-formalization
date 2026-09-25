import PKG26AtomicFeatures.OrthonormalDictionaryTransport
import PKG26AtomicFeatures.AmbientPopulationCompression
import PKG26AtomicFeatures.CountablePopulationLift
import PKG26AtomicFeatures.SparseCubeRetraction
import PKG26AtomicFeatures.MesoscaleSupportTieBreak
import PKG26AtomicFeatures.PopulationScoreTransport

/-!
# Orthonormal transport of countably supported populations

A representation encoder is only required to be measurable after composition
with the source. A countable coefficient population nevertheless admits a
measurable coefficient-space encoder with exactly the same population values.
Orthonormal synthesis then transports feasible dictionaries, losses, and
activation observables between the source and its coefficient population.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set Module
open scoped ENNReal Matrix

/-- A representation encoder has a measurable coefficient-space extension
on the actual countable population, with its feasibility and values preserved. -/
theorem exists_feasible_countable_code_extension
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    (μ : Measure X) (A : Matrix (Fin d) (Fin M) ℝ) (z : X → FeatureVector M)
    (hz : Measurable z) (g : RepresentationVector d → FeatureVector m)
    (B : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ)
    (hfeas : IsFeasibleRecoveryPair B (g ∘ fun x => A.mulVec (z x)) γ K)
    {S : Set (FeatureVector M)} (hS : S.Countable)
    (hae : ∀ᵐ q ∂Measure.map z μ, q ∈ S) (hrange : S ⊆ Set.range z) :
    ∃ u : FeatureVector M → FeatureVector m,
      IsFeasibleRecoveryPair B u γ K ∧
      Set.EqOn u (g ∘ A.mulVec) S ∧
      u ∘ z =ᵐ[μ] g ∘ (fun x => A.mulVec (z x)) := by
  obtain ⟨u, hu, heq, hzero⟩ := exists_measurable_eq_on_countable hS (g ∘ A.mulVec) 0
  refine ⟨u, ⟨hfeas.1, hfeas.2.1, hu, ?_, ?_⟩, heq, ?_⟩
  · intro q
    by_cases hq : q ∈ S
    · obtain ⟨x, rfl⟩ := hrange hq
      rw [heq hq]
      exact hfeas.2.2.2.1 x
    · simp [hzero q hq, nonzeroSupport]
  · intro q j
    by_cases hq : q ∈ S
    · obtain ⟨x, rfl⟩ := hrange hq
      rw [heq hq]
      exact hfeas.2.2.2.2 x j
    · simp [hzero q hq]
  · filter_upwards [ae_of_ae_map hz.aemeasurable hae] with x hx
    exact heq hx

/-- Actual expected loss commutes with a measurable source pushforward. -/
theorem actualPopulationSquaredLoss_map_source
    {X : Type*} [MeasurableSpace X] {d M m : ℕ}
    (μ : Measure X) (z : X → FeatureVector M) (hz : Measurable z)
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (u : FeatureVector M → FeatureVector m) (hu : Measurable u) :
    actualPopulationSquaredLoss (Measure.map z μ) A id B u =
      actualPopulationSquaredLoss μ A z B (u ∘ z) := by
  unfold actualPopulationSquaredLoss
  exact lintegral_map (measurable_euclideanSquaredResidual
    ((representationToEuclidean d).continuous.measurable.comp
      A.mulVecLin.continuous_of_finiteDimensional.measurable) B hu) hz

/-- A coefficient-space feasible pair lifts to an actual representation
encoder by recovering source coordinates with the matrix transpose. -/
theorem IsFeasibleRecoveryPair.orthonormal_lift
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : X → FeatureVector M) (hz : Measurable z)
    {C : Matrix (Fin M) (Fin m) ℝ} {u : FeatureVector M → FeatureVector m} {γ : ℝ}
    (hfeas : IsFeasibleRecoveryPair C u γ K) :
    IsFeasibleRecoveryPair (A * C)
      ((u ∘ A.transpose.mulVec) ∘ (fun x => A.mulVec (z x))) γ K := by
  have heq : (u ∘ A.transpose.mulVec) ∘ (fun x => A.mulVec (z x)) = u ∘ z := by
    funext x
    simp only [Function.comp_apply, orthonormalDictionary_transpose_left_inverse A hA]
  rw [heq]
  exact ⟨(orthonormalDictionary_lift_unit_iff A hA C).mpr hfeas.1,
    (orthonormalDictionary_lift_stable_iff A hA C γ).mpr hfeas.2.1,
    hfeas.2.2.1.comp hz, fun x => hfeas.2.2.2.1 (z x), fun x j => hfeas.2.2.2.2 (z x) j⟩

/-- The lifted representation encoder has exactly the original actual
coefficient-population loss, without any finiteness assumption. -/
theorem orthonormalRepresentation_loss_lift
    {X : Type*} [MeasurableSpace X] {d M m : ℕ}
    (μ : Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : X → FeatureVector M) (hz : Measurable z)
    (C : Matrix (Fin M) (Fin m) ℝ) (u : FeatureVector M → FeatureVector m)
    (hu : Measurable u) :
    actualPopulationSquaredLoss μ A z (A * C)
      ((u ∘ A.transpose.mulVec) ∘ (fun x => A.mulVec (z x))) =
      actualPopulationSquaredLoss (Measure.map z μ) (1 : Matrix (Fin M) (Fin M) ℝ) id C u := by
  have heq : (u ∘ A.transpose.mulVec) ∘ (fun x => A.mulVec (z x)) = u ∘ z := by
    funext x
    simp only [Function.comp_apply, orthonormalDictionary_transpose_left_inverse A hA]
  rw [heq, orthonormalDictionary_actual_loss_lift μ A hA]
  exact (actualPopulationSquaredLoss_map_source μ z hz 1 C u hu).symm

/-- Every finite-loss source pair admits a feasible coefficient-space pair
with unchanged population codes and no larger actual reconstruction loss.
The dictionary is obtained by Gram-preserving ambient compression. -/
theorem exists_coefficient_pair_of_representation_pair
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    (μ : Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : X → FeatureVector M) (hz : Measurable z)
    (hz2 : Integrable (fun x => ‖representationToEuclidean M (z x)‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m)
    (γ : ℝ) (hγ : 0 < γ) (hwidth : m ≤ M) (hstablewidth : m ≤ 2 * K)
    (hfeas : IsFeasibleRecoveryPair B (g ∘ fun x => A.mulVec (z x)) γ K)
    (hfinite : actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) < ⊤)
    {S : Set (FeatureVector M)} (hS : S.Countable)
    (hae : ∀ᵐ q ∂Measure.map z μ, q ∈ S) (hrange : S ⊆ Set.range z) :
    ∃ (C : Matrix (Fin M) (Fin m) ℝ) (u : FeatureVector M → FeatureVector m),
      IsFeasibleRecoveryPair C u γ K ∧
      Set.EqOn u (g ∘ A.mulVec) S ∧
      u ∘ z =ᵐ[μ] g ∘ (fun x => A.mulVec (z x)) ∧
      actualPopulationSquaredLoss (Measure.map z μ) (1 : Matrix (Fin M) (Fin M) ℝ) id C u ≤
        actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) := by
  obtain ⟨u, hufeas, hueq, huae⟩ :=
    exists_feasible_countable_code_extension μ A z hz g B γ hfeas hS hae hrange
  have hf : Measurable (fun x => representationToEuclidean d (A.mulVec (z x))) :=
    (representationToEuclidean d).continuous.measurable.comp
      (A.mulVecLin.continuous_of_finiteDimensional.measurable.comp hz)
  have hf2 : Integrable (fun x => ‖representationToEuclidean d (A.mulVec (z x))‖ ^ 2) μ := by
    simpa only [orthonormalDictionary_synthesis_norm A hA] using hz2
  obtain ⟨B', hB'range, hB'unit, hB'stable, _, hcomp⟩ :=
    exists_unit_stable_population_compression_of_finite_loss μ _ _ hf hfeas.2.2.1 hf2
      (LinearMap.range (Matrix.toEuclideanLin A))
      (by simpa only [orthonormalDictionary_range_finrank A hA] using hwidth)
      (Filter.Eventually.of_forall fun x => ⟨representationToEuclidean M (z x), rfl⟩)
      B γ hγ hfeas.1 hfeas.2.1 hstablewidth hfinite
  let C := A.transpose * B'
  have hBC : A * C = B' := orthonormalDictionary_lift_transpose_eq A hA B' hB'range
  have hCfeas : IsFeasibleRecoveryPair C u γ K := by
    refine ⟨(orthonormalDictionary_lift_unit_iff A hA C).mp ?_,
      (orthonormalDictionary_lift_stable_iff A hA C γ).mp ?_, hufeas.2.2⟩
    · simpa only [hBC] using hB'unit
    · simpa only [hBC] using hB'stable
  refine ⟨C, u, hCfeas, hueq, huae, ?_⟩
  calc
    _ = actualPopulationSquaredLoss μ (1 : Matrix (Fin M) (Fin M) ℝ) z C (u ∘ z) :=
      actualPopulationSquaredLoss_map_source μ z hz 1 C u hufeas.2.2.1
    _ = actualPopulationSquaredLoss μ A z B' (u ∘ z) := by
      rw [← hBC, orthonormalDictionary_actual_loss_lift μ A hA]
    _ = actualPopulationSquaredLoss μ A z B' (g ∘ fun x => A.mulVec (z x)) :=
      actualPopulationSquaredLoss_congr_ae μ A B' Filter.EventuallyEq.rfl huae
    _ ≤ _ := hcomp

/-- A finite-loss representation optimum compresses to an actual optimum
of the coefficient population. The same measurable extension preserves all
learned population values, not merely the optimal value. -/
theorem exists_coefficient_optimum_of_representation_optimum
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    (μ : Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : X → FeatureVector M) (hz : Measurable z)
    (hz2 : Integrable (fun x => ‖representationToEuclidean M (z x)‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m)
    (γ : ℝ) (hγ : 0 < γ) (hwidth : m ≤ M) (hstablewidth : m ≤ 2 * K)
    (hopt : IsOptimalRepresentationPair μ A z (fun x => A.mulVec (z x)) B g γ K)
    (hfinite : actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) < ⊤)
    {S : Set (FeatureVector M)} (hS : S.Countable)
    (hae : ∀ᵐ q ∂Measure.map z μ, q ∈ S) (hrange : S ⊆ Set.range z) :
    ∃ (C : Matrix (Fin M) (Fin m) ℝ) (u : FeatureVector M → FeatureVector m),
      IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
        (1 : Matrix (Fin M) (Fin M) ℝ) id C u γ 1 K ∧
      Set.EqOn u (g ∘ A.mulVec) S ∧
      u ∘ z =ᵐ[μ] g ∘ (fun x => A.mulVec (z x)) ∧
      actualPopulationSquaredLoss (Measure.map z μ) (1 : Matrix (Fin M) (Fin M) ℝ) id C u =
        actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) := by
  obtain ⟨C, u, hC, hueq, huae, hle⟩ := exists_coefficient_pair_of_representation_pair
    μ A hA z hz hz2 B g γ hγ hwidth hstablewidth hopt.1 hfinite hS hae hrange
  have hmin (D : Matrix (Fin M) (Fin m) ℝ) (v : FeatureVector M → FeatureVector m)
      (hv : IsFeasibleRecoveryPair D v γ K) :
      actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) ≤
        actualPopulationSquaredLoss (Measure.map z μ) (1 : Matrix (Fin M) (Fin M) ℝ) id D v := by
    rw [← orthonormalRepresentation_loss_lift μ A hA z hz D v hv.2.2.1]
    exact hopt.2 (A * D) (v ∘ A.transpose.mulVec) (hv.orthonormal_lift A hA z hz)
  refine ⟨C, u, ⟨hC, ?_⟩, hueq, huae, le_antisymm hle (hmin C u hC)⟩
  intro D v hv
  simpa only [ENNReal.ofReal_one, one_mul] using hle.trans (hmin D v hv)

/-- Every actual canonical optimum lifts to a representation optimum.
Finite-loss ambient competitors are compressed; infinite-loss competitors
satisfy the comparison automatically. -/
theorem IsApproximatelyOptimalRecoveryPair.orthonormal_representation_lift
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    (μ : Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : X → FeatureVector M) (hz : Measurable z)
    (hz2 : Integrable (fun x => ‖representationToEuclidean M (z x)‖ ^ 2) μ)
    {C : Matrix (Fin M) (Fin m) ℝ} {u : FeatureVector M → FeatureVector m}
    {γ : ℝ} (hγ : 0 < γ) (hwidth : m ≤ M) (hstablewidth : m ≤ 2 * K)
    (hopt : IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
      (1 : Matrix (Fin M) (Fin M) ℝ) id C u γ 1 K)
    {S : Set (FeatureVector M)} (hS : S.Countable)
    (hae : ∀ᵐ q ∂Measure.map z μ, q ∈ S) (hrange : S ⊆ Set.range z) :
    IsOptimalRepresentationPair μ A z (fun x => A.mulVec (z x))
      (A * C) (u ∘ A.transpose.mulVec) γ K := by
  refine ⟨hopt.1.orthonormal_lift A hA z hz, ?_⟩
  intro B g hfeas
  by_cases hfinite : actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) < ⊤
  · obtain ⟨D, v, hv, _, _, hle⟩ := exists_coefficient_pair_of_representation_pair
      μ A hA z hz hz2 B g γ hγ hwidth hstablewidth hfeas hfinite hS hae hrange
    rw [orthonormalRepresentation_loss_lift μ A hA z hz C u hopt.1.2.2.1]
    have hmin := hopt.2 D v hv
    simp only [ENNReal.ofReal_one, one_mul] at hmin
    exact hmin.trans hle
  · have htop : actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) = ⊤ :=
      top_unique (le_of_not_gt hfinite)
    rw [htop]
    exact le_top

/-- The same canonical optimum preserves every source-feature F1 supremum
and the secondary expected-support objective, as well as reconstruction loss. -/
theorem exists_coefficient_optimum_preserving_observables
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    (μ : Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : X → FeatureVector M) (hz : Measurable z)
    (hz2 : Integrable (fun x => ‖representationToEuclidean M (z x)‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m)
    (γ : ℝ) (hγ : 0 < γ) (hwidth : m ≤ M) (hstablewidth : m ≤ 2 * K)
    (hopt : IsOptimalRepresentationPair μ A z (fun x => A.mulVec (z x)) B g γ K)
    (hfinite : actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) < ⊤)
    {S : Set (FeatureVector M)} (hS : S.Countable)
    (hae : ∀ᵐ q ∂Measure.map z μ, q ∈ S) (hrange : S ⊆ Set.range z) :
    ∃ (C : Matrix (Fin M) (Fin m) ℝ) (u : FeatureVector M → FeatureVector m),
      IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
        (1 : Matrix (Fin M) (Fin M) ℝ) id C u γ 1 K ∧
      Set.EqOn u (g ∘ A.mulVec) S ∧
      u ∘ z =ᵐ[μ] g ∘ (fun x => A.mulVec (z x)) ∧
      actualPopulationSquaredLoss (Measure.map z μ) (1 : Matrix (Fin M) (Fin M) ℝ) id C u =
        actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) ∧
      (∀ i, singleCoordinateF1Sup μ {x | 0 < z x i} (g ∘ fun x => A.mulVec (z x)) =
        singleCoordinateF1Sup (Measure.map z μ) {q | 0 < q i} u) ∧
      expectedCodeSupportSize μ (g ∘ fun x => A.mulVec (z x)) =
        expectedCodeSupportSize (Measure.map z μ) u := by
  obtain ⟨C, u, hu, hueq, huae, hloss⟩ := exists_coefficient_optimum_of_representation_optimum
    μ A hA z hz hz2 B g γ hγ hwidth hstablewidth hopt hfinite hS hae hrange
  exact ⟨C, u, hu, hueq, huae, hloss,
    singleCoordinateF1Sup_eq_of_map_and_ae μ _ z hz rfl u hu.1.2.2.1 _ huae.symm,
    expectedCodeSupportSize_eq_of_map_and_ae μ _ z hz rfl u hu.1.2.2.1 _ huae.symm⟩

/-- A source optimum selected for minimum expected support yields a canonical
optimum with the same secondary minimum, not just a primary optimum. -/
theorem exists_coefficient_selected_optimum_of_representation_selected_optimum
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    (μ : Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : X → FeatureVector M) (hz : Measurable z)
    (hz2 : Integrable (fun x => ‖representationToEuclidean M (z x)‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin m) ℝ) (g : RepresentationVector d → FeatureVector m)
    (γ : ℝ) (hγ : 0 < γ) (hwidth : m ≤ M) (hstablewidth : m ≤ 2 * K)
    (hopt : IsSparsitySelectedRepresentationPair μ A z (fun x => A.mulVec (z x)) B g γ K)
    (hfinite : actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) < ⊤)
    {S : Set (FeatureVector M)} (hS : S.Countable)
    (hae : ∀ᵐ q ∂Measure.map z μ, q ∈ S) (hrange : S ⊆ Set.range z) :
    ∃ (C : Matrix (Fin M) (Fin m) ℝ) (u : FeatureVector M → FeatureVector m),
      IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
        (1 : Matrix (Fin M) (Fin M) ℝ) id C u γ 1 K ∧
      u ∘ z =ᵐ[μ] g ∘ (fun x => A.mulVec (z x)) ∧
      (∀ (D : Matrix (Fin M) (Fin m) ℝ) (v : FeatureVector M → FeatureVector m),
        IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
          (1 : Matrix (Fin M) (Fin M) ℝ) id D v γ 1 K →
        expectedCodeSupportSize (Measure.map z μ) u ≤ expectedCodeSupportSize (Measure.map z μ) v) := by
  obtain ⟨C, u, hu, _, huae, _⟩ := exists_coefficient_optimum_of_representation_optimum
    μ A hA z hz hz2 B g γ hγ hwidth hstablewidth hopt.1 hfinite hS hae hrange
  refine ⟨C, u, hu, huae, ?_⟩
  intro D v hv
  have hcomp := hopt.2 (A * D) (v ∘ A.transpose.mulVec)
    (hv.orthonormal_representation_lift μ A hA z hz hz2 hγ hwidth hstablewidth hS hae hrange)
  have heq : (v ∘ A.transpose.mulVec) ∘ (fun x => A.mulVec (z x)) = v ∘ z := by
    funext x
    simp only [Function.comp_apply, orthonormalDictionary_transpose_left_inverse A hA]
  rw [heq, ← expectedCodeSupportSize_map_measurable μ z hz v hv.1.2.2.1,
    expectedCodeSupportSize_eq_of_map_and_ae μ _ z hz rfl u hu.1.2.2.1 _ huae.symm] at hcomp
  exact hcomp

/-- A canonical optimum with a minimum-support tie-break lifts to an actual
source optimum with the same tie-break. Only its actual finite loss is used;
finite loss of competing source optima follows from primary optimality. -/
theorem orthonormal_representation_lift_selected
    {X : Type*} [MeasurableSpace X] {d M m K : ℕ}
    (μ : Measure X) (A : Matrix (Fin d) (Fin M) ℝ)
    (hA : Orthonormal ℝ (fun j => representationToEuclidean d (A.col j)))
    (z : X → FeatureVector M) (hz : Measurable z)
    (hz2 : Integrable (fun x => ‖representationToEuclidean M (z x)‖ ^ 2) μ)
    (C : Matrix (Fin M) (Fin m) ℝ) (u : FeatureVector M → FeatureVector m)
    (γ : ℝ) (hγ : 0 < γ) (hwidth : m ≤ M) (hstablewidth : m ≤ 2 * K)
    (hopt : IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
      (1 : Matrix (Fin M) (Fin M) ℝ) id C u γ 1 K)
    (hfinite : actualPopulationSquaredLoss (Measure.map z μ)
      (1 : Matrix (Fin M) (Fin M) ℝ) id C u < ⊤)
    (hselected : ∀ (D : Matrix (Fin M) (Fin m) ℝ) (v : FeatureVector M → FeatureVector m),
      IsApproximatelyOptimalRecoveryPair (Measure.map z μ)
        (1 : Matrix (Fin M) (Fin M) ℝ) id D v γ 1 K →
      expectedCodeSupportSize (Measure.map z μ) u ≤ expectedCodeSupportSize (Measure.map z μ) v)
    {S : Set (FeatureVector M)} (hS : S.Countable)
    (hae : ∀ᵐ q ∂Measure.map z μ, q ∈ S) (hrange : S ⊆ Set.range z) :
    IsSparsitySelectedRepresentationPair μ A z (fun x => A.mulVec (z x))
      (A * C) (u ∘ A.transpose.mulVec) γ K := by
  have hlift := hopt.orthonormal_representation_lift μ A hA z hz hz2 hγ hwidth hstablewidth hS hae hrange
  refine ⟨hlift, ?_⟩
  intro B g hg
  have hgfinite : actualPopulationSquaredLoss μ A z B (g ∘ fun x => A.mulVec (z x)) < ⊤ := by
    apply lt_of_le_of_lt (hg.2 (A * C) (u ∘ A.transpose.mulVec) hlift.1)
    rwa [orthonormalRepresentation_loss_lift μ A hA z hz C u hopt.1.2.2.1]
  obtain ⟨D, v, hv, _, hvae, _⟩ := exists_coefficient_optimum_of_representation_optimum
    μ A hA z hz hz2 B g γ hγ hwidth hstablewidth hg hgfinite hS hae hrange
  have heq : (u ∘ A.transpose.mulVec) ∘ (fun x => A.mulVec (z x)) = u ∘ z := by
    funext x
    simp only [Function.comp_apply, orthonormalDictionary_transpose_left_inverse A hA]
  rw [heq, ← expectedCodeSupportSize_map_measurable μ z hz u hopt.1.2.2.1,
    expectedCodeSupportSize_eq_of_map_and_ae μ _ z hz rfl v hv.1.2.2.1 _ hvae.symm]
  exact hselected D v hv

end PKG26AtomicFeatures
