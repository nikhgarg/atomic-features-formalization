import PKG26AtomicFeatures.NonnegativeLeastSquaresPopulation
import PKG26AtomicFeatures.FeatureF1Supremum

/-!
# Positive scaling of actual population recovery problems

A common positive scaling of source vectors is accompanied by the encoder
`x ↦ s • u (s⁻¹ • x)`. This gives inverse transports of the actual feasible
pairs, multiplies their actual expected squared losses by `s²`, and preserves
all multiplicative near-optimality comparisons and feature F1 suprema.
No canonical encoder or pointwise optimality is assumed.
-/

namespace PKG26AtomicFeatures

open MeasureTheory Set
open scoped ENNReal Matrix

/-- Actual source-law pushforward by a common coefficient scaling. -/
noncomputable def scaledSourceLaw {d : ℕ} (s : ℝ) (μ : Measure (FeatureVector d)) :
    Measure (FeatureVector d) :=
  Measure.map (fun x => s • x) μ

/-- The transported actual encoder, at an arbitrary input in scaled space. -/
noncomputable def scaledFeatureMap {d m : ℕ} (s : ℝ)
    (u : FeatureVector d → FeatureVector m) (x : FeatureVector d) : FeatureVector m :=
  s • u (s⁻¹ • x)

theorem measurable_scaledFeatureMap {d m : ℕ} (s : ℝ)
    {u : FeatureVector d → FeatureVector m} (hu : Measurable u) :
    Measurable (scaledFeatureMap s u) := by
  unfold scaledFeatureMap
  exact (hu.comp (measurable_const_smul s⁻¹)).const_smul s

@[simp] theorem scaledFeatureMap_apply_smul {d m : ℕ} (s : ℝ) (hs : s ≠ 0)
    (u : FeatureVector d → FeatureVector m) (x : FeatureVector d) :
    scaledFeatureMap s u (s • x) = s • u x := by
  simp only [scaledFeatureMap, inv_smul_smul₀ hs]

@[simp] theorem scaledFeatureMap_inverse {d m : ℕ} (s : ℝ) (hs : s ≠ 0)
    (u : FeatureVector d → FeatureVector m) :
    scaledFeatureMap s⁻¹ (scaledFeatureMap s u) = u := by
  funext x
  simp only [scaledFeatureMap, inv_inv, inv_smul_smul₀ hs]

@[simp] theorem scaledFeatureMap_inverse_right {d m : ℕ} (s : ℝ) (hs : s ≠ 0)
    (u : FeatureVector d → FeatureVector m) :
    scaledFeatureMap s (scaledFeatureMap s⁻¹ u) = u := by
  simpa only [inv_inv] using scaledFeatureMap_inverse s⁻¹ (inv_ne_zero hs) u

@[simp] theorem scaledSourceLaw_inverse {d : ℕ} (s : ℝ) (hs : s ≠ 0)
    (μ : Measure (FeatureVector d)) : scaledSourceLaw s⁻¹ (scaledSourceLaw s μ) = μ := by
  rw [scaledSourceLaw, scaledSourceLaw,
    Measure.map_map (measurable_const_smul s⁻¹) (measurable_const_smul s)]
  have heq : (fun x : FeatureVector d => s⁻¹ • x) ∘ (fun x => s • x) = id := by
    funext x
    exact inv_smul_smul₀ hs x
  rw [heq, Measure.map_id]

/-- Nonzero common coefficient scaling preserves the actual finite support. -/
theorem nonzeroSupport_smul_eq {m : ℕ} (s : ℝ) (hs : s ≠ 0) (v : FeatureVector m) :
    nonzeroSupport (s • v) = nonzeroSupport v := by
  ext j
  simp only [mem_nonzeroSupport_iff, Pi.smul_apply, smul_eq_mul, mul_ne_zero_iff]
  exact and_iff_right hs

/-- Feasibility transports without changing the dictionary: the actual
encoder remains measurable, nonnegative, and K-sparse. -/
theorem IsFeasibleRecoveryPair.scaledFeatureMap {d m K : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {u : FeatureVector d → FeatureVector m} {γ : ℝ}
    (h : IsFeasibleRecoveryPair B u γ K) (s : ℝ) (hs : 0 < s) :
    IsFeasibleRecoveryPair B (scaledFeatureMap s u) γ K := by
  refine ⟨h.1, h.2.1, measurable_scaledFeatureMap s h.2.2.1, ?_, ?_⟩
  · intro x
    change (nonzeroSupport (s • u (s⁻¹ • x))).card ≤ K
    rw [nonzeroSupport_smul_eq s hs.ne']
    exact h.2.2.2.1 _
  · intro x j
    exact mul_nonneg hs.le (h.2.2.2.2 _ j)

/-- The positive scaling transport is a bijection of the actual feasible
encoder class for each fixed normalized stable dictionary. -/
theorem isFeasibleRecoveryPair_scaledFeatureMap_iff {d m K : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (u : FeatureVector d → FeatureVector m)
    (γ s : ℝ) (hs : 0 < s) :
    IsFeasibleRecoveryPair B (scaledFeatureMap s u) γ K ↔ IsFeasibleRecoveryPair B u γ K := by
  constructor
  · intro h
    simpa only [scaledFeatureMap_inverse s hs.ne'] using h.scaledFeatureMap s⁻¹ (inv_pos.mpr hs)
  · exact fun h => h.scaledFeatureMap s hs

/-- The actual nonnegative expected loss scales by exactly `s²`, including
infinite losses. Both source and code are scaled in genuine Euclidean norms. -/
theorem actualPopulationSquaredLoss_positive_scaling {d m : ℕ}
    (μ : Measure (FeatureVector d)) (B : Matrix (Fin d) (Fin m) ℝ)
    (u : FeatureVector d → FeatureVector m) (hu : Measurable u)
    (s : ℝ) (hs : 0 < s) :
    actualPopulationSquaredLoss (scaledSourceLaw s μ) (1 : Matrix (Fin d) (Fin d) ℝ)
      id B (scaledFeatureMap s u) =
        ENNReal.ofReal (s ^ 2) * actualPopulationSquaredLoss μ
          (1 : Matrix (Fin d) (Fin d) ℝ) id B u := by
  have hmeas := measurable_euclideanSquaredResidual
    (representationToEuclidean d).continuous.measurable B (measurable_scaledFeatureMap s hu)
  simp only [actualPopulationSquaredLoss, Matrix.one_mulVec, id_eq, scaledSourceLaw]
  rw [lintegral_map hmeas (measurable_const_smul s)]
  have hpoint (x : FeatureVector d) : ENNReal.ofReal
      (‖representationToEuclidean d (s • x) -
        representationToEuclidean d (B.mulVec (scaledFeatureMap s u (s • x)))‖ ^ 2) =
      ENNReal.ofReal (s ^ 2) * ENNReal.ofReal
        (‖representationToEuclidean d x - representationToEuclidean d (B.mulVec (u x))‖ ^ 2) := by
    rw [scaledFeatureMap_apply_smul s hs.ne', Matrix.mulVec_smul, map_smul, map_smul,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow,
      ENNReal.ofReal_mul (sq_nonneg s)]
  simp_rw [hpoint]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Every actual feasible-pair comparison, over every dictionary and code,
transports under positive scaling. In particular this covers exact optimality
by taking approximation factor one. -/
theorem IsApproximatelyOptimalRecoveryPair.positive_scaling {d m K : ℕ}
    {μ : Measure (FeatureVector d)} {B : Matrix (Fin d) (Fin m) ℝ}
    {u : FeatureVector d → FeatureVector m} {γ C : ℝ}
    (h : IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ) id B u γ C K)
    (s : ℝ) (hs : 0 < s) :
    IsApproximatelyOptimalRecoveryPair (scaledSourceLaw s μ)
      (1 : Matrix (Fin d) (Fin d) ℝ) id B (scaledFeatureMap s u) γ C K := by
  refine ⟨h.1.scaledFeatureMap s hs, ?_⟩
  intro B' v hv
  have hvinv := hv.scaledFeatureMap s⁻¹ (inv_pos.mpr hs)
  have hcomp := h.2 B' (scaledFeatureMap s⁻¹ v) hvinv
  rw [actualPopulationSquaredLoss_positive_scaling μ B u h.1.2.2.1 s hs]
  have hscale := actualPopulationSquaredLoss_positive_scaling μ B'
    (scaledFeatureMap s⁻¹ v) hvinv.2.2.1 s hs
  rw [scaledFeatureMap_inverse_right s hs.ne'] at hscale
  rw [hscale]
  exact (mul_le_mul_right hcomp (ENNReal.ofReal (s ^ 2))).trans_eq (by ac_rfl)

/-- Positive scaling and its inverse preserve exactly the same C-factor
optimality property in the actual dictionary/encoder optimization problem. -/
theorem isApproximatelyOptimalRecoveryPair_positive_scaling_iff {d m K : ℕ}
    (μ : Measure (FeatureVector d)) (B : Matrix (Fin d) (Fin m) ℝ)
    (u : FeatureVector d → FeatureVector m) (γ C s : ℝ) (hs : 0 < s) :
    IsApproximatelyOptimalRecoveryPair (scaledSourceLaw s μ)
      (1 : Matrix (Fin d) (Fin d) ℝ) id B (scaledFeatureMap s u) γ C K ↔
    IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ) id B u γ C K := by
  constructor
  · intro h
    simpa only [scaledSourceLaw_inverse s hs.ne', scaledFeatureMap_inverse s hs.ne'] using
      h.positive_scaling s⁻¹ (inv_pos.mpr hs)
  · exact fun h => h.positive_scaling s hs

/-- Any encoder on scaled source space can be pulled back before evaluating
its actual loss; this is the inverse form of the exact loss identity. -/
theorem actualPopulationSquaredLoss_scaledSourceLaw {d m : ℕ}
    (μ : Measure (FeatureVector d)) (B : Matrix (Fin d) (Fin m) ℝ)
    (v : FeatureVector d → FeatureVector m) (hv : Measurable v)
    (s : ℝ) (hs : 0 < s) :
    actualPopulationSquaredLoss (scaledSourceLaw s μ) (1 : Matrix (Fin d) (Fin d) ℝ) id B v =
      ENNReal.ofReal (s ^ 2) * actualPopulationSquaredLoss μ
        (1 : Matrix (Fin d) (Fin d) ℝ) id B (scaledFeatureMap s⁻¹ v) := by
  simpa only [scaledFeatureMap_inverse_right s hs.ne'] using
    actualPopulationSquaredLoss_positive_scaling μ B (scaledFeatureMap s⁻¹ v)
      (measurable_scaledFeatureMap s⁻¹ hv) s hs

/-- Near-optimality of an arbitrary actual encoder on scaled source space
is equivalent to near-optimality of its inverse transport. -/
theorem isApproximatelyOptimalRecoveryPair_scaledSourceLaw_iff {d m K : ℕ}
    (μ : Measure (FeatureVector d)) (B : Matrix (Fin d) (Fin m) ℝ)
    (v : FeatureVector d → FeatureVector m) (γ C s : ℝ) (hs : 0 < s) :
    IsApproximatelyOptimalRecoveryPair (scaledSourceLaw s μ)
      (1 : Matrix (Fin d) (Fin d) ℝ) id B v γ C K ↔
    IsApproximatelyOptimalRecoveryPair μ (1 : Matrix (Fin d) (Fin d) ℝ)
      id B (scaledFeatureMap s⁻¹ v) γ C K := by
  simpa only [scaledFeatureMap_inverse_right s hs.ne'] using
    isApproximatelyOptimalRecoveryPair_positive_scaling_iff μ B (scaledFeatureMap s⁻¹ v) γ C s hs

/-- Measurable pushforwards preserve F1 when both actual events are pulled back. -/
theorem populationF1_map_measurable
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (f : Ω → Ξ) (hf : Measurable f)
    (truth prediction : Set Ξ) (ht : MeasurableSet truth) (hp : MeasurableSet prediction) :
    populationF1 (Measure.map f μ) truth prediction =
      populationF1 μ (f ⁻¹' truth) (f ⁻¹' prediction) := by
  simp only [populationF1, map_measureReal_apply hf ht, map_measureReal_apply hf hp,
    map_measureReal_apply hf (ht.inter hp), Set.preimage_inter]

/-- The actual source presence event and each scaled positive-threshold
prediction have exactly their original F1 under the scaled source law. -/
theorem populationF1_positive_scaling {d m : ℕ}
    (μ : Measure (FeatureVector d)) (u : FeatureVector d → FeatureVector m)
    (hu : Measurable u) (s : ℝ) (hs : 0 < s) (i : Fin d) (j : Fin m) (t : ℝ) :
    populationF1 (scaledSourceLaw s μ) {x | 0 < x i}
      {x | s * t < scaledFeatureMap s u x j} =
      populationF1 μ {x | 0 < x i} {x | t < u x j} := by
  rw [scaledSourceLaw, populationF1_map_measurable μ _ (measurable_const_smul s)
    {x | 0 < x i} {x | s * t < scaledFeatureMap s u x j}
    (measurableSet_lt measurable_const (measurable_pi_apply i))
    (measurableSet_lt measurable_const
      ((measurable_pi_apply j).comp (measurable_scaledFeatureMap s hu)))]
  have htruth : (fun x : FeatureVector d => s • x) ⁻¹' {x | 0 < x i} = {x | 0 < x i} := by
    ext x
    exact mul_pos_iff_of_pos_left hs
  have hpred : (fun x : FeatureVector d => s • x) ⁻¹'
      {x | s * t < scaledFeatureMap s u x j} = {x | t < u x j} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, scaledFeatureMap_apply_smul s hs.ne',
      Pi.smul_apply, smul_eq_mul]
    exact mul_lt_mul_iff_of_pos_left hs
  rw [htruth, hpred]

/-- Multiplication of thresholds by a positive scalar is a bijection, so
the complete single-coordinate F1 supremum is invariant. No finite-measure
assumption or maximizing threshold is needed for this exact identity. -/
theorem singleCoordinateF1Sup_positive_scaling {d m : ℕ}
    (μ : Measure (FeatureVector d)) (u : FeatureVector d → FeatureVector m)
    (hu : Measurable u) (s : ℝ) (hs : 0 < s) (i : Fin d) :
    singleCoordinateF1Sup (scaledSourceLaw s μ) {x | 0 < x i} (scaledFeatureMap s u) =
      singleCoordinateF1Sup μ {x | 0 < x i} u := by
  unfold singleCoordinateF1Sup
  congr 1
  ext r
  constructor
  · rintro ⟨j, t, ht, hr⟩
    have hscore := populationF1_positive_scaling μ u hu s hs i j (t / s)
    have hst : s * (t / s) = t := by field_simp
    rw [hst] at hscore
    exact ⟨j, t / s, div_pos ht hs, hr.trans hscore⟩
  · rintro ⟨j, t, ht, hr⟩
    exact ⟨j, s * t, mul_pos hs ht,
      hr.trans (populationF1_positive_scaling μ u hu s hs i j t).symm⟩

/-- Inverse-transport form for an arbitrary encoder on the scaled law. -/
theorem singleCoordinateF1Sup_scaledSourceLaw {d m : ℕ}
    (μ : Measure (FeatureVector d)) (v : FeatureVector d → FeatureVector m)
    (hv : Measurable v) (s : ℝ) (hs : 0 < s) (i : Fin d) :
    singleCoordinateF1Sup (scaledSourceLaw s μ) {x | 0 < x i} v =
      singleCoordinateF1Sup μ {x | 0 < x i} (scaledFeatureMap s⁻¹ v) := by
  simpa only [scaledFeatureMap_inverse_right s hs.ne'] using
    singleCoordinateF1Sup_positive_scaling μ (scaledFeatureMap s⁻¹ v)
      (measurable_scaledFeatureMap s⁻¹ hv) s hs i

end PKG26AtomicFeatures
