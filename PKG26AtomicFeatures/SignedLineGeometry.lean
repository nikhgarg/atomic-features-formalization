import PKG26AtomicFeatures.OrientationPenalty

/-!
# Orienting nearby atom lines

For unit atoms, a line-projector gap at most `δ` implies absolute inner
product at least `1 - δ²`, and one of the two signed distances is at most
`2δ`. No strict smallness of `δ` is needed for these geometric bounds.
The positive-cube orientation penalty excludes the negative alternative
when its loss floor exceeds the actual squared reconstruction loss.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- Applying the difference of the two line projectors to the first unit
vector bounds its residual after projection onto the second line. -/
theorem unit_line_projection_residual_le {d : ℕ}
    (a b : EuclideanRepresentation d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (δ : ℝ)
    (hgap : ‖(ℝ ∙ a).starProjection - (ℝ ∙ b).starProjection‖ ≤ δ) :
    ‖a - inner ℝ b a • b‖ ≤ δ := by
  have heval := ((ℝ ∙ a).starProjection - (ℝ ∙ b).starProjection).le_opNorm a
  rw [ContinuousLinearMap.sub_apply,
    (ℝ ∙ a).starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self a),
    Submodule.starProjection_unit_singleton ℝ hb, ha, mul_one] at heval
  exact heval.trans hgap

/-- Nearby unit-atom lines have absolute cosine at least `1-δ²`.
This includes `δ=0`, where the two atoms agree up to sign. -/
theorem abs_inner_ge_of_unit_line_projector_gap {d : ℕ}
    (a b : EuclideanRepresentation d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (δ : ℝ)
    (hgap : ‖(ℝ ∙ a).starProjection - (ℝ ∙ b).starProjection‖ ≤ δ) :
    1 - δ ^ 2 ≤ |inner ℝ a b| := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hgap
  have hres := unit_line_projection_residual_le a b ha hb δ hgap
  have hsq : ‖a - inner ℝ b a • b‖ ^ 2 = 1 - (inner ℝ a b) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, real_inner_smul_right,
      ha, hb, real_inner_comm b a]
    simp only [one_pow, mul_one, sq_abs]
    ring
  have hc : |inner ℝ a b| ≤ 1 := by
    simpa only [ha, hb, mul_one] using abs_real_inner_le_norm a b
  have hprod := mul_nonneg (abs_nonneg (inner ℝ a b)) (sub_nonneg.mpr hc)
  have hres_sq := mul_self_le_mul_self (norm_nonneg _) hres
  rw [← sq, ← sq, hsq] at hres_sq
  nlinarith [sq_abs (inner ℝ a b)]

/-- A unit vector lies within `2δ` of one orientation of a unit vector
whose line projector is within `δ`. There is no assumption `δ<1`. -/
theorem unit_atom_signed_distance_dichotomy {d : ℕ}
    (a b : EuclideanRepresentation d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (δ : ℝ)
    (hgap : ‖(ℝ ∙ a).starProjection - (ℝ ∙ b).starProjection‖ ≤ δ) :
    ‖a - b‖ ≤ 2 * δ ∨ ‖a + b‖ ≤ 2 * δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hgap
  have habs := abs_inner_ge_of_unit_line_projector_gap a b ha hb δ hgap
  by_cases hc : 0 ≤ inner ℝ a b
  · left
    rw [abs_of_nonneg hc] at habs
    have hsq := norm_sub_sq_real a b
    rw [ha, hb] at hsq
    nlinarith [sq_nonneg δ, norm_nonneg (a - b)]
  · right
    rw [abs_of_neg (lt_of_not_ge hc)] at habs
    have hsq := norm_add_sq_real a b
    rw [ha, hb] at hsq
    nlinarith [sq_nonneg δ, norm_nonneg (a + b)]

/-- Excluding the nearby negative orientation turns the absolute cosine
bound into the signed bound, with the same constant `1-δ²`. -/
theorem unit_atom_oriented_bounds_of_excluded_negative {d : ℕ}
    (a b : EuclideanRepresentation d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (δ : ℝ)
    (hgap : ‖(ℝ ∙ a).starProjection - (ℝ ∙ b).starProjection‖ ≤ δ)
    (hnegative : ¬ ‖a + b‖ ≤ 2 * δ) :
    ‖a - b‖ ≤ 2 * δ ∧ 1 - δ ^ 2 ≤ inner ℝ a b := by
  refine ⟨(unit_atom_signed_distance_dichotomy a b ha hb δ hgap).resolve_right
    hnegative, ?_⟩
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hgap
  have habs := abs_inner_ge_of_unit_line_projector_gap a b ha hb δ hgap
  have hc : 0 ≤ inner ℝ a b := by
    by_contra hn
    rw [abs_of_neg (lt_of_not_ge hn)] at habs
    have hsq := norm_add_sq_real a b
    rw [ha, hb] at hsq
    apply hnegative
    nlinarith [sq_nonneg δ, norm_nonneg (a + b)]
  rwa [abs_of_nonneg hc] at habs

/-- A singleton dictionary support spans exactly its atom line. -/
theorem euclideanColumnSpan_singleton {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (j : Fin M) :
    euclideanColumnSpan B {j} = ℝ ∙ representationToEuclidean d (B.col j) := by
  classical
  have hcolumns : Set.range (selectedColumns B {j}) = {B.col j} := by
    ext x
    constructor
    · rintro ⟨⟨l, hl⟩, rfl⟩
      have hl' : l = j := Finset.mem_singleton.mp hl
      subst l
      rfl
    · rintro rfl
      exact ⟨⟨j, Finset.mem_singleton_self j⟩, rfl⟩
  rw [euclideanColumnSpan, columnSpan, hcolumns, Submodule.map_span]
  rw [Set.image_singleton]
  rfl

/-- The line-projector estimate supplied by support matching gives the
same signed distance dichotomy for the actual unit dictionary columns. -/
theorem dictionary_atom_signed_distance_dichotomy {d M m : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (i : Fin M) (j : Fin m)
    (ha : ‖representationToEuclidean d (A.col i)‖ = 1)
    (hb : ‖representationToEuclidean d (B.col j)‖ = 1)
    (δ : ℝ)
    (hgap : ‖(euclideanColumnSpan A {i}).starProjection -
      (euclideanColumnSpan B {j}).starProjection‖ ≤ δ) :
    ‖representationToEuclidean d (A.col i) - representationToEuclidean d (B.col j)‖ ≤
        2 * δ ∨
      ‖representationToEuclidean d (A.col i) + representationToEuclidean d (B.col j)‖ ≤
        2 * δ := by
  rw [euclideanColumnSpan_singleton, euclideanColumnSpan_singleton] at hgap
  exact unit_atom_signed_distance_dichotomy _ _ ha hb δ hgap

/-- With a lower-bounded coefficient density, nonnegative sparse codes,
and actual squared loss strictly below the orientation floor, a nearby
learned atom has the positive source orientation. The support-projector
error `δ` and atom-line error `ζ` have separate explicit smallness bounds. -/
theorem signed_inner_ge_of_line_gap_and_small_loss
    {Ω : Type*} [MeasurableSpace Ω] {d M K : ℕ}
    (μ : Measure Ω) (Z : Ω → EuclideanRepresentation K) (hZ : Measurable Z)
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (code : Ω → FeatureVector M)
    (γ b c δ ζ : ℝ) (hγ : 0 < γ) (hb : 0 < b) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hdom : ENNReal.ofReal c • uniformCubeCoefficientLaw K ≤ Measure.map Z μ)
    (hT : T.card ≤ K) (hstable : SparseLowerStable B γ (2 * K))
    (hupper : ∀ z, ‖F z‖ ≤ b * ‖z‖)
    (hgap : ‖(LinearMap.range F.toLinearMap).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ)
    (hsmall : δ * b * ((K : ℝ) + 1) ≤ γ / 16)
    (i : Fin K) (j : Fin M) (hj : j ∈ T)
    (haunit : ‖F (coefficientBasisVector i)‖ = 1)
    (hbunit : ‖representationToEuclidean d (B.col j)‖ = 1)
    (hline : ‖(ℝ ∙ F (coefficientBasisVector i)).starProjection -
      (euclideanColumnSpan B {j}).starProjection‖ ≤ ζ)
    (hζ : ζ ≤ γ / 4)
    (hsparse : ∀ ω, (nonzeroSupport (code ω)).card ≤ K)
    (hnonneg : ∀ ω l, 0 ≤ code ω l)
    (hloss : (∫⁻ ω, ENNReal.ofReal
      (‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ^ 2) ∂μ) <
        ENNReal.ofReal (orientationLossFloor K γ b c)) :
    ‖F (coefficientBasisVector i) - representationToEuclidean d (B.col j)‖ ≤ 2 * ζ ∧
      1 - ζ ^ 2 ≤ inner ℝ (F (coefficientBasisVector i))
        (representationToEuclidean d (B.col j)) := by
  rw [euclideanColumnSpan_singleton] at hline
  apply unit_atom_oriented_bounds_of_excluded_negative _ _ haunit hbunit ζ hline
  intro hwrong
  have hwrong' : ‖F (coefficientBasisVector i) + representationToEuclidean d (B.col j)‖ ≤
      γ / 2 := hwrong.trans (by linarith)
  have hfloor := wrong_orientation_squared_loss_lower_bound μ Z hZ F B T code
    γ b c δ hγ hb hc hδ hdom hT hstable hupper hgap hsmall i j hj hwrong'
      hsparse hnonneg
  exact (not_le_of_gt hloss) hfloor

end PKG26AtomicFeatures
