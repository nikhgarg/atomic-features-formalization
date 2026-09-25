import PKG26AtomicFeatures.ProjectedCoefficientCodes
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal

/-- The Euclidean inverse estimate controls every coefficient error. -/
theorem coordinate_error_le_of_code_comparison {M : ℕ}
    (u : FeatureVector M) (v : EuclideanRepresentation M)
    (γ error projection : ℝ) (hγ : 0 ≤ γ)
    (hcomparison : γ * ‖representationToEuclidean M u - v‖ ≤ error + projection)
    (j : Fin M) : γ * |u j - v j| ≤ error + projection := by
  have hcoordinate : |u j - v j| ≤ ‖representationToEuclidean M u - v‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (representationToEuclidean M u - v) j
  exact (mul_le_mul_of_nonneg_left hcoordinate hγ).trans hcomparison

/-- An above-threshold coefficient outside the projected support requires
actual reconstruction error larger than half the stable threshold. -/
theorem outside_support_activation_implies_large_error {M : ℕ}
    (u : FeatureVector M) (v : EuclideanRepresentation M) (T : Finset (Fin M))
    (hsupport : nonzeroSupport ((representationToEuclidean M).symm v) ⊆ T)
    (γ t error projection : ℝ) (hγ : 0 < γ)
    (hcomparison : γ * ‖representationToEuclidean M u - v‖ ≤ error + projection)
    (hprojection : projection ≤ γ * t / 2)
    (j : Fin M) (hj : j ∉ T) (hactive : t < u j) : γ * t / 2 < error := by
  have hvzero : v j = 0 := by
    by_contra hv
    exact hj (hsupport ((mem_nonzeroSupport_iff _ j).mpr hv))
  have hcoordinate := coordinate_error_le_of_code_comparison u v γ error projection hγ.le hcomparison j
  rw [hvzero, sub_zero] at hcoordinate
  have habs : u j ≤ |u j| := le_abs_self _
  have hstrict := mul_lt_mul_of_pos_left hactive hγ
  have hle := mul_le_mul_of_nonneg_left habs hγ.le
  linarith

/-- A nonnegative coefficient below threshold, with small actual error,
forces the corresponding projected coefficient into a slab of radius `2t`. -/
theorem inactive_coordinate_implies_projected_slab {M : ℕ}
    (u : FeatureVector M) (v : EuclideanRepresentation M)
    (γ t error projection : ℝ) (hγ : 0 < γ)
    (hcomparison : γ * ‖representationToEuclidean M u - v‖ ≤ error + projection)
    (hprojection : projection ≤ γ * t / 2) (herror : error ≤ γ * t / 2)
    (j : Fin M) (huj : 0 ≤ u j) (hinactive : u j ≤ t) : |v j| ≤ 2 * t := by
  have hcoordinate := coordinate_error_le_of_code_comparison u v γ error projection hγ.le hcomparison j
  have hdiff : |u j - v j| ≤ t := by
    apply (mul_le_mul_iff_right₀ hγ).mp
    linarith
  have htriangle : |v j| ≤ |u j| + |u j - v j| := by
    calc
      |v j| = |u j + (v j - u j)| := by congr 1; ring
      _ ≤ |u j| + |v j - u j| := abs_add_le _ _
      _ = |u j| + |u j - v j| := by rw [abs_sub_comm (v j) (u j)]
  rw [abs_of_nonneg huj] at htriangle
  linarith

/-- The real mass of a strict residual tail is bounded by nonnegative
expected squared loss divided by the squared threshold. No integrability
assumption is needed for the nonnegative extended integral. -/
theorem measureReal_residual_tail_le_of_squared_loss
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (residual : Ω → ℝ) (hresidual : Measurable residual)
    (r L : ℝ) (hr : 0 < r) (hL : 0 ≤ L)
    (hloss : (∫⁻ ω, ENNReal.ofReal (residual ω ^ 2) ∂μ) ≤ ENNReal.ofReal L) :
    μ.real {ω | r < residual ω} ≤ L / r ^ 2 := by
  let bad : Set Ω := {ω | r < residual ω}
  have hbad : MeasurableSet bad := measurableSet_lt measurable_const hresidual
  have hindicator : bad.indicator (fun _ => ENNReal.ofReal (r ^ 2)) ≤
      fun ω => ENNReal.ofReal (residual ω ^ 2) := by
    intro ω
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_mem hω]
      apply ENNReal.ofReal_le_ofReal
      have hh : r < residual ω := hω
      nlinarith
    · rw [Set.indicator_of_notMem hω]
      exact zero_le _
  have hintegral := (lintegral_mono hindicator).trans hloss
  rw [lintegral_indicator_const hbad] at hintegral
  have hproduct : ENNReal.ofReal (r ^ 2 * μ.real bad) ≤ ENNReal.ofReal L := by
    rw [ENNReal.ofReal_mul (sq_nonneg r), ofReal_measureReal]
    exact hintegral
  have hreal := (ENNReal.ofReal_le_ofReal_iff hL).mp hproduct
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith

/-- The threshold `γt/2` yields the squared-loss Markov bound
`4L/(γ²t²)`. -/
theorem measureReal_stable_threshold_error_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (residual : Ω → ℝ) (hresidual : Measurable residual)
    (γ t L : ℝ) (hγ : 0 < γ) (ht : 0 < t) (hL : 0 ≤ L)
    (hloss : (∫⁻ ω, ENNReal.ofReal (residual ω ^ 2) ∂μ) ≤ ENNReal.ofReal L) :
    μ.real {ω | γ * t / 2 < residual ω} ≤ 4 * L / (γ ^ 2 * t ^ 2) := by
  have hbound := measureReal_residual_tail_le_of_squared_loss μ residual hresidual
    (γ * t / 2) L (by positivity) hL hloss
  have heq : L / (γ * t / 2) ^ 2 = 4 * L / (γ ^ 2 * t ^ 2) := by
    field_simp; ring
  simpa only [heq] using hbound

/-- A row functional whose norm is at least `c` inherits a small-slab
bound from the coefficient law at radius `2t/c`. -/
theorem measureReal_functional_slab_le_of_unit_direction_bound
    {Ω : Type*} {K : ℕ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → EuclideanRepresentation K)
    (L : EuclideanRepresentation K →L[ℝ] ℝ)
    (c t ε : ℝ) (hc : 0 < c) (hL : c ≤ ‖L‖)
    (hslab : ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
      μ.real {ω | |inner ℝ v (Z ω)| ≤ 2 * t / c} ≤ ε) :
    μ.real {ω | |L (Z ω)| ≤ 2 * t} ≤ ε := by
  obtain ⟨v, hvnorm, hdom⟩ := exists_unit_direction_of_functional_norm_lower_bound L c hc hL
  refine (measureReal_mono (μ := μ) (show {ω | |L (Z ω)| ≤ 2 * t} ⊆
      {ω | |inner ℝ v (Z ω)| ≤ 2 * t / c} from ?_)).trans (hslab v hvnorm)
  intro ω hω
  apply (le_div_iff₀ hc).mpr
  have h := (hdom (Z ω)).trans hω
  nlinarith

/-- The inverse estimate gives thresholded error probabilities: false
positives lie in the large-residual event, while false negatives lie in
that event or in a projected row's small slab. -/
theorem threshold_probabilities_of_code_comparison
    {Ω : Type*} {M K : ℕ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → EuclideanRepresentation K) (u : Ω → FeatureVector M)
    (D : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation M)
    (T : Finset (Fin M))
    (hsupport : ∀ z, nonzeroSupport ((representationToEuclidean M).symm (D z)) ⊆ T)
    (γ t ε : ℝ) (hγ : 0 < γ)
    (residual projection : Ω → ℝ)
    (hcomparison : ∀ ω, γ * ‖representationToEuclidean M (u ω) - D (Z ω)‖ ≤
      residual ω + projection ω)
    (hprojection : ∀ᵐ ω ∂μ, projection ω ≤ γ * t / 2)
    (hnonneg : ∀ ω j, 0 ≤ u ω j)
    (hslab : ∀ j ∈ T, μ.real {ω | |D (Z ω) j| ≤ 2 * t} ≤ ε) :
    (∀ j ∉ T, μ.real {ω | t < u ω j} ≤ μ.real {ω | γ * t / 2 < residual ω}) ∧
      ∀ j ∈ T, μ.real {ω | u ω j ≤ t} ≤ μ.real {ω | γ * t / 2 < residual ω} + ε := by
  constructor
  · intro j hj
    have hsubset : {ω | t < u ω j} ≤ᵐ[μ] {ω | γ * t / 2 < residual ω} := by
      filter_upwards [hprojection] with ω hω
      intro hactive
      exact outside_support_activation_implies_large_error (u ω) (D (Z ω)) T
        (hsupport (Z ω)) γ t (residual ω) (projection ω) hγ (hcomparison ω) hω j hj hactive
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsubset)
  · intro j hj
    have hsubset : ∀ᵐ ω ∂μ, u ω j ≤ t →
        γ * t / 2 < residual ω ∨ |D (Z ω) j| ≤ 2 * t := by
      filter_upwards [hprojection] with ω hω
      intro hinactive
      by_cases hbad : γ * t / 2 < residual ω
      · exact Or.inl hbad
      · apply Or.inr
        exact inactive_coordinate_implies_projected_slab (u ω) (D (Z ω)) γ t
          (residual ω) (projection ω) hγ (hcomparison ω) hω (le_of_not_gt hbad)
          j (hnonneg ω j) hinactive
    have hmeasure : μ.real {ω | u ω j ≤ t} ≤
        μ.real ({ω | γ * t / 2 < residual ω} ∪ {ω | |D (Z ω) j| ≤ 2 * t}) :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsubset)
    exact hmeasure.trans ((measureReal_union_le _ _).trans (add_le_add le_rfl (hslab j hj)))

/-- A close stable learned support recovers thresholded feature indicators
under a uniform coefficient small-slab bound. The projected coefficient map
is constructed from the dictionary, and the actual nonnegative code may
depend on the random outcome separately from the source coefficients.

The projection error is absorbed into the threshold condition
`δ * b * R ≤ γ * t / 2`; the probability bounds contain no additional
squared projection-error term. -/
theorem thresholded_feature_error_probabilities_of_projector_bound
    {Ω : Type*} {d M K : ℕ} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → EuclideanRepresentation K) (hZ : Measurable Z)
    (code : Ω → FeatureVector M) (hcode : Measurable code)
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (T : Finset (Fin M))
    (a b γ δ R t ε L : ℝ)
    (hK : 0 < K) (ha : 0 < a) (hγ : 0 < γ) (hδ : 0 ≤ δ) (ht : 0 < t) (hL : 0 ≤ L)
    (hT : T.card = K) (hstable : SparseLowerStable B γ (2 * K))
    (hunit : ∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1)
    (hlower : ∀ z, a * ‖z‖ ≤ ‖F z‖) (hupper : ∀ z, ‖F z‖ ≤ b * ‖z‖)
    (hsmall : δ * b ≤ a / 2)
    (hgap : ‖(LinearMap.range F.toLinearMap).starProjection -
      (euclideanColumnSpan B T).starProjection‖ ≤ δ)
    (hbounded : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ R)
    (hprojection : δ * b * R ≤ γ * t / 2)
    (hnonneg : ∀ ω j, 0 ≤ code ω j)
    (hsparse : ∀ ω, (nonzeroSupport (code ω)).card ≤ K)
    (hslab : ∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
      μ.real {ω | |inner ℝ v (Z ω)| ≤ 2 * t / (a / (2 * (K : ℝ)))} ≤ ε)
    (hloss : (∫⁻ ω, ENNReal.ofReal
      (‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ^ 2) ∂μ) ≤
        ENNReal.ofReal L) :
    (∀ j ∉ T, μ.real {ω | t < code ω j} ≤ 4 * L / (γ ^ 2 * t ^ 2)) ∧
      ∀ j ∈ T, μ.real {ω | code ω j ≤ t} ≤ 4 * L / (γ ^ 2 * t ^ 2) + ε := by
  obtain ⟨D, hsupport, _, _, _, hrow, hcomparison⟩ :=
    exists_projected_coefficient_map_with_row_bounds F B T a b γ δ hK ha hγ hδ
      hT hstable hunit hlower hupper hsmall hgap
  have hc : 0 < a / (2 * (K : ℝ)) := by positivity
  have hrowslab (j : Fin M) (hj : j ∈ T) :
      μ.real {ω | |D (Z ω) j| ≤ 2 * t} ≤ ε :=
    measureReal_functional_slab_le_of_unit_direction_bound μ Z
      ((PiLp.proj 2 (fun _ : Fin M => ℝ) j).comp D)
      (a / (2 * (K : ℝ))) t ε hc (hrow j hj) hslab
  have hb : 0 ≤ b := by
    let z : EuclideanRepresentation K := PiLp.single 2 ⟨0, hK⟩ 1
    have hz : ‖z‖ = 1 := by simp only [z, PiLp.norm_single, norm_one]
    have h := hlower z
    have h' := hupper z
    rw [hz, mul_one] at h h'
    linarith
  have hprojae : ∀ᵐ ω ∂μ, δ * ‖F (Z ω)‖ ≤ γ * t / 2 := by
    filter_upwards [hbounded] with ω hω
    calc
      δ * ‖F (Z ω)‖ ≤ δ * (b * ‖Z ω‖) := mul_le_mul_of_nonneg_left (hupper _) hδ
      _ ≤ δ * (b * R) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hω hb) hδ
      _ ≤ γ * t / 2 := by nlinarith [hprojection]
  let residual := fun ω => ‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖
  have hresidual : Measurable residual := by
    exact ((F.continuous.measurable.comp hZ).sub
      ((representationToEuclidean d).continuous.measurable.comp
        (B.mulVecLin.continuous_of_finiteDimensional.measurable.comp hcode))).norm
  obtain ⟨hfp, hfn⟩ := threshold_probabilities_of_code_comparison μ Z code D T
    hsupport γ t ε hγ residual (fun ω => δ * ‖F (Z ω)‖)
    (fun ω => hcomparison (Z ω) (code ω) (hsparse ω)) hprojae hnonneg hrowslab
  have hmarkov := measureReal_stable_threshold_error_le μ residual hresidual γ t L hγ ht hL hloss
  exact ⟨fun j hj => (hfp j hj).trans hmarkov,
    fun j hj => (hfn j hj).trans (add_le_add hmarkov le_rfl)⟩

end PKG26AtomicFeatures
