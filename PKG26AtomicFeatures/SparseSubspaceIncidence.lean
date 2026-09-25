import PKG26AtomicFeatures.SparseImageCompression
import PKG26AtomicFeatures.StableSupportIntersections
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped ENNReal

/-- A linear map large on one vector dominates a fixed unit coefficient
functional. The direction is obtained from its adjoint. -/
theorem exists_unit_direction_residual_lower_bound {K d : ℕ}
    (L : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (s : ℝ) (hs : 0 < s) (z : EuclideanRepresentation K)
    (hz : s * ‖z‖ < ‖L z‖) :
    ∃ v : EuclideanRepresentation K, ‖v‖ = 1 ∧
      ∀ w, s * |inner ℝ v w| ≤ ‖L w‖ := by
  let q := ‖L z‖⁻¹ • L z
  have hLz : 0 < ‖L z‖ := (mul_nonneg hs.le (norm_nonneg z)).trans_lt hz
  have hqnorm : ‖q‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLz)]
    exact inv_mul_cancel₀ hLz.ne'
  let f := L.adjoint q
  have hfz : inner ℝ f z = ‖L z‖ := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    dsimp [q]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hnorm : s < ‖f‖ := by
    have hinner := abs_real_inner_le_norm f z
    rw [hfz, abs_of_pos hLz] at hinner
    by_contra hn
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (norm_nonneg z)
    linarith
  have hfpos : 0 < ‖f‖ := hs.trans hnorm
  let v := ‖f‖⁻¹ • f
  refine ⟨v, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfpos)]
    exact inv_mul_cancel₀ hfpos.ne'
  · intro w
    have hfv : ‖f‖ • v = f := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ hfpos.ne', one_smul]
    calc
      s * |inner ℝ v w| ≤ ‖f‖ * |inner ℝ v w| :=
        mul_le_mul_of_nonneg_right hnorm.le (abs_nonneg _)
      _ = |inner ℝ f w| := by
        conv_rhs => rw [← hfv, real_inner_smul_left, abs_mul, abs_of_pos hfpos]
      _ = |inner ℝ q (L w)| := by rw [ContinuousLinearMap.adjoint_inner_left]
      _ ≤ ‖L w‖ := by simpa only [hqnorm, one_mul] using abs_real_inner_le_norm q (L w)

/-- Projection perpendicular to a subspace gives a residual no larger than
the error of any point in that subspace. -/
theorem norm_orthogonal_projection_le_sub_of_mem {d : ℕ}
    (V : Submodule ℝ (EuclideanRepresentation d))
    (x y : EuclideanRepresentation d) (hy : y ∈ V) :
    ‖Vᗮ.starProjection x‖ ≤ ‖x - y‖ := by
  have hzero : Vᗮ.starProjection y = 0 := V.starProjection_orthogonal_apply_eq_zero hy
  have hproj := Vᗮ.norm_starProjection_apply_le (x - y)
  simpa only [map_sub, hzero, sub_zero] using hproj

/-- Failure of directed subspace approximation produces a unit coefficient
direction whose magnitude lower-bounds every residual to the target span. -/
theorem exists_direction_of_no_directed_approximation {K d : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (V : Submodule ℝ (EuclideanRepresentation d)) (a δ : ℝ)
    (ha : 0 < a) (hδ : 0 < δ)
    (hlower : ∀ z, a * ‖z‖ ≤ ‖F z‖)
    (hfar : ¬ ∀ x ∈ LinearMap.range F.toLinearMap,
      ∃ y ∈ V, ‖x - y‖ ≤ δ * ‖x‖) :
    ∃ v : EuclideanRepresentation K, ‖v‖ = 1 ∧
      ∀ z y, y ∈ V → a * δ * |inner ℝ v z| ≤ ‖F z - y‖ := by
  have hfail : ¬ ∀ x ∈ LinearMap.range F.toLinearMap,
      ‖Vᗮ.starProjection x‖ ≤ δ * ‖x‖ := by
    intro h
    apply hfar
    intro x hx
    refine ⟨V.starProjection x, V.starProjection_apply_mem x, ?_⟩
    simpa only [Submodule.starProjection_orthogonal_val] using h x hx
  push Not at hfail
  obtain ⟨x, ⟨z, rfl⟩, hz⟩ := hfail
  change δ * ‖F z‖ < ‖Vᗮ.starProjection (F z)‖ at hz
  have hlarge : (a * δ) * ‖z‖ < ‖(Vᗮ.starProjection.comp F) z‖ := by
    have hl := mul_le_mul_of_nonneg_left (hlower z) hδ.le
    change (a * δ) * ‖z‖ < ‖Vᗮ.starProjection (F z)‖
    nlinarith
  obtain ⟨v, hv, hres⟩ := exists_unit_direction_residual_lower_bound
    (Vᗮ.starProjection.comp F) (a * δ) (mul_pos ha hδ) z hlarge
  refine ⟨v, hv, fun z y hy => ?_⟩
  exact (hres z).trans (norm_orthogonal_projection_le_sub_of_mem V (F z) y hy)

/-- A finite collection of narrow coefficient slabs has a complement of
probability at least three quarters when each slab has mass at most
`1 / (4 * (N + 1))` and there are at most `N` directions. -/
theorem measureReal_compl_finite_slabs_ge
    {Ω J K : Type*} [MeasurableSpace Ω] [Fintype J] [Fintype K]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → EuclideanSpace ℝ K) (hZ : Measurable Z)
    (v : J → EuclideanSpace ℝ K) (N : ℕ) (hcard : Fintype.card J ≤ N)
    (t : ℝ)
    (hslab : ∀ j, μ.real {ω | |inner ℝ (v j) (Z ω)| ≤ t} ≤
      1 / (4 * ((N : ℝ) + 1))) :
    3 / 4 ≤ μ.real (⋃ j, {ω | |inner ℝ (v j) (Z ω)| ≤ t})ᶜ := by
  classical
  have hmeas (j : J) : MeasurableSet {ω | |inner ℝ (v j) (Z ω)| ≤ t} :=
    measurableSet_le ((continuous_const.inner continuous_id).abs.measurable.comp hZ)
      measurable_const
  have hbad : μ.real (⋃ j, {ω | |inner ℝ (v j) (Z ω)| ≤ t}) ≤ 1 / 4 := by
    calc
      _ ≤ ∑ j, μ.real {ω | |inner ℝ (v j) (Z ω)| ≤ t} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : J, 1 / (4 * ((N : ℝ) + 1)) := Finset.sum_le_sum fun j _ => hslab j
      _ = (Fintype.card J : ℝ) * (1 / (4 * ((N : ℝ) + 1))) := by simp
      _ ≤ (N : ℝ) * (1 / (4 * ((N : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ ≤ 1 / 4 := by
        rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 4 * ((N : ℝ) + 1))]
        nlinarith
  have hsum := measureReal_add_measureReal_compl (μ := μ) (MeasurableSet.iUnion hmeas)
  rw [probReal_univ] at hsum
  linarith

/-- On a measurable event of mass at least three quarters, a lower bound
on a nonnegative residual gives the corresponding squared-loss bound.
The nonnegative extended integral remains meaningful for infinite loss. -/
theorem lintegral_sq_lower_bound_of_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (residual : Ω → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (G : Set Ω) (hG : MeasurableSet G) (hprob : 3 / 4 ≤ μ.real G)
    (hlower : ∀ᵐ ω ∂μ, ω ∈ G → q ≤ residual ω) :
    ENNReal.ofReal (3 / 4 * q ^ 2) ≤ ∫⁻ ω, ENNReal.ofReal (residual ω ^ 2) ∂μ := by
  have hindicator : G.indicator (fun _ => ENNReal.ofReal (q ^ 2)) ≤ᵐ[μ]
      fun ω => ENNReal.ofReal (residual ω ^ 2) := by
    filter_upwards [hlower] with ω hω
    by_cases hωG : ω ∈ G
    · rw [Set.indicator_of_mem hωG]
      apply ENNReal.ofReal_le_ofReal
      have h := hω hωG
      nlinarith
    · rw [Set.indicator_of_notMem hωG]
      exact zero_le _
  have hintegral := lintegral_mono_ae hindicator
  rw [lintegral_indicator_const hG] at hintegral
  calc
    ENNReal.ofReal (3 / 4 * q ^ 2) ≤ ENNReal.ofReal (μ.real G * q ^ 2) := by
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hprob (sq_nonneg q))
    _ = ENNReal.ofReal (q ^ 2) * μ G := by
      rw [ENNReal.ofReal_mul (measureReal_nonneg), ofReal_measureReal, mul_comm]
    _ ≤ _ := hintegral

/-- A unit-sphere cover by selected sparse supports scales to every nonzero
input in the source subspace. -/
private theorem sparse_family_covers_scaled_input {d M k : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (U : Submodule ℝ (EuclideanRepresentation d))
    (family : Finset (Finset (Fin M))) (ε η : ℝ)
    (hcover : ∀ (x : EuclideanRepresentation d), x ∈ U → ‖x‖ = 1 →
      ∀ u : FeatureVector M, (nonzeroSupport u).card ≤ k →
        ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ ε →
        ∃ T ∈ family, ∃ v : FeatureVector M, nonzeroSupport v ⊆ T ∧
          ‖x - representationToEuclidean d (B.mulVec v)‖ ≤ η)
    (x : EuclideanRepresentation d) (hx : x ∈ U) (hxpos : 0 < ‖x‖)
    (u : FeatureVector M) (hu : (nonzeroSupport u).card ≤ k)
    (herr : ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ ε * ‖x‖) :
    ∃ T ∈ family, ∃ y ∈ euclideanColumnSpan B T, ‖x - y‖ ≤ η * ‖x‖ := by
  let xn := ‖x‖⁻¹ • x
  let un := ‖x‖⁻¹ • u
  have hxn : ‖xn‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    exact inv_mul_cancel₀ hxpos.ne'
  have hun : (nonzeroSupport un).card ≤ k :=
    (Finset.card_le_card (nonzeroSupport_smul_subset _ _)).trans hu
  have hnerr : ‖xn - representationToEuclidean d (B.mulVec un)‖ ≤ ε := by
    dsimp [xn, un]
    rw [Matrix.mulVec_smul, map_smul, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    have hbound := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hxpos.le)
    calc
      _ ≤ ‖x‖⁻¹ * (ε * ‖x‖) := hbound
      _ = ε := by field_simp
  obtain ⟨T, hT, v, hv, hve⟩ := hcover xn (U.smul_mem _ hx) hxn un hun hnerr
  let y := ‖x‖ • representationToEuclidean d (B.mulVec v)
  refine ⟨T, hT, y, ?_, ?_⟩
  · exact (euclideanColumnSpan B T).smul_mem _
      ((mem_euclideanColumnSpan_iff_exists_code B T _).mpr ⟨v, hv, rfl⟩)
  · have hxscale : ‖x‖ • xn = x := by
      dsimp [xn]
      rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
    calc
      ‖x - y‖ = ‖‖x‖ • (xn - representationToEuclidean d (B.mulVec v))‖ := by
        rw [smul_sub, hxscale]
      _ = ‖x‖ * ‖xn - representationToEuclidean d (B.mulVec v)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hxpos]
      _ ≤ ‖x‖ * η := mul_le_mul_of_nonneg_left hve hxpos.le
      _ = η * ‖x‖ := mul_comm _ _

universe u

/-- Under a uniform small-slab bound for a bounded coefficient law,
sufficiently small expected actual sparse reconstruction loss forces a
learned `K`-column span close to the source range in projector norm.

The compression bound `N` depends only on `K` and `γ`. The positive loss
threshold depends on the displayed scalar bounds and on the slab threshold,
but not on the ambient dimension or learned width. Coefficients and learned
codes may depend separately on the underlying random outcome. -/
theorem exists_uniform_sparse_subspace_incidence_threshold
    (K : ℕ) (γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) :
    ∃ N : ℕ, ∀ (a b R t δ : ℝ),
      0 < a → 0 < b → 0 < R → 0 < t → 0 < δ → δ < 1 →
      ∃ τ : ℝ, 0 < τ ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Z : Ω → EuclideanRepresentation K), Measurable Z →
          (∀ᵐ ω ∂μ, ‖Z ω‖ ≤ R) →
          (∀ v : EuclideanRepresentation K, ‖v‖ = 1 →
            μ.real {ω | |inner ℝ v (Z ω)| ≤ t} ≤ 1 / (4 * ((N : ℝ) + 1))) →
          ∀ (d M : ℕ) (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
            (B : Matrix (Fin d) (Fin M) ℝ) (code : Ω → FeatureVector M),
            Measurable code →
            (∀ z, a * ‖z‖ ≤ ‖F z‖) → (∀ z, ‖F z‖ ≤ b * ‖z‖) →
            (∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1) →
            SparseLowerStable B γ (2 * K) →
            (∀ ω, (nonzeroSupport (code ω)).card ≤ K) →
            (∫⁻ ω, ENNReal.ofReal
              (‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ^ 2) ∂μ)
              ≤ ENNReal.ofReal τ →
            ∃ T : Finset (Fin M), T.card = K ∧
              ‖(LinearMap.range F.toLinearMap).starProjection -
                (euclideanColumnSpan B T).starProjection‖ ≤ δ := by
  classical
  obtain ⟨N, hcompression⟩ := exists_uniform_sparse_image_compression K K γ hK hγ hγone
  refine ⟨N, ?_⟩
  intro a b R t δ ha hb hR ht hδ hδone
  let e := δ / 2
  have he : 0 < e := half_pos hδ
  have hehalf : e ≤ 1 / 2 := by dsimp [e]; linarith
  let η := min 1 (a * e * t / (2 * b * R))
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hηone : η ≤ 1 := min_le_left _ _
  have hηbound : η * b * R ≤ a * e * t / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * b * R by positivity)).mp
      (show η ≤ a * e * t / (2 * b * R) from min_le_right _ _)
    nlinarith
  let ε := γ / (16 * (K : ℝ)) * η ^ K
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hε : 0 < ε := by dsimp [ε]; positivity
  let q := ε * a * t
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q ^ 2 / 2, by positivity, ?_⟩
  intro Ω _ μ _ Z hZ hbounded hslab d M F B code _ hlower hupper hunit hstable hsparse hloss
  have hFinj : Function.Injective F := by
    intro z w hzw
    have h := hlower (z - w)
    rw [map_sub, hzw, sub_self, norm_zero] at h
    have hz : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hdim : Module.finrank ℝ (LinearMap.range F.toLinearMap) = K := by
    rw [LinearMap.finrank_range_of_inj hFinj]
    simp
  obtain ⟨family, hempty, hcard, hgood, hcover⟩ :=
    hcompression d M B Finset.univ (LinearMap.range F.toLinearMap) η hunit
      (hstable.on _) hdim.le hη hηone
  have hunitcover : ∀ (x : EuclideanRepresentation d), x ∈ LinearMap.range F.toLinearMap →
      ‖x‖ = 1 → ∀ u : FeatureVector M, (nonzeroSupport u).card ≤ K →
      ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ ε →
      ∃ T ∈ family, ∃ v : FeatureVector M, nonzeroSupport v ⊆ T ∧
        ‖x - representationToEuclidean d (B.mulVec v)‖ ≤ η := by
    intro x hx hxnorm u hu herr
    exact hcover x hx hxnorm u (Finset.subset_univ _) hu herr
  have hnear : ∃ T ∈ family, ∀ x ∈ LinearMap.range F.toLinearMap,
      ∃ y ∈ euclideanColumnSpan B T, ‖x - y‖ ≤ e * ‖x‖ := by
    by_contra hnone
    have hfar (T : family) : ¬ ∀ x ∈ LinearMap.range F.toLinearMap,
        ∃ y ∈ euclideanColumnSpan B T.1, ‖x - y‖ ≤ e * ‖x‖ :=
      fun h => hnone ⟨T.1, T.2, h⟩
    have hdir (T : family) : ∃ v : EuclideanRepresentation K, ‖v‖ = 1 ∧
        ∀ z y, y ∈ euclideanColumnSpan B T.1 →
          a * e * |inner ℝ v z| ≤ ‖F z - y‖ :=
      exists_direction_of_no_directed_approximation F (euclideanColumnSpan B T.1)
        a e ha he hlower (hfar T)
    choose direction hnorm hresidual using hdir
    let bad : Set Ω := ⋃ T : family, {ω | |inner ℝ (direction T) (Z ω)| ≤ t}
    let G := badᶜ
    have hmeasbad : MeasurableSet bad := by
      apply MeasurableSet.iUnion
      intro T
      exact measurableSet_le
        ((continuous_const.inner continuous_id).abs.measurable.comp hZ) measurable_const
    have hprob : 3 / 4 ≤ μ.real G := by
      apply measureReal_compl_finite_slabs_ge μ Z hZ direction N
        (by simpa using hcard) t
      intro T
      exact hslab (direction T) (hnorm T)
    have hlowerloss : ∀ᵐ ω ∂μ, ω ∈ G →
        q ≤ ‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ := by
      filter_upwards [hbounded] with ω hωbounded
      intro hωG
      have haway (T : family) : t < |inner ℝ (direction T) (Z ω)| := by
        by_contra hn
        exact hωG (Set.mem_iUnion.mpr ⟨T, le_of_not_gt hn⟩)
      let Tzero : family := ⟨∅, hempty⟩
      have hZlarge : t < ‖Z ω‖ := by
        have hcauchy := abs_real_inner_le_norm (direction Tzero) (Z ω)
        rw [hnorm Tzero, one_mul] at hcauchy
        exact (haway Tzero).trans_le hcauchy
      have hFpositive : 0 < ‖F (Z ω)‖ :=
        (mul_pos ha (ht.trans hZlarge)).trans_le (hlower (Z ω))
      have hnotclose : ¬ ‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ≤
          ε * ‖F (Z ω)‖ := by
        intro hclose
        obtain ⟨T, hT, y, hy, happrox⟩ := sparse_family_covers_scaled_input
          B (LinearMap.range F.toLinearMap) family ε η hunitcover
          (F (Z ω)) ⟨Z ω, rfl⟩ hFpositive (code ω) (hsparse ω) hclose
        have hres := hresidual ⟨T, hT⟩ (Z ω) y hy
        have hstrict : a * e * t < a * e * |inner ℝ (direction ⟨T, hT⟩) (Z ω)| :=
          mul_lt_mul_of_pos_left (haway ⟨T, hT⟩) (mul_pos ha he)
        have hsize : ‖F (Z ω)‖ ≤ b * R :=
          (hupper (Z ω)).trans (mul_le_mul_of_nonneg_left hωbounded hb.le)
        have hsmall := (mul_le_mul_of_nonneg_left hsize hη.le)
        have hpositive : 0 < a * e * t := by positivity
        nlinarith
      have hresgt := lt_of_not_ge hnotclose
      have hFlower : a * t ≤ ‖F (Z ω)‖ :=
        (mul_le_mul_of_nonneg_left hZlarge.le ha.le).trans (hlower (Z ω))
      have hqle := mul_le_mul_of_nonneg_left hFlower hε.le
      dsimp [q]
      nlinarith
    have hlargeLoss := lintegral_sq_lower_bound_of_event μ
      (fun ω => ‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖)
      q hq.le G hmeasbad.compl hprob hlowerloss
    have hscalar := ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ q ^ 2 / 2) |>.mp
      (hlargeLoss.trans hloss)
    nlinarith [sq_pos_of_pos hq]
  obtain ⟨T, hT, hTnear⟩ := hnear
  have hVcard : Module.finrank ℝ (euclideanColumnSpan B T) ≤ T.card := by
    rw [euclideanColumnSpan, (representationToEuclidean d).toLinearEquiv.finrank_map_eq]
    exact finrank_columnSpan_le_card B T
  have hVdim : Module.finrank ℝ (euclideanColumnSpan B T) ≤
      Module.finrank ℝ (LinearMap.range F.toLinearMap) := by
    rw [hdim]
    exact hVcard.trans (hgood T hT).2
  obtain ⟨hdimeq, hproj⟩ := projector_bound_of_one_sided_approximation
    (LinearMap.range F.toLinearMap) (euclideanColumnSpan B T) e he.le hehalf hVdim hTnear
  refine ⟨T, ?_, ?_⟩
  · have hKcard : K ≤ T.card := by rw [hdim] at hdimeq; omega
    exact Nat.le_antisymm (hgood T hT).2 hKcard
  · have htwo : 2 * e = δ := by dsimp [e]; ring
    simpa only [htwo] using hproj

end PKG26AtomicFeatures
