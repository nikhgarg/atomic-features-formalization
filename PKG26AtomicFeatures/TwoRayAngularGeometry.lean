import PKG26AtomicFeatures.NonnegativeLeastSquaresIsometry
import PKG26AtomicFeatures.NonnegativeLeastSquaresActiveSet
import PKG26AtomicFeatures.TwoColumnStability
import PKG26AtomicFeatures.StableSupportIntersections
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Reflections of a two-ray cone

Reflecting a two-ray cone toward a strict separating half-plane preserves
feasibility of its portion in that half-plane. The argument is expressed in
the actual two-column Gram coordinates, without an angular enclosure premise.
-/

namespace PKG26AtomicFeatures

open scoped InnerProductSpace Topology

private theorem reflected_first_coordinate_pos
    (c p q u v : ℝ) (hc : c < 1) (hsum : p + q < 0)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hN : 0 < p ^ 2 + q ^ 2 + 2 * c * p * q)
    (hD : 0 < u * (p + c * q) + v * (c * p + q)) :
    0 < u - 2 * (u * (p + c * q) + v * (c * p + q)) * p /
      (p ^ 2 + q ^ 2 + 2 * c * p * q) := by
  by_cases hp : p < 0
  · have hneg : 2 * (u * (p + c * q) + v * (c * p + q)) * p /
        (p ^ 2 + q ^ 2 + 2 * c * p * q) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hp) hN
    linarith
  have hp0 : 0 ≤ p := le_of_not_gt hp
  by_cases hpzero : p = 0
  · have hu' : 0 < u := by
      by_contra hn
      have huzero : u = 0 := le_antisymm (le_of_not_gt hn) hu
      have hq : q < 0 := by linarith
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hv hq.le
      simp only [huzero, hpzero, zero_mul, mul_zero, zero_add] at hD
      linarith
    simpa only [hpzero, mul_zero, zero_div, sub_zero] using hu'
  have hp' : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpzero)
  have hq : q < -p := by linarith
  have hqminus : 0 < q ^ 2 - p ^ 2 := by nlinarith
  have hother : c * p + q < 0 := by nlinarith
  have huv : 0 < u ∨ 0 < v := by
    by_contra hn
    push Not at hn
    have huzero := le_antisymm hn.1 hu
    have hvzero := le_antisymm hn.2 hv
    simp only [huzero, hvzero, zero_mul, add_zero, lt_self_iff_false] at hD
  have hnum : 0 < (q ^ 2 - p ^ 2) * u + (-2 * p * (c * p + q)) * v := by
    have hfactor : 0 < -2 * p * (c * p + q) :=
      mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by norm_num) hp') hother
    rcases huv with hu' | hv'
    · exact add_pos_of_pos_of_nonneg (mul_pos hqminus hu') (mul_nonneg hfactor.le hv)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hqminus.le hu) (mul_pos hfactor hv')
  have heq : u - 2 * (u * (p + c * q) + v * (c * p + q)) * p /
      (p ^ 2 + q ^ 2 + 2 * c * p * q) =
      ((q ^ 2 - p ^ 2) * u + (-2 * p * (c * p + q)) * v) /
        (p ^ 2 + q ^ 2 + 2 * c * p * q) := by
    apply (eq_div_iff hN.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hN.ne']
    ring
  rw [heq]
  exact div_pos hnum hN

/-- In Gram coordinates, reflecting a nonzero vector on the positive
side of a separator yields strictly positive coefficients whenever the
sum of the two unit generators lies on its negative side. -/
theorem two_ray_reflection_coefficients_pos
    (c p q u v : ℝ) (hc : c < 1) (hsum : p + q < 0)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hN : 0 < p ^ 2 + q ^ 2 + 2 * c * p * q)
    (hD : 0 < u * (p + c * q) + v * (c * p + q)) :
    0 < u - 2 * (u * (p + c * q) + v * (c * p + q)) * p /
      (p ^ 2 + q ^ 2 + 2 * c * p * q) ∧
    0 < v - 2 * (u * (p + c * q) + v * (c * p + q)) * q /
      (p ^ 2 + q ^ 2 + 2 * c * p * q) := by
  refine ⟨reflected_first_coordinate_pos c p q u v hc hsum hu hv hN hD, ?_⟩
  have h := reflected_first_coordinate_pos c q p v u hc (by linarith) hv hu
    (by nlinarith only [hN]) (by nlinarith only [hD])
  convert h using 1
  ring

/-- The closed-half-plane version also includes vectors fixed by the
reflection, whose separator coordinate is zero. -/
theorem two_ray_reflection_coefficients_nonneg
    (c p q u v : ℝ) (hc : c < 1) (hsum : p + q < 0)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hN : 0 < p ^ 2 + q ^ 2 + 2 * c * p * q)
    (hD : 0 ≤ u * (p + c * q) + v * (c * p + q)) :
    0 ≤ u - 2 * (u * (p + c * q) + v * (c * p + q)) * p /
      (p ^ 2 + q ^ 2 + 2 * c * p * q) ∧
    0 ≤ v - 2 * (u * (p + c * q) + v * (c * p + q)) * q /
      (p ^ 2 + q ^ 2 + 2 * c * p * q) := by
  rcases eq_or_lt_of_le hD with heq | hpos
  · rw [← heq]
    simpa only [mul_zero, zero_mul, zero_div, sub_zero] using And.intro hu hv
  · exact ⟨(two_ray_reflection_coefficients_pos c p q u v hc hsum hu hv hN hpos).1.le,
      (two_ray_reflection_coefficients_pos c p q u v hc hsum hu hv hN hpos).2.le⟩

/-- Reflection across the hyperplane normal to `h`, written in a form
that makes its action on actual coefficient vectors explicit. -/
theorem reflection_orthogonal_hyperplane_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (h x : E) :
    (ℝ ∙ h)ᗮ.reflection x = x - (2 * inner ℝ h x / ‖h‖ ^ 2) • h := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  module

/-- Reflecting the positive half of an actual two-column cone gives
feasible coefficients, and strictly positive coefficients away from the
separating hyperplane. The separator and its center inequality are actual
ambient geometric data. -/
theorem two_column_reflection_preserves_positive_half_cone {d : ℕ}
    (B : Matrix (Fin d) (Fin 2) ℝ) (hunit : HasUnitEuclideanColumns B)
    (hstable : SparseLowerStable B (1 / 2) 4)
    (h : EuclideanRepresentation d) (hh : h ∈ euclideanColumnSpan B Finset.univ)
    (hcenter : inner ℝ h (representationToEuclidean d (B.col 0) +
      representationToEuclidean d (B.col 1)) < 0)
    (u : FeatureVector 2) (hu : ∀ j, 0 ≤ u j)
    (hside : 0 ≤ inner ℝ h (representationToEuclidean d (B.mulVec u))) :
    ∃ v : FeatureVector 2, (∀ j, 0 ≤ v j) ∧
      representationToEuclidean d (B.mulVec v) =
        (ℝ ∙ h)ᗮ.reflection (representationToEuclidean d (B.mulVec u)) ∧
      (0 < inner ℝ h (representationToEuclidean d (B.mulVec u)) → ∀ j, 0 < v j) := by
  classical
  obtain ⟨p, _, hp⟩ := (mem_euclideanColumnSpan_iff_exists_code B Finset.univ h).mp hh
  let c := inner ℝ (representationToEuclidean d (B.col 0))
    (representationToEuclidean d (B.col 1))
  have hcabs := (two_column_half_stable_iff_abs_inner_le_three_quarters B hunit).mp hstable
  change |c| ≤ 3 / 4 at hcabs
  have hc : c < 1 := by have hc' := (abs_le.mp hcabs).2; linarith
  have hcneg : -1 < c := by have hc' := (abs_le.mp hcabs).1; linarith
  have hcenterformula : inner ℝ h (representationToEuclidean d (B.col 0) +
      representationToEuclidean d (B.col 1)) = (1 + c) * (p 0 + p 1) := by
    rw [← hp, two_column_euclidean_mulVec]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hunit 0, hunit 1,
      real_inner_comm (representationToEuclidean d (B.col 1))
        (representationToEuclidean d (B.col 0))]
    dsimp [c]
    simp only [real_inner_comm (representationToEuclidean d (B.col 1))
      (representationToEuclidean d (B.col 0))]
    ring
  have hsum : p 0 + p 1 < 0 := by
    rw [hcenterformula] at hcenter
    by_contra hn
    have hprod := mul_nonneg (by linarith : 0 ≤ 1 + c) (le_of_not_gt hn)
    linarith
  have hnorm : ‖h‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + 2 * c * p 0 * p 1 := by
    rw [← hp, two_column_unit_gram_norm_sq B hunit p]
    dsimp [c]
    simp only [real_inner_comm (representationToEuclidean d (B.col 1))
      (representationToEuclidean d (B.col 0))]
    ring
  have hne : h ≠ 0 := by
    intro hz
    simp only [hz, inner_zero_left, lt_self_iff_false] at hcenter
  have hnormpos : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hN : 0 < (p 0) ^ 2 + (p 1) ^ 2 + 2 * c * p 0 * p 1 := hnorm ▸ hnormpos
  have hinner : inner ℝ h (representationToEuclidean d (B.mulVec u)) =
      u 0 * (p 0 + c * p 1) + u 1 * (c * p 0 + p 1) := by
    rw [← hp, two_column_euclidean_mulVec, two_column_euclidean_mulVec]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hunit 0, hunit 1,
      real_inner_comm (representationToEuclidean d (B.col 1))
        (representationToEuclidean d (B.col 0))]
    dsimp [c]
    simp only [real_inner_comm (representationToEuclidean d (B.col 1))
      (representationToEuclidean d (B.col 0))]
    ring
  let a := 2 * inner ℝ h (representationToEuclidean d (B.mulVec u)) / ‖h‖ ^ 2
  let v : FeatureVector 2 := u - a • p
  have hv (j : Fin 2) : v j = u j -
      2 * (u 0 * (p 0 + c * p 1) + u 1 * (c * p 0 + p 1)) * p j /
        ((p 0) ^ 2 + (p 1) ^ 2 + 2 * c * p 0 * p 1) := by
    change u j - a * p j = _
    dsimp [a]
    rw [hinner, hnorm]
    ring
  have hnonneg := two_ray_reflection_coefficients_nonneg c (p 0) (p 1) (u 0) (u 1)
    hc hsum (hu 0) (hu 1) hN (by rwa [← hinner])
  refine ⟨v, ?_, ?_, ?_⟩
  · intro j
    rw [hv]
    fin_cases j
    · exact hnonneg.1
    · exact hnonneg.2
  · rw [reflection_orthogonal_hyperplane_apply]
    dsimp only [v]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, map_sub, map_smul, hp]
  · intro hpos j
    have hpositive := two_ray_reflection_coefficients_pos c (p 0) (p 1) (u 0) (u 1)
      hc hsum (hu 0) (hu 1) hN (by rwa [← hinner])
    rw [hv]
    fin_cases j
    · exact hpositive.1
    · exact hpositive.2

/-- Reflection in a direction of the learned span preserves that actual
span. This statement is independent of cone or sign assumptions. -/
theorem euclideanColumnSpan_reflected_dictionary_eq {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (h : EuclideanRepresentation d)
    (hh : h ∈ euclideanColumnSpan B Finset.univ) :
    euclideanColumnSpan (isometricDictionary (ℝ ∙ h)ᗮ.reflection B) Finset.univ =
      euclideanColumnSpan B Finset.univ := by
  classical
  let V := euclideanColumnSpan B Finset.univ
  let R := (ℝ ∙ h)ᗮ.reflection
  have hpreserve (x : EuclideanRepresentation d) (hx : x ∈ V) : R x ∈ V := by
    rw [show R x = x - (2 * inner ℝ h x / ‖h‖ ^ 2) • h from
      reflection_orthogonal_hyperplane_apply h x]
    exact V.sub_mem hx (V.smul_mem _ hh)
  ext x
  constructor
  · intro hx
    obtain ⟨u, _, hu⟩ := (mem_euclideanColumnSpan_iff_exists_code _ _ x).mp hx
    rw [isometricDictionary_synthesis] at hu
    rw [← hu]
    apply hpreserve
    exact (mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mpr
      ⟨u, Finset.subset_univ _, rfl⟩
  · intro hx
    obtain ⟨u, _, hu⟩ := (mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mp
      (hpreserve x hx)
    apply (mem_euclideanColumnSpan_iff_exists_code _ _ x).mpr
    refine ⟨u, Finset.subset_univ _, ?_⟩
    rw [isometricDictionary_synthesis, hu]
    exact Submodule.reflection_reflection _ x

/-- An actual NNLS code whose coordinates are all positive reconstructs
the orthogonal projection onto the full learned span. -/
theorem IsNonnegativeLeastSquaresCode.full_positive_synthesis_eq_projection {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {x : EuclideanRepresentation d} {u : FeatureVector m}
    (hu : IsNonnegativeLeastSquaresCode B x u) (hpos : ∀ j, 0 < u j) :
    (euclideanColumnSpan B Finset.univ).starProjection x =
      representationToEuclidean d (B.mulVec u) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mpr
      ⟨u, Finset.subset_univ _, rfl⟩
  · intro y hy
    obtain ⟨v, _, hv⟩ := (mem_euclideanColumnSpan_iff_exists_code B Finset.univ y).mp hy
    rw [← hv, euclidean_mulVec_eq_sum B v, inner_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [real_inner_smul_right]
    change v j * nnlsResidualColumnInner B x u j = 0
    rw [hu.columnResidual_eq_zero_of_pos j (hpos j), mul_zero]

/-- Reflection strictly improves a fit lying on the opposite side of its
hyperplane from the data point. The comparison is between actual squared
Euclidean residuals. -/
theorem reflection_residual_sq_lt_of_opposite_sides {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h x y : E) (hx : 0 < inner ℝ h x) (hy : inner ℝ h y < 0) :
    ‖x - (ℝ ∙ h)ᗮ.reflection y‖ ^ 2 < ‖x - y‖ ^ 2 := by
  have hh : h ≠ 0 := by intro hh; simp only [hh, inner_zero_left, lt_self_iff_false] at hx
  have hnorm : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hh)
  have hformula : inner ℝ x ((ℝ ∙ h)ᗮ.reflection y) =
      inner ℝ x y - 2 * inner ℝ h y * inner ℝ h x / ‖h‖ ^ 2 := by
    rw [reflection_orthogonal_hyperplane_apply, inner_sub_right, real_inner_smul_right,
      real_inner_comm x h]
    ring
  have hnegative : 2 * inner ℝ h y * inner ℝ h x / ‖h‖ ^ 2 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by nlinarith) hx) hnorm
  rw [norm_sub_sq_real, norm_sub_sq_real, LinearIsometryEquiv.norm_map, hformula]
  linarith

/-- The reflected dictionary does no worse on a point in the strict
positive half-plane. If its old fit has positive separator coordinate and
is strictly clipped, the improvement is strict. The final global argument
chooses a separator avoiding the finitely many zero fit coordinates. -/
theorem two_column_reflection_nnls_comparison {d : ℕ}
    (B : Matrix (Fin d) (Fin 2) ℝ) (hunit : HasUnitEuclideanColumns B)
    (hstable : SparseLowerStable B (1 / 2) 4)
    (h : EuclideanRepresentation d) (hh : h ∈ euclideanColumnSpan B Finset.univ)
    (hcenter : inner ℝ h (representationToEuclidean d (B.col 0) +
      representationToEuclidean d (B.col 1)) < 0)
    (x : EuclideanRepresentation d) (hx : 0 < inner ℝ h x)
    (u v : FeatureVector 2) (hu : IsNonnegativeLeastSquaresCode B x u)
    (hv : IsNonnegativeLeastSquaresCode (isometricDictionary (ℝ ∙ h)ᗮ.reflection B) x v) :
    ‖x - representationToEuclidean d
        ((isometricDictionary (ℝ ∙ h)ᗮ.reflection B).mulVec v)‖ ^ 2 ≤
      ‖x - representationToEuclidean d (B.mulVec u)‖ ^ 2 ∧
    (inner ℝ h (representationToEuclidean d (B.mulVec u)) ≠ 0 →
      (euclideanColumnSpan B Finset.univ).starProjection x ≠
        representationToEuclidean d (B.mulVec u) →
      ‖x - representationToEuclidean d
          ((isometricDictionary (ℝ ∙ h)ᗮ.reflection B).mulVec v)‖ ^ 2 <
        ‖x - representationToEuclidean d (B.mulVec u)‖ ^ 2) := by
  let R := (ℝ ∙ h)ᗮ.reflection
  let C := isometricDictionary R B
  change ‖x - representationToEuclidean d (C.mulVec v)‖ ^ 2 ≤
      ‖x - representationToEuclidean d (B.mulVec u)‖ ^ 2 ∧ _
  by_cases hside : 0 ≤ inner ℝ h (representationToEuclidean d (B.mulVec u))
  · obtain ⟨w, hw, hweq, hwpos⟩ := two_column_reflection_preserves_positive_half_cone
      B hunit hstable h hh hcenter u hu.1 hside
    have hCw : representationToEuclidean d (C.mulVec w) =
        representationToEuclidean d (B.mulVec u) := by
      rw [isometricDictionary_synthesis, hweq]
      exact Submodule.reflection_reflection _ _
    have hbound := hv.2 w hw
    rw [hCw] at hbound
    refine ⟨hbound, ?_⟩
    intro hne hclip
    have hpositive := hwpos (lt_of_le_of_ne hside (Ne.symm hne))
    by_contra hn
    have hequal : ‖x - representationToEuclidean d (C.mulVec v)‖ ^ 2 =
        ‖x - representationToEuclidean d (B.mulVec u)‖ ^ 2 :=
      le_antisymm hbound (le_of_not_gt hn)
    have hwmin : IsNonnegativeLeastSquaresCode C x w := by
      refine ⟨hw, fun q hq => ?_⟩
      rw [hCw, ← hequal]
      exact hv.2 q hq
    have hprojection := hwmin.full_positive_synthesis_eq_projection hpositive
    rw [euclideanColumnSpan_reflected_dictionary_eq B h hh, hCw] at hprojection
    exact hclip hprojection
  · have hnegative := lt_of_not_ge hside
    have hstrict := reflection_residual_sq_lt_of_opposite_sides h x
      (representationToEuclidean d (B.mulVec u)) hx hnegative
    have hbound := hv.2 u hu.1
    simp only [isometricDictionary_synthesis] at hbound
    have hlt := hbound.trans_lt hstrict
    constructor
    · simpa only [C, isometricDictionary_synthesis] using hlt.le
    · intro _ _
      simpa only [isometricDictionary_synthesis] using hlt

/-- A finite collection of nonzero cone fits can be kept off a strict
separating hyperplane. Perturbation along a center with positive inner
product against every fit preserves all strict data-side inequalities. -/
theorem exists_strict_separator_avoiding_finite_fits
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Finite ι]
    (V : Submodule ℝ E) (h center : E) (hh : h ∈ V) (hcenterV : center ∈ V)
    (data fit : ι → E) (hcenter : inner ℝ h center < 0)
    (hdata : ∀ i, 0 < inner ℝ h (data i))
    (hfit : ∀ i, 0 < inner ℝ center (fit i)) :
    ∃ h' : E, h' ∈ V ∧ inner ℝ h' center < 0 ∧
      (∀ i, 0 < inner ℝ h' (data i)) ∧ (∀ i, inner ℝ h' (fit i) ≠ 0) := by
  have hcont (x : E) : Continuous (fun t : ℝ => inner ℝ (h + t • center) x) := by
    fun_prop
  have hcenter_event : ∀ᶠ t : ℝ in 𝓝 0, inner ℝ (h + t • center) center < 0 := by
    apply (hcont center).continuousAt.eventually_lt continuousAt_const
    simpa only [zero_smul, add_zero] using hcenter
  have hdata_event : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < inner ℝ (h + t • center) (data i) := by
    apply Filter.eventually_all.mpr
    intro i
    apply continuousAt_const.eventually_lt (hcont (data i)).continuousAt
    simpa only [zero_smul, add_zero] using hdata i
  have hfit_event : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,
      inner ℝ h (fit i) = 0 ∨ inner ℝ (h + t • center) (fit i) ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : inner ℝ h (fit i) = 0
    · exact Filter.Eventually.of_forall fun _ => Or.inl hi
    · have hi' : (fun t : ℝ => inner ℝ (h + t • center) (fit i)) 0 ≠ 0 := by
        simpa only [zero_smul, add_zero] using hi
      exact ((hcont (fit i)).continuousAt.eventually_ne hi').mono fun _ ht => Or.inr ht
  have hevent := (hcenter_event.and (hdata_event.and hfit_event)).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have ht_event : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, htc, htd, htf⟩ := (ht_event.and hevent).exists
  refine ⟨h + t • center, V.add_mem hh (V.smul_mem t hcenterV), htc, htd, ?_⟩
  intro i
  rcases htf i with hi | hi
  · rw [inner_add_left, real_inner_smul_left, hi, zero_add]
    exact ne_of_gt (mul_pos ht (hfit i))
  · exact hi

end PKG26AtomicFeatures
