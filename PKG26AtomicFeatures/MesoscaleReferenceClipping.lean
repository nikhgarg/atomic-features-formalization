import PKG26AtomicFeatures.MesoscaleClippingObstruction
import PKG26AtomicFeatures.TwoRayAngularGeometry
import PKG26AtomicFeatures.MesoscalePlaneStationarity

/-!
# Strict clipping at actual mesoscale reference minimizers

The finite reference risk controls all three actual NNLS fits. Feasible
dictionary reflections supply a global comparison, in addition to the
rotation stationarity condition. These two conditions determine the strict
dominant active sets without assuming an angular position of the dictionary.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators InnerProductSpace

/-- The actual canonical code of a finite reference point. -/
noncomputable def mesoscaleReferenceCode (B : Matrix (Fin 3) (Fin 2) ℝ)
    (hstable : SparseLowerStable B (1 / 2) 4) (s : Fin 3) : FeatureVector 2 :=
  nonnegativeLeastSquaresCode B (1 / 2) (by norm_num)
    (hstable.global_bound_of_width_le (by norm_num)) (mesoscaleReferenceInput s)

theorem mesoscaleReferenceCode_isNNLS (B : Matrix (Fin 3) (Fin 2) ℝ)
    (hstable : SparseLowerStable B (1 / 2) 4) (s : Fin 3) :
    IsNonnegativeLeastSquaresCode B (mesoscaleReferenceInput s)
      (mesoscaleReferenceCode B hstable s) :=
  nonnegativeLeastSquaresCode_isMinimizer B (1 / 2) (by norm_num)
    (hstable.global_bound_of_width_le (by norm_num)) (mesoscaleReferenceInput s)

theorem mesoscaleReferenceWeight_pos (s : Fin 3) : 0 < mesoscaleReferenceWeight s := by
  fin_cases s <;> norm_num [mesoscaleReferenceWeight]

/-- A zero fit of any reference point by itself exceeds the strict
benchmark attained by every actual global minimizer. -/
theorem IsMesoscaleReferenceMinimizer.reference_fit_ne_zero
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable) (s : Fin 3) :
    representationToEuclidean 3 (B.mulVec (mesoscaleReferenceCode B hstable s)) ≠ 0 := by
  intro hz
  have hterm : mesoscaleReferenceWeight s *
      ‖mesoscaleReferenceInput s - representationToEuclidean 3
        (B.mulVec (mesoscaleReferenceCode B hstable s))‖ ^ 2 ≤
      mesoscaleReferenceNNLSRisk B hstable := by
    exact Finset.single_le_sum (f := fun j => mesoscaleReferenceWeight j *
      ‖mesoscaleReferenceInput j - representationToEuclidean 3
        (B.mulVec (mesoscaleReferenceCode B hstable j))‖ ^ 2)
      (fun j _ => mul_nonneg (mesoscaleReferenceWeight_pos j).le (sq_nonneg _))
      (Finset.mem_univ s)
  rw [hz, sub_zero] at hterm
  have hlt := hterm.trans_lt hmin.referenceRisk_lt
  have hnorm (x : EuclideanRepresentation 3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, add_assoc]
  rw [hnorm] at hlt
  fin_cases s <;> norm_num [mesoscaleReferenceWeight, mesoscaleReferenceInput,
    representationToEuclidean, Matrix.cons_val_two] at hlt

/-- Every nonzero nonnegative fit has positive correlation with the sum
of the two unit learned columns. -/
theorem two_column_fit_inner_center_pos {d : ℕ}
    (B : Matrix (Fin d) (Fin 2) ℝ) (hunit : HasUnitEuclideanColumns B)
    (hstable : SparseLowerStable B (1 / 2) 4)
    (u : FeatureVector 2) (hu : ∀ j, 0 ≤ u j)
    (hne : representationToEuclidean d (B.mulVec u) ≠ 0) :
    0 < inner ℝ
      (representationToEuclidean d (B.col 0) + representationToEuclidean d (B.col 1))
      (representationToEuclidean d (B.mulVec u)) := by
  have hsum : 0 < u 0 + u 1 := by
    by_contra hn
    have hu0 : u 0 = 0 := by have h := hu 0; have h' := hu 1; linarith
    have hu1 : u 1 = 0 := by have h := hu 0; have h' := hu 1; linarith
    apply hne
    simp only [two_column_euclidean_mulVec, hu0, hu1, zero_smul, add_zero]
  have hcorr := (abs_le.mp
    ((two_column_half_stable_iff_abs_inner_le_three_quarters B hunit).mp hstable)).1
  have hformula : inner ℝ
      (representationToEuclidean d (B.col 0) + representationToEuclidean d (B.col 1))
      (representationToEuclidean d (B.mulVec u)) =
      (1 + inner ℝ (representationToEuclidean d (B.col 0))
        (representationToEuclidean d (B.col 1))) * (u 0 + u 1) := by
    rw [two_column_euclidean_mulVec]
    simp only [inner_add_left, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hunit 0, hunit 1,
      real_inner_comm (representationToEuclidean d (B.col 1))
        (representationToEuclidean d (B.col 0))]
    ring
  rw [hformula]
  exact mul_pos (by linarith) hsum

/-- A strict separator of all three data points from the learned cone
center would give an actually feasible dictionary with strictly smaller
reference risk. Finite perturbation removes all zero fitted coordinates
before the reflected-NNLS comparison is applied. -/
theorem IsMesoscaleReferenceMinimizer.no_strict_data_separator
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable)
    (hclip : ∃ s : Fin 3, (euclideanColumnSpan B Finset.univ).starProjection
      (mesoscaleReferenceInput s) ≠
        representationToEuclidean 3 (B.mulVec (mesoscaleReferenceCode B hstable s)))
    (h : EuclideanRepresentation 3) (hh : h ∈ euclideanColumnSpan B Finset.univ)
    (hcenter : inner ℝ h (representationToEuclidean 3 (B.col 0) +
      representationToEuclidean 3 (B.col 1)) < 0)
    (hdata : ∀ s, 0 < inner ℝ h (mesoscaleReferenceInput s)) : False := by
  classical
  let center := representationToEuclidean 3 (B.col 0) + representationToEuclidean 3 (B.col 1)
  let fit := fun s => representationToEuclidean 3 (B.mulVec (mesoscaleReferenceCode B hstable s))
  have hcenterV : center ∈ euclideanColumnSpan B Finset.univ := by
    have heq : center = representationToEuclidean 3 (B.mulVec ![1, 1]) := by
      simp only [two_column_euclidean_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_smul, center]
    rw [heq]
    exact (mem_euclideanColumnSpan_iff_exists_code _ _ _).mpr
      ⟨![1, 1], Finset.subset_univ _, rfl⟩
  obtain ⟨h', hh', hc', hd', hf'⟩ := exists_strict_separator_avoiding_finite_fits
    (euclideanColumnSpan B Finset.univ) h center hh hcenterV mesoscaleReferenceInput fit
    hcenter hdata (fun s => two_column_fit_inner_center_pos B hmin.1 hstable _
      (mesoscaleReferenceCode_isNNLS B hstable s).1 (hmin.reference_fit_ne_zero s))
  let R := (ℝ ∙ h')ᗮ.reflection
  let C := isometricDictionary R B
  have hC := hstable.isometricDictionary R
  have hcompare (s : Fin 3) := two_column_reflection_nnls_comparison B hmin.1 hstable
    h' hh' hc' (mesoscaleReferenceInput s) (hd' s)
    (mesoscaleReferenceCode B hstable s) (mesoscaleReferenceCode C hC s)
    (mesoscaleReferenceCode_isNNLS B hstable s) (mesoscaleReferenceCode_isNNLS C hC s)
  have hstrict : mesoscaleReferenceNNLSRisk C hC < mesoscaleReferenceNNLSRisk B hstable := by
    unfold mesoscaleReferenceNNLSRisk
    apply Finset.sum_lt_sum
    · intro s _
      exact mul_le_mul_of_nonneg_left (hcompare s).1 (mesoscaleReferenceWeight_pos s).le
    · obtain ⟨s, hs⟩ := hclip
      exact ⟨s, Finset.mem_univ s,
        mul_lt_mul_of_pos_left ((hcompare s).2 (hf' s) hs) (mesoscaleReferenceWeight_pos s)⟩
  exact (not_lt_of_ge (hmin.2 C (hmin.1.isometricDictionary R) hC)) hstrict

-- Finite-dimensional rank and orthogonal-complement elaboration uses a larger local budget.
set_option maxHeartbeats 800000 in
/-- Every feasible width-two dictionary in the reference ambient space
has an actual unit plane normal. Its learned projector is exactly removal
of the normal component. -/
theorem two_column_three_dimensional_unit_normal
    (B : Matrix (Fin 3) (Fin 2) ℝ) (hstable : SparseLowerStable B (1 / 2) 4) :
    ∃ n : EuclideanRepresentation 3, ‖n‖ = 1 ∧
      (∀ j, inner ℝ n (representationToEuclidean 3 (B.col j)) = 0) ∧
      euclideanColumnSpan B Finset.univ = (ℝ ∙ n)ᗮ ∧
      ∀ x, (euclideanColumnSpan B Finset.univ).starProjection x = mesoscaleNormalProjection n x := by
  classical
  let V := euclideanColumnSpan B Finset.univ
  have hdim : Module.finrank ℝ V = 2 := by
    simpa using finrank_euclideanColumnSpan_eq_card B Finset.univ
      (hstable.linearIndependent (by norm_num) _ (by simp))
  have horthdim : Module.finrank ℝ Vᗮ = 1 := by
    have h := V.finrank_add_finrank_orthogonal
    rw [hdim] at h
    have hambient : Module.finrank ℝ (EuclideanRepresentation 3) = 3 := by simp
    rw [hambient] at h
    omega
  letI : Nontrivial Vᗮ := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ Vᗮ)
  obtain ⟨v, hv⟩ := exists_ne (0 : Vᗮ)
  have hv' : (v : EuclideanRepresentation 3) ≠ 0 := by
    intro hz
    exact hv (Subtype.ext hz)
  let n := NormedSpace.normalize (v : EuclideanRepresentation 3)
  have hn : ‖n‖ = 1 := NormedSpace.norm_normalize hv'
  have hnmem : n ∈ Vᗮ := Vᗮ.smul_mem _ v.property
  have hnne : n ≠ 0 := by intro hz; simp [hz] at hn
  have hline : ℝ ∙ n = Vᗮ := Submodule.eq_of_le_of_finrank_eq
    (Submodule.span_le.mpr (by simpa only [Set.singleton_subset_iff] using hnmem))
    (by rw [finrank_span_singleton hnne, horthdim])
  have hV : V = (ℝ ∙ n)ᗮ := by rw [hline, Submodule.orthogonal_orthogonal]
  refine ⟨n, hn, ?_, hV, ?_⟩
  · intro j
    apply (V.mem_orthogonal' n).mp hnmem
    exact (mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mpr
      ⟨Pi.single j 1, Finset.subset_univ _, by simp⟩
  · intro x
    change V.starProjection x = _
    rw [hV, Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton]
    simp only [hn, one_pow, RCLike.ofReal_one, div_one]
    rfl

/-- At an actual optimum the unit normal can be oriented with negative
parent coordinate and two strictly positive child coordinates. -/
theorem IsMesoscaleReferenceMinimizer.exists_oriented_normal
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable) :
    ∃ n : EuclideanRepresentation 3, ‖n‖ = 1 ∧ n 0 < 0 ∧ 0 < n 1 ∧ 0 < n 2 ∧
      (∀ j, inner ℝ n (representationToEuclidean 3 (B.col j)) = 0) ∧
      ∀ x, (euclideanColumnSpan B Finset.univ).starProjection x = mesoscaleNormalProjection n x := by
  obtain ⟨n, hn, horth, _, hproj⟩ := two_column_three_dimensional_unit_normal B hstable
  obtain ⟨h12, h01⟩ := mesoscale_low_referenceRisk_normal_signs B hstable
    hmin.referenceRisk_lt n hn horth
  rcases mul_pos_iff.mp h12 with hpos | hneg
  · refine ⟨n, hn, ?_, hpos.1, hpos.2, horth, hproj⟩
    nlinarith only [h01, hpos.1]
  · refine ⟨-n, by simpa using hn, ?_, by simpa using hneg.1,
      by simpa using hneg.2, ?_, ?_⟩
    · change -(n 0) < 0
      nlinarith only [h01, hneg.1]
    · intro j
      rw [inner_neg_left, horth, neg_zero]
    · intro x
      rw [hproj]
      simp only [mesoscaleNormalProjection, inner_neg_left, smul_neg, neg_smul, neg_neg]

/-- The unavoidable clipping conclusion holds for the actual learned
span projector, with its normal constructed from the feasible dictionary. -/
theorem IsMesoscaleReferenceMinimizer.exists_strictly_clipped_reference
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable) :
    ∃ s : Fin 3, (euclideanColumnSpan B Finset.univ).starProjection
      (mesoscaleReferenceInput s) ≠
        representationToEuclidean 3 (B.mulVec (mesoscaleReferenceCode B hstable s)) := by
  obtain ⟨n, hn, horth, _, hproj⟩ := two_column_three_dimensional_unit_normal B hstable
  obtain ⟨s, hs⟩ := hmin.exists_projection_not_mem_cone n hn horth
  refine ⟨s, ?_⟩
  intro heq
  rw [hproj] at heq
  apply hs
  rw [heq]
  exact ⟨representationToEuclidean 2 (mesoscaleReferenceCode B hstable s),
    (mesoscaleReferenceCode_isNNLS B hstable s).1, by simp⟩

/-- The reference inputs express the normal with the exact source
coefficients. This identity is before any learned projection. -/
theorem mesoscale_reference_normal_decomposition (n : EuclideanRepresentation 3) :
    n 1 • mesoscaleReferenceInput 0 + n 2 • mesoscaleReferenceInput 1 =
      n + (-n 0 + (n 1 + n 2) / 20) • mesoscaleReferenceInput 2 := by
  ext j
  fin_cases j <;> norm_num [mesoscaleReferenceInput, representationToEuclidean,
    Matrix.cons_val_two] <;> first | rfl | ring

/-- Projecting the source relation makes the parent projection a strict
positive combination of the two dominant projections when the normal has
its forced sign pattern. -/
theorem mesoscale_projected_parent_relation
    (Q : EuclideanRepresentation 3 →L[ℝ] EuclideanRepresentation 3)
    (n : EuclideanRepresentation 3) (hQn : Q n = 0) :
    (-n 0 + (n 1 + n 2) / 20) • Q (mesoscaleReferenceInput 2) =
      n 1 • Q (mesoscaleReferenceInput 0) + n 2 • Q (mesoscaleReferenceInput 1) := by
  have h := congrArg Q (mesoscale_reference_normal_decomposition n)
  simpa only [map_add, map_smul, hQn, zero_add] using h.symm

/-- The two projected dominant inputs remain independent for every
normal with the forced signs. In particular the parent lies between two
actual distinct projected directions. -/
theorem mesoscale_projected_dominants_linearIndependent
    (n : EuclideanRepresentation 3) (hn0 : n 0 < 0) (hn1 : 0 < n 1) (hn2 : 0 < n 2) :
    LinearIndependent ℝ (fun i : Fin 2 =>
      mesoscaleNormalProjection n (mesoscaleReferenceInput i.castSucc)) := by
  have hcancel (a b : ℝ)
      (heq : a • mesoscaleNormalProjection n (mesoscaleReferenceInput 0) +
        b • mesoscaleNormalProjection n (mesoscaleReferenceInput 1) = 0) : a = 0 ∧ b = 0 := by
    let t := a * inner ℝ n (mesoscaleReferenceInput 0) +
      b * inner ℝ n (mesoscaleReferenceInput 1)
    have hraw : a • mesoscaleReferenceInput 0 + b • mesoscaleReferenceInput 1 = t • n := by
      apply sub_eq_zero.mp
      calc
        _ = a • mesoscaleNormalProjection n (mesoscaleReferenceInput 0) +
            b • mesoscaleNormalProjection n (mesoscaleReferenceInput 1) := by
          dsimp [mesoscaleNormalProjection, t]
          module
        _ = 0 := heq
    have h0 := congrArg (fun x : EuclideanRepresentation 3 => x 0) hraw
    have h1 := congrArg (fun x : EuclideanRepresentation 3 => x 1) hraw
    have h2 := congrArg (fun x : EuclideanRepresentation 3 => x 2) hraw
    norm_num [mesoscaleReferenceInput, representationToEuclidean, Matrix.cons_val_two] at h0 h1 h2
    have hfactor : t * (n 0 - (n 1 + n 2) / 20) = 0 := by nlinarith only [h0, h1, h2]
    have ht : t = 0 := (mul_eq_zero.mp hfactor).resolve_right (by linarith)
    exact ⟨by simpa only [ht, zero_mul] using h1,
      by simpa only [ht, zero_mul] using h2⟩
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    have h := hcancel 0 1 (by simpa only [zero_smul, one_smul, zero_add] using hz)
    norm_num at h
  · intro a ha
    have h := hcancel (-1) a (by
      change a • mesoscaleNormalProjection n (mesoscaleReferenceInput 1) =
        mesoscaleNormalProjection n (mesoscaleReferenceInput 0) at ha
      rw [ha, neg_one_smul, neg_add_cancel])
    norm_num at h

private theorem exists_positive_weights_of_negative_coordinate
    (a b : ℝ) (hneg : a < 0 ∨ b < 0) :
    ∃ p q : ℝ, 0 < p ∧ 0 < q ∧ p * a + q * b < 0 := by
  have hone (a b : ℝ) (ha : a < 0) : ∃ q : ℝ, 0 < q ∧ a + q * b < 0 := by
    let q := -a / (|b| + 1)
    have hden : 0 < |b| + 1 := by positivity
    have hq : 0 < q := div_pos (neg_pos.mpr ha) hden
    have heq : q * (|b| + 1) = -a := div_mul_cancel₀ _ hden.ne'
    have hlt := mul_lt_mul_of_pos_left (show b < |b| + 1 by linarith [le_abs_self b]) hq
    rw [heq] at hlt
    exact ⟨q, hq, by linarith⟩
  rcases hneg with ha | hb
  · obtain ⟨q, hq, h⟩ := hone a b ha
    exact ⟨1, q, zero_lt_one, hq, by simpa only [one_mul] using h⟩
  · obtain ⟨p, hp, h⟩ := hone b a hb
    exact ⟨p, 1, hp, zero_lt_one, by simpa only [one_mul, add_comm] using h⟩

/-- A vector dual to one of two independent directions can be constructed
by orthogonally removing the other direction and rescaling. -/
theorem exists_inner_dual_of_not_mem_line {d : ℕ}
    (y₀ y₁ : EuclideanRepresentation d) (hnot : y₀ ∉ ℝ ∙ y₁) :
    ∃ r : EuclideanRepresentation d, r ∈ Submodule.span ℝ {y₀, y₁} ∧
      inner ℝ r y₀ = 1 ∧ inner ℝ r y₁ = 0 := by
  let w := (ℝ ∙ y₁)ᗮ.starProjection y₀
  have hwne : w ≠ 0 := by
    intro hz
    have hmem := (Submodule.starProjection_apply_eq_zero_iff (ℝ ∙ y₁)ᗮ).mp hz
    rw [Submodule.orthogonal_orthogonal] at hmem
    exact hnot hmem
  have hwpos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hwne)
  have hwmem : w ∈ (ℝ ∙ y₁)ᗮ := Submodule.starProjection_apply_mem _ _
  have horth : inner ℝ w y₁ = 0 :=
    ((ℝ ∙ y₁).mem_orthogonal' w).mp hwmem y₁ (Submodule.mem_span_singleton_self y₁)
  have hself : inner ℝ w y₀ = ‖w‖ ^ 2 := by
    have h := (ℝ ∙ y₁)ᗮ.starProjection_inner_eq_zero y₀ w hwmem
    change inner ℝ (y₀ - w) w = 0 at h
    rw [inner_sub_left, real_inner_comm w y₀, real_inner_self_eq_norm_sq] at h
    linarith
  have hwspan : w ∈ Submodule.span ℝ {y₀, y₁} := by
    rw [show w = y₀ - (ℝ ∙ y₁).starProjection y₀ from
      Submodule.starProjection_orthogonal_val y₀, Submodule.starProjection_singleton]
    exact (Submodule.span ℝ {y₀, y₁}).sub_mem
      (Submodule.subset_span (by simp))
      ((Submodule.span ℝ {y₀, y₁}).smul_mem _ (Submodule.subset_span (by simp)))
  refine ⟨(‖w‖ ^ 2)⁻¹ • w, (Submodule.span ℝ {y₀, y₁}).smul_mem _ hwspan, ?_, ?_⟩
  · rw [real_inner_smul_left, hself, inv_mul_cancel₀ hwpos.ne']
  · rw [real_inner_smul_left, horth, mul_zero]

/-- If either coordinate in an independent two-direction basis is
negative, a separator is strictly positive on both generators and strictly
negative on that vector. All separators remain in the generated plane. -/
theorem exists_strict_separator_of_negative_two_coordinates {d : ℕ}
    (y : Fin 2 → EuclideanRepresentation d) (hlin : LinearIndependent ℝ y)
    (a b : ℝ) (hneg : a < 0 ∨ b < 0) :
    ∃ h : EuclideanRepresentation d, h ∈ Submodule.span ℝ {y 0, y 1} ∧
      0 < inner ℝ h (y 0) ∧ 0 < inner ℝ h (y 1) ∧
      inner ℝ h (a • y 0 + b • y 1) < 0 := by
  have hnot₀ : y 0 ∉ ℝ ∙ y 1 := by
    simpa only [Set.image_singleton] using
      hlin.notMem_span_image (s := {1}) (show (0 : Fin 2) ∉ ({1} : Set (Fin 2)) by simp)
  have hnot₁ : y 1 ∉ ℝ ∙ y 0 := by
    simpa only [Set.image_singleton] using
      hlin.notMem_span_image (s := {0}) (show (1 : Fin 2) ∉ ({0} : Set (Fin 2)) by simp)
  obtain ⟨r₀, hr₀, h00, h01⟩ := exists_inner_dual_of_not_mem_line (y 0) (y 1) hnot₀
  obtain ⟨r₁, hr₁, h11, h10⟩ := exists_inner_dual_of_not_mem_line (y 1) (y 0) hnot₁
  obtain ⟨p, q, hp, hq, hnegative⟩ := exists_positive_weights_of_negative_coordinate a b hneg
  refine ⟨p • r₀ + q • r₁, ?_, ?_, ?_, ?_⟩
  · exact (Submodule.span ℝ {y 0, y 1}).add_mem
      ((Submodule.span ℝ {y 0, y 1}).smul_mem p hr₀)
      ((Submodule.span ℝ {y 0, y 1}).smul_mem q (by simpa only [Set.pair_comm] using hr₁))
  · simpa only [inner_add_left, real_inner_smul_left, h00, h10, mul_one, mul_zero, add_zero] using hp
  · simpa only [inner_add_left, real_inner_smul_left, h01, h11, mul_one, mul_zero, zero_add] using hq
  · simpa only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, h00, h01, h10, h11, mul_one, mul_zero, add_zero, zero_add, mul_comm]
      using hnegative

-- The finite-dimensional span and separation argument needs a larger local elaboration budget.
set_option maxHeartbeats 800000 in
/-- Global reference optimality places the actual learned center in the
positive wedge of the two independent dominant projections. The parent
projection is a strict positive combination of those same projections.
The wedge conclusion follows from a derived separator and an actual
feasible reflection comparison, not from rotation stationarity alone. -/
theorem IsMesoscaleReferenceMinimizer.projected_data_geometry
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable) :
    let Q := (euclideanColumnSpan B Finset.univ).starProjection
    LinearIndependent ℝ (fun i : Fin 2 => Q (mesoscaleReferenceInput i.castSucc)) ∧
      ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
        Q (mesoscaleReferenceInput 2) =
          α • Q (mesoscaleReferenceInput 0) + β • Q (mesoscaleReferenceInput 1) ∧
        ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
          representationToEuclidean 3 (B.col 0) + representationToEuclidean 3 (B.col 1) =
            a • Q (mesoscaleReferenceInput 0) + b • Q (mesoscaleReferenceInput 1) := by
  classical
  let V := euclideanColumnSpan B Finset.univ
  let Q := V.starProjection
  let y : Fin 2 → EuclideanRepresentation 3 := fun i => Q (mesoscaleReferenceInput i.castSucc)
  let center := representationToEuclidean 3 (B.col 0) + representationToEuclidean 3 (B.col 1)
  obtain ⟨n, hn, hn0, hn1, hn2, horth, hproj⟩ := hmin.exists_oriented_normal
  have hQn : Q n = 0 := by
    change V.starProjection n = 0
    rw [hproj, mesoscaleNormalProjection, real_inner_self_eq_norm_sq, hn]
    norm_num
  have hlin : LinearIndependent ℝ y := by
    have h := mesoscale_projected_dominants_linearIndependent n hn0 hn1 hn2
    simpa only [y, Q, V, hproj] using h
  let κ := -n 0 + (n 1 + n 2) / 20
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hrelation := mesoscale_projected_parent_relation Q n hQn
  change κ • Q (mesoscaleReferenceInput 2) = n 1 • y 0 + n 2 • y 1 at hrelation
  have hparent : Q (mesoscaleReferenceInput 2) = (n 1 / κ) • y 0 + (n 2 / κ) • y 1 := by
    have h := congrArg (fun x => κ⁻¹ • x) hrelation
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ hκ.ne', one_smul, div_eq_mul_inv,
      mul_comm] using h
  refine ⟨hlin, n 1 / κ, n 2 / κ, div_pos hn1 hκ, div_pos hn2 hκ, hparent, ?_⟩
  have hdimV : Module.finrank ℝ V = 2 := by
    simpa using finrank_euclideanColumnSpan_eq_card B Finset.univ
      (hstable.linearIndependent (by norm_num) _ (by simp))
  have hspan : Submodule.span ℝ (Set.range y) = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact V.starProjection_apply_mem _
    · rw [finrank_span_eq_card hlin, hdimV]
      simp
  have hrange : Set.range y = {y 0, y 1} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact or_congr eq_comm eq_comm
  have hcenterV : center ∈ V := by
    apply V.add_mem
    · exact (mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mpr
        ⟨Pi.single 0 1, Finset.subset_univ _, by simp⟩
    · exact (mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mpr
        ⟨Pi.single 1 1, Finset.subset_univ _, by simp⟩
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp
    (show center ∈ Submodule.span ℝ {y 0, y 1} by rw [← hrange, hspan]; exact hcenterV)
  have hnonneg : 0 ≤ a ∧ 0 ≤ b := by
    by_contra h
    have hneg : a < 0 ∨ b < 0 := by
      by_cases ha : 0 ≤ a
      · exact Or.inr (lt_of_not_ge (fun hb => h ⟨ha, hb⟩))
      · exact Or.inl (lt_of_not_ge ha)
    obtain ⟨h, hh, h0, h1, hc⟩ := exists_strict_separator_of_negative_two_coordinates y hlin a b hneg
    have hhV : h ∈ V := by rwa [← hrange, hspan] at hh
    have hcenter : inner ℝ h center < 0 := by rwa [hab] at hc
    have hinner (s : Fin 3) : inner ℝ h (Q (mesoscaleReferenceInput s)) =
        inner ℝ h (mesoscaleReferenceInput s) := by
      rw [← V.inner_starProjection_left_eq_right, V.starProjection_eq_self_iff.mpr hhV]
    have hdata : ∀ s, 0 < inner ℝ h (mesoscaleReferenceInput s) := by
      intro s
      rw [← hinner s]
      fin_cases s
      · exact h0
      · exact h1
      · change 0 < inner ℝ h (Q (mesoscaleReferenceInput 2))
        rw [hparent, inner_add_right, real_inner_smul_right, real_inner_smul_right]
        exact add_pos (mul_pos (div_pos hn1 hκ) h0) (mul_pos (div_pos hn2 hκ) h1)
    exact hmin.no_strict_data_separator hmin.exists_strictly_clipped_reference h hhV hcenter hdata
  exact ⟨a, b, hnonneg.1, hnonneg.2, hab.symm⟩

/-- The signed first-order contribution of a two-ray NNLS fit to common rotation. -/
noncomputable def twoRayNNLSRotationScore {d : ℕ} (B : Matrix (Fin d) (Fin 2) ℝ)
    (x : EuclideanRepresentation d) (u : FeatureVector 2) : ℝ :=
  u 0 * nnlsResidualColumnInner B x u 1 - u 1 * nnlsResidualColumnInner B x u 0

theorem twoRayNNLSRotationScore_neg_iff {d : ℕ} {B : Matrix (Fin d) (Fin 2) ℝ}
    {x : EuclideanRepresentation d} {u : FeatureVector 2}
    (hu : IsNonnegativeLeastSquaresCode B x u) :
    twoRayNNLSRotationScore B x u < 0 ↔
      0 < u 0 ∧ nnlsResidualColumnInner B x u 1 < 0 := by
  have hn0 := hu.1 0
  have hn1 := hu.1 1
  have hg0 := hu.columnResidual_nonpos 0
  have hg1 := hu.columnResidual_nonpos 1
  constructor
  · intro h
    have hm : u 0 * nnlsResidualColumnInner B x u 1 < 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hn1 hg0
      dsimp [twoRayNNLSRotationScore] at h
      linarith
    exact ⟨lt_of_le_of_ne hn0 (by intro hz; simp [← hz] at hm),
      lt_of_le_of_ne hg1 (by intro hz; simp [hz] at hm)⟩
  · rintro ⟨h0, h1⟩
    dsimp [twoRayNNLSRotationScore]
    rw [hu.columnResidual_eq_zero_of_pos 0 h0, mul_zero, sub_zero]
    exact mul_neg_of_pos_of_neg h0 h1

theorem twoRayNNLSRotationScore_pos_iff {d : ℕ} {B : Matrix (Fin d) (Fin 2) ℝ}
    {x : EuclideanRepresentation d} {u : FeatureVector 2}
    (hu : IsNonnegativeLeastSquaresCode B x u) :
    0 < twoRayNNLSRotationScore B x u ↔
      0 < u 1 ∧ nnlsResidualColumnInner B x u 0 < 0 := by
  have hn0 := hu.1 0
  have hn1 := hu.1 1
  have hg0 := hu.columnResidual_nonpos 0
  have hg1 := hu.columnResidual_nonpos 1
  constructor
  · intro h
    have hm : u 1 * nnlsResidualColumnInner B x u 0 < 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hn0 hg1
      dsimp [twoRayNNLSRotationScore] at h
      linarith
    exact ⟨lt_of_le_of_ne hn1 (by intro hz; simp [← hz] at hm),
      lt_of_le_of_ne hg0 (by intro hz; simp [hz] at hm)⟩
  · rintro ⟨h1, h0⟩
    dsimp [twoRayNNLSRotationScore]
    rw [hu.columnResidual_eq_zero_of_pos 1 h1, mul_zero, zero_sub]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg h1 h0)

/-- With a nonzero fit, a vanishing rotation score means that the full
span projection already belongs to the nonnegative cone. -/
theorem nnls_scores_zero_of_rotation_zero {d : ℕ} {B : Matrix (Fin d) (Fin 2) ℝ}
    {x : EuclideanRepresentation d} {u : FeatureVector 2}
    (hu : IsNonnegativeLeastSquaresCode B x u)
    (hne : representationToEuclidean d (B.mulVec u) ≠ 0)
    (hzero : twoRayNNLSRotationScore B x u = 0) :
    ∀ j, nnlsResidualColumnInner B x u j = 0 := by
  have hpos : 0 < u 0 ∨ 0 < u 1 := by
    by_contra h
    push Not at h
    have h0 := le_antisymm h.1 (hu.1 0)
    have h1 := le_antisymm h.2 (hu.1 1)
    apply hne
    simp [two_column_euclidean_mulVec, h0, h1]
  rcases hpos with h0 | h1
  · have hg0 := hu.columnResidual_eq_zero_of_pos 0 h0
    have hg1 : nnlsResidualColumnInner B x u 1 = 0 := by
      dsimp [twoRayNNLSRotationScore] at hzero
      rw [hg0, mul_zero, sub_zero] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left h0.ne'
    intro j; fin_cases j <;> assumption
  · have hg1 := hu.columnResidual_eq_zero_of_pos 1 h1
    have hg0 : nnlsResidualColumnInner B x u 0 = 0 := by
      dsimp [twoRayNNLSRotationScore] at hzero
      rw [hg1, mul_zero, zero_sub, neg_eq_zero] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left h1.ne'
    intro j; fin_cases j <;> assumption

theorem nnls_synthesis_eq_projection_of_scores_zero {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {x : EuclideanRepresentation d} {u : FeatureVector m}
    (hscore : ∀ j, nnlsResidualColumnInner B x u j = 0) :
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
    rw [hscore, mul_zero]

/-- The column difference tests which side of the cone bisector contains
an input with a strict active set. -/
noncomputable def twoRayInputDifference {d : ℕ} (B : Matrix (Fin d) (Fin 2) ℝ)
    (x : EuclideanRepresentation d) : ℝ :=
  inner ℝ x (representationToEuclidean d (B.col 1) - representationToEuclidean d (B.col 0))

theorem twoRayInputDifference_formula {d : ℕ} (B : Matrix (Fin d) (Fin 2) ℝ)
    (hunit : HasUnitEuclideanColumns B) (x : EuclideanRepresentation d) (u : FeatureVector 2) :
    twoRayInputDifference B x =
      (1 - inner ℝ (representationToEuclidean d (B.col 0))
        (representationToEuclidean d (B.col 1))) * (u 1 - u 0) +
        nnlsResidualColumnInner B x u 1 - nnlsResidualColumnInner B x u 0 := by
  simp only [twoRayInputDifference, nnlsResidualColumnInner, two_column_euclidean_mulVec,
    inner_sub_right, inner_sub_left, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hunit 0, hunit 1, one_pow]
  rw [real_inner_comm (representationToEuclidean d (B.col 1))
    (representationToEuclidean d (B.col 0))]
  ring

theorem twoRayInputDifference_sign {d : ℕ} {B : Matrix (Fin d) (Fin 2) ℝ}
    (hunit : HasUnitEuclideanColumns B) (hc : inner ℝ (representationToEuclidean d (B.col 0))
      (representationToEuclidean d (B.col 1)) < 1)
    {x : EuclideanRepresentation d} {u : FeatureVector 2}
    (hu : IsNonnegativeLeastSquaresCode B x u) :
    (twoRayNNLSRotationScore B x u < 0 → twoRayInputDifference B x < 0) ∧
    (0 < twoRayNNLSRotationScore B x u → 0 < twoRayInputDifference B x) := by
  rw [twoRayInputDifference_formula B hunit x u]
  constructor
  · intro h
    obtain ⟨hu0, hg1⟩ := (twoRayNNLSRotationScore_neg_iff hu).mp h
    rw [hu.eq_zero_of_columnResidual_neg 1 hg1, hu.columnResidual_eq_zero_of_pos 0 hu0]
    have := mul_pos (sub_pos.mpr hc) hu0
    nlinarith
  · intro h
    obtain ⟨hu1, hg0⟩ := (twoRayNNLSRotationScore_pos_iff hu).mp h
    rw [hu.eq_zero_of_columnResidual_neg 0 hg0, hu.columnResidual_eq_zero_of_pos 1 hu1]
    have := mul_pos (sub_pos.mpr hc) hu1
    nlinarith

theorem nnls_rotation_zero_of_nonnegative_projection_code {d : ℕ}
    {B : Matrix (Fin d) (Fin 2) ℝ} {x : EuclideanRepresentation d} {u : FeatureVector 2}
    (hu : IsNonnegativeLeastSquaresCode B x u) (w : FeatureVector 2) (hw : ∀ j, 0 ≤ w j)
    (hproj : (euclideanColumnSpan B Finset.univ).starProjection x =
      representationToEuclidean d (B.mulVec w)) : twoRayNNLSRotationScore B x u = 0 := by
  let V := euclideanColumnSpan B Finset.univ
  have hs (j : Fin 2) : nnlsResidualColumnInner B x w j = 0 := by
    dsimp [nnlsResidualColumnInner]
    rw [← hproj]
    exact V.starProjection_inner_eq_zero x _
      ((mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mpr
        ⟨Pi.single j 1, Finset.subset_univ _, by simp⟩)
  have hwmin : IsNonnegativeLeastSquaresCode B x w :=
    (isNonnegativeLeastSquaresCode_iff_kkt B x w).mpr
      ⟨hw, fun j => (hs j).le, fun j => by rw [hs j, mul_zero]⟩
  have hdist := nonnegativeLeastSquares_synthesis_distance_le hu hwmin
  rw [sub_self, norm_zero] at hdist
  have heq := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hdist (norm_nonneg _)))
  have hsu (j : Fin 2) : nnlsResidualColumnInner B x u j = 0 := by
    dsimp [nnlsResidualColumnInner] at hs ⊢
    rw [heq]
    exact hs j
  simp [twoRayNNLSRotationScore, hsu]

/-- Adding a nonnegative bisector component cannot create a strict
rotation sign absent from the other component. -/
theorem twoRayNNLSRotationScore_sign_of_center_combination {d : ℕ}
    {B : Matrix (Fin d) (Fin 2) ℝ} (hunit : HasUnitEuclideanColumns B)
    (hc : inner ℝ (representationToEuclidean d (B.col 0))
      (representationToEuclidean d (B.col 1)) < 1)
    {x y : EuclideanRepresentation d} {u v : FeatureVector 2}
    (hu : IsNonnegativeLeastSquaresCode B x u) (hv : IsNonnegativeLeastSquaresCode B y v)
    (hne : representationToEuclidean d (B.mulVec u) ≠ 0)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hproj : (euclideanColumnSpan B Finset.univ).starProjection y =
      a • (representationToEuclidean d (B.col 0) + representationToEuclidean d (B.col 1)) +
        b • (euclideanColumnSpan B Finset.univ).starProjection x) :
    (twoRayNNLSRotationScore B y v < 0 → twoRayNNLSRotationScore B x u < 0) ∧
    (0 < twoRayNNLSRotationScore B y v → 0 < twoRayNNLSRotationScore B x u) := by
  let V := euclideanColumnSpan B Finset.univ
  have hdmem : representationToEuclidean d (B.col 1) - representationToEuclidean d (B.col 0) ∈ V := by
    apply V.sub_mem
    · exact (mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mpr
        ⟨Pi.single 1 1, Finset.subset_univ _, by simp⟩
    · exact (mem_euclideanColumnSpan_iff_exists_code B Finset.univ _).mpr
        ⟨Pi.single 0 1, Finset.subset_univ _, by simp⟩
  have hi (z : EuclideanRepresentation d) : twoRayInputDifference B (V.starProjection z) =
      twoRayInputDifference B z := by
    dsimp [twoRayInputDifference]
    rw [V.inner_starProjection_left_eq_right, V.starProjection_eq_self_iff.mpr hdmem]
  have hdiff : twoRayInputDifference B y = b * twoRayInputDifference B x := by
    rw [← hi y, hproj]
    unfold twoRayInputDifference
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    change a * inner ℝ _ _ + b * twoRayInputDifference B (V.starProjection x) = _
    rw [hi x]
    have hz : inner ℝ
        (representationToEuclidean d (B.col 0) + representationToEuclidean d (B.col 1))
        (representationToEuclidean d (B.col 1) - representationToEuclidean d (B.col 0)) = 0 := by
      simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq, hunit 0, hunit 1, one_pow]
      rw [real_inner_comm (representationToEuclidean d (B.col 0))
        (representationToEuclidean d (B.col 1))]
      ring
    rw [hz, mul_zero, zero_add]
    rfl
  have hzero (hz : twoRayNNLSRotationScore B x u = 0) : twoRayNNLSRotationScore B y v = 0 := by
    have hpx := nnls_synthesis_eq_projection_of_scores_zero
      (nnls_scores_zero_of_rotation_zero hu hne hz)
    apply nnls_rotation_zero_of_nonnegative_projection_code hv (fun j => a + b * u j)
      (fun j => add_nonneg ha (mul_nonneg hb (hu.1 j)))
    rw [hproj, hpx, two_column_euclidean_mulVec, two_column_euclidean_mulVec]
    module
  constructor
  · intro hy
    rcases lt_trichotomy (twoRayNNLSRotationScore B x u) 0 with hx | hx | hx
    · exact hx
    · have := hzero hx; linarith
    · have hx' := (twoRayInputDifference_sign hunit hc hu).2 hx
      have hy' := (twoRayInputDifference_sign hunit hc hv).1 hy
      rw [hdiff] at hy'
      exact (not_lt_of_ge (mul_nonneg hb hx'.le) hy').elim
  · intro hy
    rcases lt_trichotomy (twoRayNNLSRotationScore B x u) 0 with hx | hx | hx
    · have hx' := (twoRayInputDifference_sign hunit hc hu).1 hx
      have hy' := (twoRayInputDifference_sign hunit hc hv).2 hy
      rw [hdiff] at hy'
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hb hx'.le) hy').elim
    · have := hzero hx; linarith
    · exact hx

/-- A positive combination of two endpoints lies between their
nonnegative center combination and at least one endpoint. -/
theorem positive_pair_combination_eq_center_endpoint
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y : Fin 2 → E) (a b α β : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a + b) (hα : 0 < α) (hβ : 0 < β) :
    ∃ (i : Fin 2) (l μ : ℝ), 0 ≤ l ∧ 0 ≤ μ ∧
      α • y 0 + β • y 1 = l • (a • y 0 + b • y 1) + μ • y i := by
  by_cases hcmp : α * b ≤ β * a
  · have ha' : 0 < a := by
      by_contra h
      have haz : a = 0 := le_antisymm (le_of_not_gt h) ha
      have hb' : 0 < b := by linarith
      have := mul_pos hα hb'
      rw [haz, mul_zero] at hcmp
      linarith
    refine ⟨1, α / a, β - α / a * b, (div_pos hα ha').le, ?_, ?_⟩
    · apply sub_nonneg.mpr
      rw [div_mul_eq_mul_div, div_le_iff₀ ha']
      exact hcmp
    · rw [smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ ha'.ne']
      module
  · have hb' : 0 < b := by
      by_contra h
      have hbz : b = 0 := le_antisymm (le_of_not_gt h) hb
      have := mul_nonneg hβ.le ha
      rw [hbz, mul_zero] at hcmp
      exact hcmp this
    refine ⟨0, β / b, α - β / b * a, (div_pos hβ hb').le, ?_, ?_⟩
    · apply sub_nonneg.mpr
      rw [div_mul_eq_mul_div, div_le_iff₀ hb']
      exact (lt_of_not_ge hcmp).le
    · rw [smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ hb'.ne']
      module

/-- Positive weighted stationarity and inheritance of the parent's
strict sign force opposite, nonzero dominant signs. -/
theorem opposite_dominant_signs_of_stationarity
    (d₀ d₁ d₂ w₀ w₁ w₂ : ℝ) (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hstation : w₀ * d₀ + w₁ * d₁ + w₂ * d₂ = 0)
    (hne : d₀ ≠ 0 ∨ d₁ ≠ 0 ∨ d₂ ≠ 0)
    (hneg : d₂ < 0 → d₀ < 0 ∨ d₁ < 0)
    (hpos : 0 < d₂ → 0 < d₀ ∨ 0 < d₁) :
    (d₀ < 0 ∧ 0 < d₁) ∨ (d₁ < 0 ∧ 0 < d₀) := by
  have hpositive : 0 < d₀ ∨ 0 < d₁ := by
    by_contra h
    push Not at h
    have hd₂ : d₂ ≤ 0 := le_of_not_gt (fun h₂ => by rcases hpos h₂ with h₀ | h₁ <;> linarith)
    have hm₀ := mul_nonpos_of_nonneg_of_nonpos hw₀.le h.1
    have hm₁ := mul_nonpos_of_nonneg_of_nonpos hw₁.le h.2
    have hm₂ := mul_nonpos_of_nonneg_of_nonpos hw₂.le hd₂
    have hz₀ : d₀ = 0 := by nlinarith
    have hz₁ : d₁ = 0 := by nlinarith
    have hz₂ : d₂ = 0 := by nlinarith
    rcases hne with hn | hn | hn <;> contradiction
  have hnegative : d₀ < 0 ∨ d₁ < 0 := by
    by_contra h
    push Not at h
    have hd₂ : 0 ≤ d₂ := le_of_not_gt (fun h₂ => by rcases hneg h₂ with h₀ | h₁ <;> linarith)
    have hm₀ := mul_nonneg hw₀.le h.1
    have hm₁ := mul_nonneg hw₁.le h.2
    have hm₂ := mul_nonneg hw₂.le hd₂
    rcases hpositive with hp | hp <;> nlinarith
  rcases hnegative with hn | hn
  · left; refine ⟨hn, ?_⟩
    exact hpositive.resolve_left (not_lt_of_ge hn.le)
  · right; refine ⟨hn, ?_⟩
    exact hpositive.resolve_right (not_lt_of_ge hn.le)

/-- At every feasible global reference minimizer the two dominant inputs
are strictly clipped to distinct learned rays. Positivity and strict
inactivity are consequences of the actual risk minimum. -/
theorem IsMesoscaleReferenceMinimizer.strict_dominant_clipping
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable) :
    ∃ e : Equiv.Perm (Fin 2), ∀ s : Fin 2,
      0 < mesoscaleReferenceCode B hstable s.castSucc (e s) ∧
        ∀ j, j ≠ e s → nnlsResidualColumnInner B (mesoscaleReferenceInput s.castSucc)
          (mesoscaleReferenceCode B hstable s.castSucc) j < 0 := by
  let Q := (euclideanColumnSpan B Finset.univ).starProjection
  let u := mesoscaleReferenceCode B hstable
  let d : Fin 3 → ℝ := fun s => twoRayNNLSRotationScore B (mesoscaleReferenceInput s) (u s)
  let y : Fin 2 → EuclideanRepresentation 3 := fun i => Q (mesoscaleReferenceInput i.castSucc)
  let center := representationToEuclidean 3 (B.col 0) + representationToEuclidean 3 (B.col 1)
  have hu (s : Fin 3) : IsNonnegativeLeastSquaresCode B (mesoscaleReferenceInput s) (u s) :=
    mesoscaleReferenceCode_isNNLS B hstable s
  have hfit (s : Fin 3) : representationToEuclidean 3 (B.mulVec (u s)) ≠ 0 :=
    hmin.reference_fit_ne_zero s
  obtain ⟨_, α, β, hα, hβ, hp, a, b, ha, hb, hc⟩ := hmin.projected_data_geometry
  change Q (mesoscaleReferenceInput 2) = α • y 0 + β • y 1 at hp
  change center = a • y 0 + b • y 1 at hc
  have hcenter : center ≠ 0 := by
    have h := two_column_fit_inner_center_pos B hmin.1 hstable (u 0) (hu 0).1 (hfit 0)
    intro hz
    change 0 < inner ℝ center _ at h
    rw [hz, inner_zero_left] at h
    exact lt_irrefl _ h
  have hab : 0 < a + b := by
    by_contra h
    have haz : a = 0 := by linarith
    have hbz : b = 0 := by linarith
    apply hcenter
    simp [hc, haz, hbz]
  obtain ⟨i, l, r, hl, hr, heq⟩ :=
    positive_pair_combination_eq_center_endpoint y a b α β ha hb hab hα hβ
  have hparent : Q (mesoscaleReferenceInput 2) = l • center + r • y i := by
    rw [hp, heq, ← hc]
  have hcorr : inner ℝ (representationToEuclidean 3 (B.col 0))
      (representationToEuclidean 3 (B.col 1)) < 1 := by
    have h := (abs_le.mp ((two_column_half_stable_iff_abs_inner_le_three_quarters B hmin.1).mp hstable)).2
    linarith
  have htransfer := twoRayNNLSRotationScore_sign_of_center_combination hmin.1 hcorr
    (hu i.castSucc) (hu 2) (hfit i.castSucc) l r hl hr hparent
  have hneg : d 2 < 0 → d 0 < 0 ∨ d 1 < 0 := by
    intro h
    have hi := htransfer.1 h
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hpos : 0 < d 2 → 0 < d 0 ∨ 0 < d 1 := by
    intro h
    have hi := htransfer.2 h
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hne : d 0 ≠ 0 ∨ d 1 ≠ 0 ∨ d 2 ≠ 0 := by
    obtain ⟨s, hs⟩ := hmin.exists_strictly_clipped_reference
    have hds : d s ≠ 0 := by
      intro hz
      exact hs (nnls_synthesis_eq_projection_of_scores_zero
        (nnls_scores_zero_of_rotation_zero (hu s) (hfit s) hz))
    fin_cases s
    · exact Or.inl hds
    · exact Or.inr (Or.inl hds)
    · exact Or.inr (Or.inr hds)
  have hstation : mesoscaleReferenceWeight 0 * d 0 + mesoscaleReferenceWeight 1 * d 1 +
      mesoscaleReferenceWeight 2 * d 2 = 0 := by
    have h := hmin.plane_stationarity
    change ∑ s, mesoscaleReferenceWeight s * d s = 0 at h
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, add_assoc] using h
  have hopposite := opposite_dominant_signs_of_stationarity (d 0) (d 1) (d 2)
    (mesoscaleReferenceWeight 0) (mesoscaleReferenceWeight 1) (mesoscaleReferenceWeight 2)
    (mesoscaleReferenceWeight_pos 0) (mesoscaleReferenceWeight_pos 1)
    (mesoscaleReferenceWeight_pos 2) hstation hne hneg hpos
  rcases hopposite with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · have hclip0 := (twoRayNNLSRotationScore_neg_iff (hu 0)).mp h0
    have hclip1 := (twoRayNNLSRotationScore_pos_iff (hu 1)).mp h1
    refine ⟨Equiv.refl _, ?_⟩
    intro s
    fin_cases s
    · refine ⟨hclip0.1, ?_⟩
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · exact hclip0.2
    · refine ⟨hclip1.1, ?_⟩
      intro j hj
      fin_cases j
      · exact hclip1.2
      · exact (hj rfl).elim
  · have hclip0 := (twoRayNNLSRotationScore_pos_iff (hu 0)).mp h0
    have hclip1 := (twoRayNNLSRotationScore_neg_iff (hu 1)).mp h1
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro s
    fin_cases s
    · refine ⟨?_, ?_⟩
      · simpa using hclip0.1
      · intro j hj
        fin_cases j
        · exact hclip0.2
        · exact (hj (by simp)).elim
    · refine ⟨?_, ?_⟩
      · simpa using hclip1.1
      · intro j hj
        fin_cases j
        · exact (hj (by simp)).elim
        · exact hclip1.2

end PKG26AtomicFeatures
