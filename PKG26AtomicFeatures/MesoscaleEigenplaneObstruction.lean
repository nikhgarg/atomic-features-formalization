import PKG26AtomicFeatures.MesoscaleReferenceGeometry

/-!
# The spectral obstruction for the mesoscale reference plane

A unit eigenvector of the actual reference covariance with moment below
49/100 has equal child coordinates and is proportional to (-k,1,1), where
0 < k < 9/20. Removing that normal component makes the dominant inputs
strictly more obtuse than the stable two-column cone can accommodate.
-/

namespace PKG26AtomicFeatures

open scoped Matrix BigOperators InnerProductSpace

/-- The actual uncentered covariance of the three-point reference objective. -/
noncomputable def mesoscaleReferenceCovariance : Matrix (Fin 3) (Fin 3) ℝ :=
  !![241 / 400, 1 / 40, 1 / 40; 1 / 40, 1 / 2, 0; 1 / 40, 0, 1 / 2]

/-- The reference covariance acting on Euclidean, rather than sup-norm,
coordinates. -/
noncomputable def mesoscaleReferenceCovarianceAction
    (n : EuclideanRepresentation 3) : EuclideanRepresentation 3 :=
  representationToEuclidean 3 (mesoscaleReferenceCovariance.mulVec (fun i => n i))

/-- Orthogonal removal of a unit normal component. -/
noncomputable def mesoscaleNormalProjection
    (n x : EuclideanRepresentation 3) : EuclideanRepresentation 3 :=
  x - inner ℝ n x • n

private theorem unit_three_coordinates
    (n : EuclideanRepresentation 3) (hn : ‖n‖ = 1) :
    n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq n
  rw [hn] at h
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_pow, add_assoc] using h.symm

private theorem covariance_eigen_coordinates
    (n : EuclideanRepresentation 3) (evalue : ℝ)
    (heigen : mesoscaleReferenceCovarianceAction n = evalue • n) :
    (241 / 400) * n 0 + (1 / 40) * n 1 + (1 / 40) * n 2 = evalue * n 0 ∧
    (1 / 40) * n 0 + (1 / 2) * n 1 = evalue * n 1 ∧
    (1 / 40) * n 0 + (1 / 2) * n 2 = evalue * n 2 := by
  have h (j : Fin 3) := congrArg (fun v : EuclideanRepresentation 3 => v j) heigen
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [mesoscaleReferenceCovarianceAction, mesoscaleReferenceCovariance,
    representationToEuclidean, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h0 h1 h2
  change (241 / 400) * n 0 + ((1 / 40) * n 1 + (1 / 40) * n 2) = evalue * n 0 at h0
  change (1 / 40) * n 0 + (1 / 2) * n 1 = evalue * n 1 at h1
  change (1 / 40) * n 0 + (1 / 2) * n 2 = evalue * n 2 at h2
  exact ⟨by linarith only [h0], h1, h2⟩

/-- The eigenvalue is the actual quadratic moment; no eigenvalue formula
or choice of the lowest eigenspace is assumed. -/
theorem mesoscale_eigenvalue_eq_moment
    (n : EuclideanRepresentation 3) (evalue : ℝ) (hn : ‖n‖ = 1)
    (heigen : mesoscaleReferenceCovarianceAction n = evalue • n) :
    evalue = mesoscaleNormalMoment n := by
  obtain ⟨h0, h1, h2⟩ := covariance_eigen_coordinates n evalue heigen
  have hnorm := unit_three_coordinates n hn
  have h0' := congrArg (fun t : ℝ => t * n 0) h0
  have h1' := congrArg (fun t : ℝ => t * n 1) h1
  have h2' := congrArg (fun t : ℝ => t * n 2) h2
  have hnorm' := congrArg (fun t : ℝ => evalue * t) hnorm
  dsimp [mesoscaleNormalMoment]
  nlinarith

/-- The actual eigen-equation below the reference cutoff forces the
symmetric normal and its exact rational quadratic equation. The scale n₁
may have either sign, so the claim does not impose a normal orientation. -/
theorem mesoscale_eigenplane_scalar_constraints
    (n : EuclideanRepresentation 3) (evalue : ℝ) (hn : ‖n‖ = 1)
    (heigen : mesoscaleReferenceCovarianceAction n = evalue • n)
    (hmoment : mesoscaleNormalMoment n < 49 / 100) :
    evalue = mesoscaleNormalMoment n ∧ n 2 = n 1 ∧ n 1 ≠ 0 ∧
      ∃ k : ℝ, 0 < k ∧ k < 9 / 20 ∧ n 0 = -k * n 1 ∧
        10 * k ^ 2 + 41 * k - 20 = 0 ∧ evalue = 1 / 2 - k / 40 := by
  have hevalue := mesoscale_eigenvalue_eq_moment n evalue hn heigen
  have hevaluecut : evalue < 49 / 100 := hevalue ▸ hmoment
  obtain ⟨h0, h1, h2⟩ := covariance_eigen_coordinates n evalue heigen
  have hchildren : n 2 = n 1 := by
    have hprod : (1 / 2 - evalue) * (n 2 - n 1) = 0 := by nlinarith
    have hne : (1 / 2 - evalue : ℝ) ≠ 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hne)
  have hn1 : n 1 ≠ 0 := by
    intro hzero
    have hnorm := unit_three_coordinates n hn
    rw [hchildren] at hnorm
    rw [hzero] at hnorm h1
    nlinarith
  let k : ℝ := -n 0 / n 1
  have hnk : n 0 = -k * n 1 := by
    dsimp [k]
    field_simp
  have hevaluek : evalue = 1 / 2 - k / 40 := by
    have hprod : (evalue - (1 / 2 - k / 40)) * n 1 = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hn1)
  have hkpos : 0 < k := by linarith
  have hquadratic : 10 * k ^ 2 + 41 * k - 20 = 0 := by
    rw [hchildren, hnk, hevaluek] at h0
    have hprod : (10 * k ^ 2 + 41 * k - 20) * n 1 = 0 := by nlinarith [h0]
    exact (mul_eq_zero.mp hprod).resolve_right hn1
  have hkupper : k < 9 / 20 := by
    by_contra hk
    have hkle : (9 / 20 : ℝ) ≤ k := le_of_not_gt hk
    have hsq : (9 / 20 : ℝ) ^ 2 ≤ k ^ 2 :=
      (sq_le_sq₀ (by norm_num) hkpos.le).mpr hkle
    nlinarith
  exact ⟨hevalue, hchildren, hn1, k, hkpos, hkupper, hnk, hquadratic, hevaluek⟩

private theorem inner_three_coordinates (v w : EuclideanRepresentation 3) :
    inner ℝ v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change w 0 * v 0 + (w 1 * v 1 + w 2 * v 2) = _
  ring

private theorem dominant_inner_normal (n : EuclideanRepresentation 3) :
    inner ℝ n (mesoscaleReferenceInput 0) = n 0 / 20 + n 1 ∧
    inner ℝ n (mesoscaleReferenceInput 1) = n 0 / 20 + n 2 := by
  constructor <;> rw [inner_three_coordinates] <;>
    norm_num [mesoscaleReferenceInput, representationToEuclidean, Matrix.cons_val_two] <;> ring

/-- The removed normal component of either dominant point exceeds the
exact threshold that makes their projected cosine smaller than -3/4. -/
theorem mesoscale_eigenplane_normal_component_sq
    (n : EuclideanRepresentation 3) (evalue : ℝ) (hn : ‖n‖ = 1)
    (heigen : mesoscaleReferenceCovarianceAction n = evalue • n)
    (hmoment : mesoscaleNormalMoment n < 49 / 100) :
    inner ℝ n (mesoscaleReferenceInput 0) = inner ℝ n (mesoscaleReferenceInput 1) ∧
      (1 / 400 + 3 / 7 : ℝ) < inner ℝ n (mesoscaleReferenceInput 0) ^ 2 := by
  obtain ⟨_, hchildren, _, k, hkpos, hkupper, hnk, _, _⟩ :=
    mesoscale_eigenplane_scalar_constraints n evalue hn heigen hmoment
  obtain ⟨ht0, ht1⟩ := dominant_inner_normal n
  refine ⟨by rw [ht0, ht1, hchildren], ?_⟩
  have hnorm := unit_three_coordinates n hn
  have hscale : (2 + k ^ 2) * n 1 ^ 2 = 1 := by
    rw [hnk, hchildren] at hnorm
    nlinarith [hnorm]
  have hden : 0 < 2 + k ^ 2 := by positivity
  have hfrac : inner ℝ n (mesoscaleReferenceInput 0) ^ 2 =
      (1 - k / 20) ^ 2 / (2 + k ^ 2) := by
    apply (eq_div_iff hden.ne').mpr
    rw [ht0, hnk]
    nlinarith [congrArg (fun t : ℝ => (1 - k / 20) ^ 2 * t) hscale]
  have hksq : k ^ 2 < (9 / 20 : ℝ) ^ 2 := by
    exact (sq_lt_sq₀ hkpos.le (by norm_num)).mpr hkupper
  have hnum : (391 / 400 : ℝ) ^ 2 < (1 - k / 20) ^ 2 := by
    apply (sq_lt_sq₀ (by norm_num) (by linarith : 0 ≤ 1 - k / 20)).mpr
    linarith
  have hratio : (152881 / 352400 : ℝ) < (1 - k / 20) ^ 2 / (2 + k ^ 2) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  rw [hfrac]
  exact lt_trans (by norm_num) hratio

/-- Inner products after removing a unit normal have the usual exact
rank-one correction. -/
theorem mesoscaleNormalProjection_inner
    (n x y : EuclideanRepresentation 3) (hn : ‖n‖ = 1) :
    inner ℝ (mesoscaleNormalProjection n x) (mesoscaleNormalProjection n y) =
      inner ℝ x y - inner ℝ n x * inner ℝ n y := by
  simp only [mesoscaleNormalProjection, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, real_inner_comm x n]
  ring

private theorem dominant_reference_inner_products :
    inner ℝ (mesoscaleReferenceInput 0) (mesoscaleReferenceInput 0) = 401 / 400 ∧
    inner ℝ (mesoscaleReferenceInput 1) (mesoscaleReferenceInput 1) = 401 / 400 ∧
    inner ℝ (mesoscaleReferenceInput 0) (mesoscaleReferenceInput 1) = 1 / 400 := by
  repeat' constructor
  all_goals
    rw [inner_three_coordinates]
    norm_num [mesoscaleReferenceInput, representationToEuclidean, Matrix.cons_val_two]

/-- Below the actual reference cutoff, an eigenplane's two dominant
projections have inner product strictly below minus three quarters of
their norm product. All eigenvalue and scalar constraints are derived from
the actual covariance equation in this statement. -/
theorem mesoscale_eigenplane_projection_inner_lt
    (n : EuclideanRepresentation 3) (evalue : ℝ) (hn : ‖n‖ = 1)
    (heigen : mesoscaleReferenceCovarianceAction n = evalue • n)
    (hmoment : mesoscaleNormalMoment n < 49 / 100) :
    inner ℝ (mesoscaleNormalProjection n (mesoscaleReferenceInput 0))
        (mesoscaleNormalProjection n (mesoscaleReferenceInput 1)) <
      -(3 / 4 : ℝ) * (‖mesoscaleNormalProjection n (mesoscaleReferenceInput 0)‖ *
        ‖mesoscaleNormalProjection n (mesoscaleReferenceInput 1)‖) := by
  obtain ⟨ht, hcomponent⟩ := mesoscale_eigenplane_normal_component_sq n evalue hn heigen hmoment
  obtain ⟨h00, h11, h01⟩ := dominant_reference_inner_products
  have hnorm0 := mesoscaleNormalProjection_inner n (mesoscaleReferenceInput 0)
    (mesoscaleReferenceInput 0) hn
  have hnorm1 := mesoscaleNormalProjection_inner n (mesoscaleReferenceInput 1)
    (mesoscaleReferenceInput 1) hn
  have hinner := mesoscaleNormalProjection_inner n (mesoscaleReferenceInput 0)
    (mesoscaleReferenceInput 1) hn
  rw [real_inner_self_eq_norm_sq, h00] at hnorm0
  rw [real_inner_self_eq_norm_sq, h11, ← ht] at hnorm1
  rw [h01, ← ht] at hinner
  have hnormeq : ‖mesoscaleNormalProjection n (mesoscaleReferenceInput 0)‖ =
      ‖mesoscaleNormalProjection n (mesoscaleReferenceInput 1)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith
  rw [← hnormeq]
  nlinarith

/-- In particular both projections are nonzero, and their normalized
inner product is strictly below the stable cone's -3/4 threshold. -/
theorem mesoscale_eigenplane_projected_cosine_lt
    (n : EuclideanRepresentation 3) (evalue : ℝ) (hn : ‖n‖ = 1)
    (heigen : mesoscaleReferenceCovarianceAction n = evalue • n)
    (hmoment : mesoscaleNormalMoment n < 49 / 100) :
    0 < ‖mesoscaleNormalProjection n (mesoscaleReferenceInput 0)‖ ∧
    0 < ‖mesoscaleNormalProjection n (mesoscaleReferenceInput 1)‖ ∧
    inner ℝ (mesoscaleNormalProjection n (mesoscaleReferenceInput 0))
        (mesoscaleNormalProjection n (mesoscaleReferenceInput 1)) /
      (‖mesoscaleNormalProjection n (mesoscaleReferenceInput 0)‖ *
        ‖mesoscaleNormalProjection n (mesoscaleReferenceInput 1)‖) < -(3 / 4 : ℝ) := by
  have hinner := mesoscale_eigenplane_projection_inner_lt n evalue hn heigen hmoment
  have hy0 : mesoscaleNormalProjection n (mesoscaleReferenceInput 0) ≠ 0 := by
    intro hzero
    simp only [hzero, inner_zero_left, norm_zero, zero_mul, mul_zero, lt_self_iff_false] at hinner
  have hy1 : mesoscaleNormalProjection n (mesoscaleReferenceInput 1) ≠ 0 := by
    intro hzero
    simp only [hzero, inner_zero_right, norm_zero, mul_zero, lt_self_iff_false] at hinner
  refine ⟨norm_pos_iff.mpr hy0, norm_pos_iff.mpr hy1, ?_⟩
  exact (div_lt_iff₀ (mul_pos (norm_pos_iff.mpr hy0) (norm_pos_iff.mpr hy1))).mpr hinner

end PKG26AtomicFeatures
