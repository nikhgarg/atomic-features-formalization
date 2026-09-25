import PKG26AtomicFeatures.MesoscaleReferenceStationarity
import PKG26AtomicFeatures.ReflectionVariations
import PKG26AtomicFeatures.MesoscaleEigenplaneObstruction
import PKG26AtomicFeatures.TwoColumnConeGeometry

/-!
# A reference minimizer must clip some projected input

If all orthogonal projections of the three reference inputs belonged to
the actual nonnegative synthesis cone, uniqueness of nonnegative least
squares would make each residual its exact normal component. Feasible
reflection variations then force the normal to be an eigenvector of the
actual reference covariance. Its low-moment eigenplane has two dominant
projections too obtuse to lie in a stable two-column cone.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators InnerProductSpace Matrix

/-- If the orthogonal plane projection is an actual feasible cone point,
its residual attains the normal-component lower bound and is the actual
unique nonnegative least-squares reconstruction. -/
theorem mesoscale_nnls_residual_of_projection_mem
    (B : Matrix (Fin 3) (Fin 2) ℝ) (hstable : SparseLowerStable B (1 / 2) 4)
    (n x : EuclideanRepresentation 3) (hn : ‖n‖ = 1)
    (horth : ∀ j, inner ℝ n (representationToEuclidean 3 (B.col j)) = 0)
    (hmem : mesoscaleNormalProjection n x ∈ nonnegativeSynthesisCone B) :
    x - representationToEuclidean 3
      (B.mulVec (nonnegativeLeastSquaresCode B (1 / 2) (by norm_num)
        (hstable.global_bound_of_width_le (by norm_num)) x)) = inner ℝ n x • n := by
  obtain ⟨u, hu, heq⟩ := hmem
  let ucode : FeatureVector 2 := (representationToEuclidean 2).symm u
  have hcode : IsNonnegativeLeastSquaresCode B x ucode := by
    refine ⟨hu, ?_⟩
    intro v _
    have heq' : representationToEuclidean 3 (B.mulVec ucode) = mesoscaleNormalProjection n x := heq
    rw [heq', mesoscaleNormalProjection, sub_sub_cancel]
    have hbound := squared_normal_projection_le_residual B n x hn horth v
    simpa [norm_smul, hn, Real.norm_eq_abs] using hbound
  have hchosen := hcode.eq_nonnegativeLeastSquaresCode (show (0 : ℝ) < 1 / 2 by norm_num)
    (hstable.global_bound_of_width_le (show 2 ≤ 4 by norm_num))
  rw [← hchosen]
  change x - euclideanDictionarySynthesis B u = _
  rw [heq, mesoscaleNormalProjection, sub_sub_cancel]

/-- The actual covariance's bilinear form is the actual weighted reference
second moment, including the unnormalized parent mass 3/5. -/
theorem mesoscale_covariance_inner_eq_weighted
    (n v : EuclideanRepresentation 3) :
    inner ℝ (mesoscaleReferenceCovarianceAction n) v =
      ∑ s, mesoscaleReferenceWeight s * inner ℝ n (mesoscaleReferenceInput s) *
        inner ℝ v (mesoscaleReferenceInput s) := by
  simp only [mesoscaleReferenceCovarianceAction, mesoscaleReferenceCovariance,
    mesoscaleReferenceWeight, mesoscaleReferenceInput, PiLp.inner_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [representationToEuclidean, real_inner_eq_re_inner, RCLike.inner_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

/-- If the three actual residuals are normal components, the reflection
variations force covariance-orthogonality to every tangent direction. -/
theorem IsMesoscaleReferenceMinimizer.covariance_orthogonal_of_normal_residuals
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable)
    (n : EuclideanRepresentation 3) (hn : ‖n‖ = 1)
    (hresidual : ∀ s, mesoscaleReferenceInput s - representationToEuclidean 3
      (B.mulVec (nonnegativeLeastSquaresCode B (1 / 2) (by norm_num)
        (hstable.global_bound_of_width_le (by norm_num)) (mesoscaleReferenceInput s))) =
          inner ℝ n (mesoscaleReferenceInput s) • n)
    (v : EuclideanRepresentation 3) (hv : inner ℝ n v = 0) :
    inner ℝ (mesoscaleReferenceCovarianceAction n) v = 0 := by
  have hstation := hmin.isometry_stationarity (reflectionVariation n v)
    (reflectionVariation_zero n v)
    (fun s => (2 : ℝ) • (inner ℝ n (mesoscaleReferenceInput s) • v -
      inner ℝ v (mesoscaleReferenceInput s) • n))
    (fun s => hasDerivAt_reflectionVariation_symm n v (mesoscaleReferenceInput s) hn hv)
  simp only [hresidual, real_inner_smul_left, real_inner_smul_right,
    inner_sub_right, real_inner_self_eq_norm_sq, hn, one_pow, hv, mul_zero,
    zero_sub] at hstation
  have hfactor : (∑ s, mesoscaleReferenceWeight s *
      (2 * -(inner ℝ v (mesoscaleReferenceInput s) *
        (inner ℝ n (mesoscaleReferenceInput s) * 1)))) =
      -2 * ∑ s, mesoscaleReferenceWeight s * inner ℝ n (mesoscaleReferenceInput s) *
        inner ℝ v (mesoscaleReferenceInput s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hfactor] at hstation
  rw [mesoscale_covariance_inner_eq_weighted]
  linarith

/-- Tangent covariance-orthogonality yields an actual eigenvector, using
the covariance vector's own orthogonal remainder as a tangent. -/
theorem IsMesoscaleReferenceMinimizer.eigenvector_of_normal_residuals
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable)
    (n : EuclideanRepresentation 3) (hn : ‖n‖ = 1)
    (hresidual : ∀ s, mesoscaleReferenceInput s - representationToEuclidean 3
      (B.mulVec (nonnegativeLeastSquaresCode B (1 / 2) (by norm_num)
        (hstable.global_bound_of_width_le (by norm_num)) (mesoscaleReferenceInput s))) =
          inner ℝ n (mesoscaleReferenceInput s) • n) :
    mesoscaleReferenceCovarianceAction n = mesoscaleNormalMoment n • n := by
  let c := mesoscaleReferenceCovarianceAction n
  let a : ℝ := inner ℝ n c
  let v := c - a • n
  have hv : inner ℝ n v = 0 := by
    dsimp [v, a]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
    ring
  have hcv := hmin.covariance_orthogonal_of_normal_residuals n hn hresidual v hv
  have hvv : inner ℝ v v = 0 := by
    change inner ℝ (c - a • n) v = 0
    rw [inner_sub_left, real_inner_smul_left, hv, mul_zero, sub_zero]
    exact hcv
  have hvzero : v = 0 := (inner_self_eq_zero).mp hvv
  have heigen : mesoscaleReferenceCovarianceAction n = a • n := sub_eq_zero.mp hvzero
  have ha := mesoscale_eigenvalue_eq_moment n a hn heigen
  simpa only [ha] using heigen

/-- Actual cone feasibility of every projected reference input forces
stationarity in the corresponding eigenplane. -/
theorem IsMesoscaleReferenceMinimizer.eigenvector_of_projections_mem
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable)
    (n : EuclideanRepresentation 3) (hn : ‖n‖ = 1)
    (horth : ∀ j, inner ℝ n (representationToEuclidean 3 (B.col j)) = 0)
    (hmem : ∀ s, mesoscaleNormalProjection n (mesoscaleReferenceInput s) ∈ nonnegativeSynthesisCone B) :
    mesoscaleReferenceCovarianceAction n = mesoscaleNormalMoment n • n := by
  exact hmin.eigenvector_of_normal_residuals n hn fun s =>
    mesoscale_nnls_residual_of_projection_mem B hstable n (mesoscaleReferenceInput s) hn horth (hmem s)

/-- Every actual global reference minimizer clips at least one orthogonal
reference projection. The only geometric input is an actual unit normal
to its two columns; stationarity and the eigenvector condition are derived. -/
theorem IsMesoscaleReferenceMinimizer.exists_projection_not_mem_cone
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable)
    (n : EuclideanRepresentation 3) (hn : ‖n‖ = 1)
    (horth : ∀ j, inner ℝ n (representationToEuclidean 3 (B.col j)) = 0) :
    ∃ s : Fin 3, mesoscaleNormalProjection n (mesoscaleReferenceInput s) ∉
      nonnegativeSynthesisCone B := by
  classical
  by_contra hnot
  push Not at hnot
  have heigen := hmin.eigenvector_of_projections_mem n hn horth hnot
  have hmoment := (mesoscaleNormalMoment_le_referenceRisk B hstable n hn horth).trans_lt
    hmin.referenceRisk_lt
  have hupper := mesoscale_eigenplane_projection_inner_lt n (mesoscaleNormalMoment n)
    hn heigen hmoment
  obtain ⟨u, hu, heu⟩ := hnot 0
  obtain ⟨v, hv, hev⟩ := hnot 1
  have hlower := two_column_half_stable_cone_inner_ge B hmin.1 hstable
    ((representationToEuclidean 2).symm u) ((representationToEuclidean 2).symm v) hu hv
  change -(3 / 4 : ℝ) * ‖euclideanDictionarySynthesis B u‖ *
      ‖euclideanDictionarySynthesis B v‖ ≤
    inner ℝ (euclideanDictionarySynthesis B u) (euclideanDictionarySynthesis B v) at hlower
  rw [heu, hev] at hlower
  exact (not_lt_of_ge (by simpa only [mul_assoc] using hlower)) hupper

end PKG26AtomicFeatures
