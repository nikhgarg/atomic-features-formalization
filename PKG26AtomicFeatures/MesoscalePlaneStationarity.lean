import PKG26AtomicFeatures.MesoscaleReferenceStationarity
import PKG26AtomicFeatures.NonnegativeLeastSquaresActiveSet
import PKG26AtomicFeatures.ReflectionVariations

/-!
# In-plane stationarity of every mesoscale reference minimizer

A common rotation of the two learned rays is feasible even at the boundary
of the Gram constraint. Its first-order condition is an exact balance of
active coefficients times the opposite residual scores. Complementarity
removes the same-coordinate terms.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators InnerProductSpace

theorem nnls_plane_variation_inner {d : ℕ}
    (B : Matrix (Fin d) (Fin 2) ℝ) (hunit : HasUnitEuclideanColumns B)
    (x : EuclideanRepresentation d) (u : FeatureVector 2)
    (hu : IsNonnegativeLeastSquaresCode B x u) :
    let b₀ := representationToEuclidean d (B.col 0)
    let b₁ := representationToEuclidean d (B.col 1)
    let v := b₁ - inner ℝ b₀ b₁ • b₀
    inner ℝ (x - representationToEuclidean d (B.mulVec u))
      ((2 : ℝ) • (inner ℝ b₀ x • v - inner ℝ v x • b₀)) =
        2 * (u 0 * nnlsResidualColumnInner B x u 1 -
          u 1 * nnlsResidualColumnInner B x u 0) := by
  let b₀ := representationToEuclidean d (B.col 0)
  let b₁ := representationToEuclidean d (B.col 1)
  let r := x - representationToEuclidean d (B.mulVec u)
  let c := inner ℝ b₀ b₁
  let g₀ := nnlsResidualColumnInner B x u 0
  let g₁ := nnlsResidualColumnInner B x u 1
  have hsynth : representationToEuclidean d (B.mulVec u) = u 0 • b₀ + u 1 • b₁ := by
    rw [euclidean_mulVec_eq_sum]
    simp only [Fin.sum_univ_two]
    rfl
  have hb₀ : inner ℝ b₀ b₀ = 1 := by rw [real_inner_self_eq_norm_sq, hunit 0]; norm_num
  have hb₁ : inner ℝ b₁ b₁ = 1 := by rw [real_inner_self_eq_norm_sq, hunit 1]; norm_num
  have hx₀ : inner ℝ b₀ x = u 0 + c * u 1 + g₀ := by
    dsimp [g₀, nnlsResidualColumnInner]
    rw [hsynth]
    change inner ℝ b₀ x = u 0 + c * u 1 + inner ℝ (x - (u 0 • b₀ + u 1 • b₁)) b₀
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_comm x b₀, hb₀]
    dsimp [c]
    rw [real_inner_comm b₁ b₀]
    ring
  have hx₁ : inner ℝ b₁ x = c * u 0 + u 1 + g₁ := by
    dsimp [g₁, nnlsResidualColumnInner]
    rw [hsynth]
    change inner ℝ b₁ x = c * u 0 + u 1 + inner ℝ (x - (u 0 • b₀ + u 1 • b₁)) b₁
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_comm x b₁, hb₁]
    dsimp [c]
    ring
  have hpair : inner ℝ r
      ((2 : ℝ) • (inner ℝ b₀ x • (b₁ - c • b₀) -
        inner ℝ (b₁ - c • b₀) x • b₀)) =
      2 * (inner ℝ b₀ x * g₁ - inner ℝ b₁ x * g₀) := by
    simp only [real_inner_smul_right, inner_sub_right, inner_sub_left, real_inner_smul_left]
    change 2 * (inner ℝ b₀ x * (g₁ - c * g₀) -
      (inner ℝ b₁ x - c * inner ℝ b₀ x) * g₀) = _
    ring
  change inner ℝ r _ = 2 * (u 0 * g₁ - u 1 * g₀)
  rw [hpair, hx₀, hx₁]
  calc
    _ = 2 * (u 0 * g₁ - u 1 * g₀) + 2 * c * (u 1 * g₁ - u 0 * g₀) := by ring
    _ = _ := by
      rw [show u 1 * g₁ = 0 from hu.coordinate_complementarity 1,
        show u 0 * g₀ = 0 from hu.coordinate_complementarity 0]
      ring

theorem IsMesoscaleReferenceMinimizer.plane_stationarity
    {B : Matrix (Fin 3) (Fin 2) ℝ} {hstable : SparseLowerStable B (1 / 2) 4}
    (hmin : IsMesoscaleReferenceMinimizer B hstable) :
    let u := fun s => nonnegativeLeastSquaresCode B (1 / 2) (by norm_num)
      (hstable.global_bound_of_width_le (by norm_num)) (mesoscaleReferenceInput s)
    ∑ s, mesoscaleReferenceWeight s *
      (u s 0 * nnlsResidualColumnInner B (mesoscaleReferenceInput s) (u s) 1 -
        u s 1 * nnlsResidualColumnInner B (mesoscaleReferenceInput s) (u s) 0) = 0 := by
  let b₀ := representationToEuclidean 3 (B.col 0)
  let b₁ := representationToEuclidean 3 (B.col 1)
  let v := b₁ - inner ℝ b₀ b₁ • b₀
  have hnorm : ‖b₀‖ = 1 := hmin.1 0
  have horth : inner ℝ b₀ v = 0 := by
    simp [v, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm]
  have hstation := hmin.isometry_stationarity (reflectionVariation b₀ v)
    (reflectionVariation_zero b₀ v)
    (fun s => (2 : ℝ) • (inner ℝ b₀ (mesoscaleReferenceInput s) • v -
      inner ℝ v (mesoscaleReferenceInput s) • b₀))
    (fun s => hasDerivAt_reflectionVariation_symm b₀ v (mesoscaleReferenceInput s) hnorm horth)
  dsimp only [v, b₀, b₁] at hstation
  simp_rw [nnls_plane_variation_inner B hmin.1 _ _
    (nonnegativeLeastSquaresCode_isMinimizer B (1 / 2) (by norm_num)
      (hstable.global_bound_of_width_le (by norm_num)) _)] at hstation
  dsimp only
  have heq : ∀ a w : ℝ, w * (2 * a) = 2 * (w * a) := by intros; ring
  simp_rw [heq] at hstation
  rw [← Finset.mul_sum] at hstation
  linarith

end PKG26AtomicFeatures
