import PKG26AtomicFeatures.SparseCodeGeometry

/-!
# Local estimates for a matched coefficient

A source coordinate functional nearly annihilates the other columns of a
selected learned support. Its value on the matched column distinguishes the
two orientations. Comparing the actual code with a signed supported code
then bounds either the source coordinate or its recovery error. The
functional and approximation hypotheses below are local geometric inputs;
no distributional or support-selection conclusion is assumed.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators

/-- A functional with norm at most `1 / γ` has the same absolute bound on
every column whose Euclidean norm is at most one. -/
theorem abs_functional_column_le_of_norm {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ)
    (L : EuclideanRepresentation d →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hL : ‖L‖ ≤ 1 / γ) (j : Fin m)
    (hunit : ‖representationToEuclidean d (B.col j)‖ ≤ 1) :
    |L (representationToEuclidean d (B.col j))| ≤ 1 / γ := by
  calc
    _ ≤ ‖L‖ * ‖representationToEuclidean d (B.col j)‖ := L.le_opNorm _
    _ ≤ (1 / γ) * 1 := mul_le_mul hL hunit (norm_nonneg _) (by positivity)
    _ = 1 / γ := mul_one _

/-- A supported synthesis has its usual finite functional expansion. -/
theorem functional_mulVec_eq_supported_sum {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ)
    (L : EuclideanRepresentation d →L[ℝ] ℝ)
    (T : Finset (Fin m)) (v : FeatureVector m) (hv : nonzeroSupport v ⊆ T) :
    L (representationToEuclidean d (B.mulVec v)) =
      ∑ j ∈ T, v j * L (representationToEuclidean d (B.col j)) := by
  classical
  rw [euclidean_mulVec_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hz : v j = 0 := by
    by_contra hn
    exact hj (hv (by simpa only [mem_nonzeroSupport_iff] using hn))
  simp only [hz, zero_mul]

/-- The other supported columns contribute at most the coefficient norm
times their common functional bound and their number. -/
theorem abs_off_matched_functional_sum_le {d m K : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ)
    (L : EuclideanRepresentation d →L[ℝ] ℝ)
    (T : Finset (Fin m)) (v : FeatureVector m) (e : Fin m) (γ δ : ℝ)
    (hγ : 0 < γ) (hδ : 0 ≤ δ) (hT : T.card ≤ K)
    (hvnorm : ‖representationToEuclidean m v‖ ≤ (K : ℝ) / γ)
    (hoff : ∀ j ∈ T, j ≠ e →
      |L (representationToEuclidean d (B.col j))| ≤ 2 * δ / γ) :
    |∑ j ∈ T.erase e, v j * L (representationToEuclidean d (B.col j))| ≤
      2 * δ * (K : ℝ) ^ 2 / γ ^ 2 := by
  classical
  have hcoord (j : Fin m) : |v j| ≤ (K : ℝ) / γ :=
    (PiLp.norm_apply_le (representationToEuclidean m v) j).trans hvnorm
  have hcard : (T.erase e).card ≤ K := (Finset.card_erase_le).trans hT
  calc
    _ ≤ ∑ j ∈ T.erase e, |v j * L (representationToEuclidean d (B.col j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ T.erase e, ((K : ℝ) / γ) * (2 * δ / γ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hcoord j) (hoff j (Finset.mem_erase.mp hj).2
        (Finset.mem_erase.mp hj).1) (abs_nonneg _) (by positivity)
    _ = ((T.erase e).card : ℝ) * (((K : ℝ) / γ) * (2 * δ / γ)) := by simp
    _ ≤ (K : ℝ) * (((K : ℝ) / γ) * (2 * δ / γ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = 2 * δ * (K : ℝ) ^ 2 / γ ^ 2 := by ring

/-- A projection residual controls the error in the source-coordinate
functional, using its operator norm. -/
theorem abs_functional_projection_error_le {d m K : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ)
    (L : EuclideanRepresentation d →L[ℝ] ℝ)
    (f : EuclideanRepresentation d) (v : FeatureVector m) (z γ δ : ℝ)
    (hγ : 0 < γ) (hL : ‖L‖ ≤ 1 / γ) (hz : L f = z)
    (hprojection : ‖f - representationToEuclidean d (B.mulVec v)‖ ≤ δ * (K : ℝ)) :
    |z - L (representationToEuclidean d (B.mulVec v))| ≤ δ * (K : ℝ) / γ := by
  calc
    _ = ‖L (f - representationToEuclidean d (B.mulVec v))‖ := by
      rw [map_sub, hz, Real.norm_eq_abs]
    _ ≤ ‖L‖ * ‖f - representationToEuclidean d (B.mulVec v)‖ := L.le_opNorm _
    _ ≤ (1 / γ) * (δ * (K : ℝ)) :=
      mul_le_mul hL hprojection (norm_nonneg _) (by positivity)
    _ = δ * (K : ℝ) / γ := by ring

/-- A nonpositive matched functional value cannot make a large positive
contribution unless the supported code differs from the nonnegative code. -/
theorem negative_functional_coordinate_contribution_le {m K : ℕ}
    (u v : FeatureVector m) (e : Fin m) (c γ δ r : ℝ)
    (hγ : 0 < γ) (hc : c ≤ 0) (hcbound : |c| ≤ 1 / γ) (hu : 0 ≤ u e)
    (hcomparison : ‖representationToEuclidean m (u - v)‖ ≤ (r + δ * (K : ℝ)) / γ) :
    v e * c ≤ (r + δ * (K : ℝ)) / γ ^ 2 := by
  have hcoord := (abs_coordinate_sub_le_euclidean_norm u v e).trans hcomparison
  have hnonpos : u e * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu hc
  calc
    v e * c = (v e - u e) * c + u e * c := by ring
    _ ≤ |(v e - u e) * c| := by linarith [le_abs_self ((v e - u e) * c)]
    _ = |u e - v e| * |c| := by rw [abs_mul, abs_sub_comm]
    _ ≤ |u e - v e| * (1 / γ) := mul_le_mul_of_nonneg_left hcbound (abs_nonneg _)
    _ ≤ ((r + δ * (K : ℝ)) / γ) * (1 / γ) :=
      mul_le_mul_of_nonneg_right hcoord (by positivity)
    _ = (r + δ * (K : ℝ)) / γ ^ 2 := by ring

/-- Negative orientation forces the actual residual to control the source
coordinate, with a sparsity-dependent projection-error term. -/
theorem matched_coefficient_negative_orientation_bound {d m K : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ)
    (L : EuclideanRepresentation d →L[ℝ] ℝ)
    (T : Finset (Fin m)) (e : Fin m) (f : EuclideanRepresentation d)
    (u v : FeatureVector m) (z γ δ r : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hδ : 0 ≤ δ)
    (hT : T.card ≤ K) (he : e ∈ T) (hv : nonzeroSupport v ⊆ T)
    (hL : ‖L‖ ≤ 1 / γ) (hz : L f = z)
    (hnegative : L (representationToEuclidean d (B.col e)) ≤ -(1 / 2 : ℝ))
    (hdiag : |L (representationToEuclidean d (B.col e))| ≤ 1 / γ)
    (hoff : ∀ j ∈ T, j ≠ e →
      |L (representationToEuclidean d (B.col j))| ≤ 2 * δ / γ)
    (hvnorm : ‖representationToEuclidean m v‖ ≤ (K : ℝ) / γ)
    (hprojection : ‖f - representationToEuclidean d (B.mulVec v)‖ ≤ δ * (K : ℝ))
    (hcomparison : ‖representationToEuclidean m (u - v)‖ ≤ (r + δ * (K : ℝ)) / γ)
    (hu : 0 ≤ u e) :
    z ≤ r / γ ^ 2 + 4 * δ * (K : ℝ) ^ 2 / γ ^ 2 := by
  have herror := abs_functional_projection_error_le B L f v z γ δ hγ hL hz hprojection
  have hother := abs_off_matched_functional_sum_le B L T v e γ δ hγ hδ hT hvnorm hoff
  have hmatched := negative_functional_coordinate_contribution_le u v e
    (L (representationToEuclidean d (B.col e))) γ δ r hγ (by linarith) hdiag hu hcomparison
  have hexpand := functional_mulVec_eq_supported_sum B L T v hv
  rw [← Finset.add_sum_erase _ _ he] at hexpand
  have hpre : z ≤ δ * (K : ℝ) / γ + (r + δ * (K : ℝ)) / γ ^ 2 +
      2 * δ * (K : ℝ) ^ 2 / γ ^ 2 := by
    have hleft := (le_abs_self _).trans herror
    have hright := (le_abs_self _).trans hother
    rw [hexpand] at hleft
    linarith
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hproduct := mul_nonneg (mul_nonneg hδ (Nat.cast_nonneg K))
    (show 0 ≤ 2 * (K : ℝ) - γ - 1 by linarith)
  calc
    z ≤ _ := hpre
    _ = (r + δ * (K : ℝ) * γ + δ * (K : ℝ) + 2 * δ * (K : ℝ) ^ 2) / γ ^ 2 := by
      field_simp
      ring
    _ ≤ (r + 4 * δ * (K : ℝ) ^ 2) / γ ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg γ)
    _ = r / γ ^ 2 + 4 * δ * (K : ℝ) ^ 2 / γ ^ 2 := by ring

/-- Once the matched column is positively oriented, the same local
functional controls the actual matched coefficient's error. -/
theorem matched_coefficient_positive_orientation_bound {d m K : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ)
    (L : EuclideanRepresentation d →L[ℝ] ℝ)
    (T : Finset (Fin m)) (e : Fin m) (f : EuclideanRepresentation d)
    (u v : FeatureVector m) (z γ δ r q : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1) (hδ : 0 ≤ δ)
    (hT : T.card ≤ K) (he : e ∈ T) (hv : nonzeroSupport v ⊆ T)
    (hL : ‖L‖ ≤ 1 / γ) (hz : L f = z)
    (hpositive : |L (representationToEuclidean d (B.col e)) - 1| ≤ q / γ)
    (hoff : ∀ j ∈ T, j ≠ e →
      |L (representationToEuclidean d (B.col j))| ≤ 2 * δ / γ)
    (hvnorm : ‖representationToEuclidean m v‖ ≤ (K : ℝ) / γ)
    (hprojection : ‖f - representationToEuclidean d (B.mulVec v)‖ ≤ δ * (K : ℝ))
    (hcomparison : ‖representationToEuclidean m (u - v)‖ ≤ (r + δ * (K : ℝ)) / γ) :
    |u e - z| ≤ r / γ + (q * (K : ℝ) + 4 * δ * (K : ℝ) ^ 2) / γ ^ 2 := by
  have herror := abs_functional_projection_error_le B L f v z γ δ hγ hL hz hprojection
  have hother := abs_off_matched_functional_sum_le B L T v e γ δ hγ hδ hT hvnorm hoff
  have hcoord := (abs_coordinate_sub_le_euclidean_norm u v e).trans hcomparison
  have hdiag : |v e * (L (representationToEuclidean d (B.col e)) - 1)| ≤
      q * (K : ℝ) / γ ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ ((K : ℝ) / γ) * (q / γ) :=
        mul_le_mul ((PiLp.norm_apply_le (representationToEuclidean m v) e).trans hvnorm)
          hpositive (abs_nonneg _) (by positivity)
      _ = q * (K : ℝ) / γ ^ 2 := by ring
  have hexpand := functional_mulVec_eq_supported_sum B L T v hv
  rw [← Finset.add_sum_erase _ _ he] at hexpand
  have hprojected : |v e - z| ≤ δ * (K : ℝ) / γ + q * (K : ℝ) / γ ^ 2 +
      2 * δ * (K : ℝ) ^ 2 / γ ^ 2 := by
    calc
      _ = |(z - L (representationToEuclidean d (B.mulVec v))) +
          v e * (L (representationToEuclidean d (B.col e)) - 1) +
          ∑ j ∈ T.erase e, v j * L (representationToEuclidean d (B.col j))| := by
        rw [hexpand, abs_sub_comm (v e) z]
        congr 1
        ring
      _ ≤ |z - L (representationToEuclidean d (B.mulVec v))| +
          |v e * (L (representationToEuclidean d (B.col e)) - 1)| +
          |∑ j ∈ T.erase e, v j * L (representationToEuclidean d (B.col j))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add herror hdiag) hother
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hproduct := mul_nonneg (mul_nonneg hδ (Nat.cast_nonneg K))
    (show 0 ≤ (K : ℝ) - γ by linarith)
  calc
    _ ≤ |u e - v e| + |v e - z| := abs_sub_le _ _ _
    _ ≤ (r + δ * (K : ℝ)) / γ +
        (δ * (K : ℝ) / γ + q * (K : ℝ) / γ ^ 2 +
          2 * δ * (K : ℝ) ^ 2 / γ ^ 2) := add_le_add hcoord hprojected
    _ = r / γ + (2 * δ * (K : ℝ) * γ + q * (K : ℝ) +
        2 * δ * (K : ℝ) ^ 2) / γ ^ 2 := by
      field_simp
      ring
    _ ≤ r / γ + (q * (K : ℝ) + 4 * δ * (K : ℝ) ^ 2) / γ ^ 2 := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg γ))

/-- A coordinate absent from the supported comparison code can be active
only to the extent permitted by the actual code-distance bound. -/
theorem actual_coordinate_le_of_projected_support_exclusion {m K : ℕ}
    (T : Finset (Fin m)) (u v : FeatureVector m) (e : Fin m) (γ δ r : ℝ)
    (hv : nonzeroSupport v ⊆ T) (he : e ∉ T)
    (hcomparison : ‖representationToEuclidean m (u - v)‖ ≤ (r + δ * (K : ℝ)) / γ) :
    u e ≤ (r + δ * (K : ℝ)) / γ := by
  have hz : v e = 0 := by
    by_contra hn
    exact he (hv (by simpa only [mem_nonzeroSupport_iff] using hn))
  have hcoord := (abs_coordinate_sub_le_euclidean_norm u v e).trans hcomparison
  rw [hz, sub_zero] at hcoord
  exact (le_abs_self _).trans hcoord

end PKG26AtomicFeatures
