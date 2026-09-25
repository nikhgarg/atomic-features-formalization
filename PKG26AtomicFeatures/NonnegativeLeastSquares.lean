import PKG26AtomicFeatures.SparseStability
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Nonnegative least squares for globally stable dictionaries

The actual nonnegative synthesis cone is closed because the dictionary's
global lower singular-value bound makes synthesis a closed embedding. The
Hilbert projection theorem gives a minimizer. Its variational inequalities
give uniqueness and continuity of the selected coefficient map.

No sparsity constraint is imposed here. In the mesoscale application it is
automatic at the relevant small learned widths.
-/

namespace PKG26AtomicFeatures

open Set Topology
open scoped NNReal

/-- Dictionary synthesis as a continuous linear map between Euclidean
coefficient and representation spaces. -/
noncomputable def euclideanDictionarySynthesis {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) :
    EuclideanRepresentation M →L[ℝ] EuclideanRepresentation d :=
  ((representationToEuclidean d).toLinearMap.comp
    (B.mulVecLin.comp (representationToEuclidean M).symm.toLinearMap)).toContinuousLinearMap

@[simp] theorem euclideanDictionarySynthesis_apply {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (u : EuclideanRepresentation M) :
    euclideanDictionarySynthesis B u =
      representationToEuclidean d (B.mulVec ((representationToEuclidean M).symm u)) := rfl

/-- The actual Euclidean nonnegative orthant. -/
def nonnegativeCoefficientOrthant (M : ℕ) : Set (EuclideanRepresentation M) :=
  {u | ∀ j, 0 ≤ u j}

theorem isClosed_nonnegativeCoefficientOrthant (M : ℕ) :
    IsClosed (nonnegativeCoefficientOrthant M) := by
  have heq : nonnegativeCoefficientOrthant M =
      ⋂ j : Fin M, {u : EuclideanRepresentation M | 0 ≤ u j} := by ext u; simp [nonnegativeCoefficientOrthant]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le continuous_const
    (PiLp.continuous_apply 2 (fun _ : Fin M => ℝ) j)

theorem convex_nonnegativeCoefficientOrthant (M : ℕ) :
    Convex ℝ (nonnegativeCoefficientOrthant M) := by
  intro u hu v hv a b ha hb _ j
  change 0 ≤ a * u j + b * v j
  exact add_nonneg (mul_nonneg ha (hu j)) (mul_nonneg hb (hv j))

/-- The image of the nonnegative orthant under actual dictionary synthesis. -/
noncomputable def nonnegativeSynthesisCone {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) : Set (EuclideanRepresentation d) :=
  euclideanDictionarySynthesis B '' nonnegativeCoefficientOrthant M

theorem nonnegativeSynthesisCone_nonempty {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) : (nonnegativeSynthesisCone B).Nonempty := by
  exact ⟨0, 0, fun _ => le_rfl, map_zero _⟩

theorem convex_nonnegativeSynthesisCone {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) : Convex ℝ (nonnegativeSynthesisCone B) :=
  (convex_nonnegativeCoefficientOrthant M).linear_image (euclideanDictionarySynthesis B).toLinearMap

/-- Global lower stability supplies a quantitative inverse bound for
synthesis, in genuine Euclidean norms. -/
theorem euclideanDictionarySynthesis_antilipschitz {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    AntilipschitzWith ⟨γ⁻¹, (inv_pos.mpr hγ).le⟩ (euclideanDictionarySynthesis B) := by
  apply (euclideanDictionarySynthesis B).antilipschitz_of_bound
  intro u
  have h := hlower ((representationToEuclidean M).symm u)
  rw [(representationToEuclidean M).apply_symm_apply] at h
  change ‖u‖ ≤ γ⁻¹ * ‖euclideanDictionarySynthesis B u‖
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using h)

/-- The nonnegative synthesis cone is closed under the global singular
margin. This is derived from the dictionary, not assumed of its image. -/
theorem isClosed_nonnegativeSynthesisCone {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    IsClosed (nonnegativeSynthesisCone B) :=
  ((euclideanDictionarySynthesis_antilipschitz B γ hγ hlower).isClosedEmbedding
    (euclideanDictionarySynthesis B).uniformContinuous).isClosedMap _
      (isClosed_nonnegativeCoefficientOrthant M)

/-- A code minimizes actual squared Euclidean residual among all
coordinatewise nonnegative codes. -/
def IsNonnegativeLeastSquaresCode {d M : ℕ} (B : Matrix (Fin d) (Fin M) ℝ)
    (x : EuclideanRepresentation d) (u : FeatureVector M) : Prop :=
  (∀ j, 0 ≤ u j) ∧ ∀ v : FeatureVector M, (∀ j, 0 ≤ v j) →
    ‖x - representationToEuclidean d (B.mulVec u)‖ ^ 2 ≤
      ‖x - representationToEuclidean d (B.mulVec v)‖ ^ 2

/-- Hilbert projection onto the derived closed convex cone provides an
actual nonnegative least-squares coefficient vector for every input. -/
theorem exists_nonnegativeLeastSquaresCode {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) :
    ∃ u : FeatureVector M, IsNonnegativeLeastSquaresCode B x u := by
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (nonnegativeSynthesisCone_nonempty B) (isClosed_nonnegativeSynthesisCone B γ hγ hlower).isComplete
    (convex_nonnegativeSynthesisCone B) x
  obtain ⟨u, hu, rfl⟩ := hy
  refine ⟨(representationToEuclidean M).symm u, hu, ?_⟩
  intro v hv
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  change ‖x - euclideanDictionarySynthesis B u‖ ≤ _
  rw [hmin]
  apply ciInf_le _ (⟨representationToEuclidean d (B.mulVec v), ?_⟩ : nonnegativeSynthesisCone B)
  · exact ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  · exact ⟨representationToEuclidean M v, hv, by simp⟩

/-- The cone-projection variational inequality is a consequence of actual
squared-residual optimality, for every feasible comparison code. -/
theorem IsNonnegativeLeastSquaresCode.inner_le_zero {d M : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {x : EuclideanRepresentation d} {u : FeatureVector M}
    (hu : IsNonnegativeLeastSquaresCode B x u) (v : FeatureVector M) (hv : ∀ j, 0 ≤ v j) :
    inner ℝ (x - representationToEuclidean d (B.mulVec u))
      (representationToEuclidean d (B.mulVec v) - representationToEuclidean d (B.mulVec u)) ≤ 0 := by
  have humem : representationToEuclidean d (B.mulVec u) ∈ nonnegativeSynthesisCone B :=
    ⟨representationToEuclidean M u, hu.1, by simp⟩
  letI : Nonempty (nonnegativeSynthesisCone B) := ⟨⟨_, humem⟩⟩
  have hmin : ‖x - representationToEuclidean d (B.mulVec u)‖ =
      ⨅ w : nonnegativeSynthesisCone B, ‖x - w‖ := by
    apply le_antisymm
    · apply le_ciInf
      rintro ⟨y, v', hv', rfl⟩
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        (hu.2 ((representationToEuclidean M).symm v') hv')
    · apply ciInf_le _ (⟨_, humem⟩ : nonnegativeSynthesisCone B)
      exact ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero (convex_nonnegativeSynthesisCone B) humem).mp hmin
    _ ⟨representationToEuclidean M v, hv, by simp⟩

/-- Reconstruction vectors selected by nonnegative least squares are
nonexpansive functions of the input, even before assuming injectivity. -/
theorem nonnegativeLeastSquares_synthesis_distance_le {d M : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {x y : EuclideanRepresentation d}
    {u v : FeatureVector M}
    (hu : IsNonnegativeLeastSquaresCode B x u) (hv : IsNonnegativeLeastSquaresCode B y v) :
    ‖representationToEuclidean d (B.mulVec u) - representationToEuclidean d (B.mulVec v)‖ ≤ ‖x - y‖ := by
  let a := representationToEuclidean d (B.mulVec u)
  let b := representationToEuclidean d (B.mulVec v)
  have h1 := hu.inner_le_zero v hv.1
  have h2 := hv.inner_le_zero u hu.1
  change inner ℝ (x - a) (b - a) ≤ 0 at h1
  change inner ℝ (y - b) (a - b) ≤ 0 at h2
  rw [show b - a = -(a - b) by abel, inner_neg_right] at h1
  have hsum : 0 ≤ inner ℝ ((x - a) - (y - b)) (a - b) := by
    rw [inner_sub_left]
    linarith
  rw [show (x - a) - (y - b) = (x - y) - (a - b) by abel,
    inner_sub_left, real_inner_self_eq_norm_sq] at hsum
  have hcauchy := real_inner_le_norm (x - y) (a - b)
  change ‖a - b‖ ≤ ‖x - y‖
  by_cases hzero : ‖a - b‖ = 0
  · rw [hzero]
    exact norm_nonneg _
  · have hpos : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

/-- Global lower stability upgrades uniqueness of the cone projection to
uniqueness of the coefficient vector. -/
theorem existsUnique_nonnegativeLeastSquaresCode {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) :
    ∃! u : FeatureVector M, IsNonnegativeLeastSquaresCode B x u := by
  obtain ⟨u, hu⟩ := exists_nonnegativeLeastSquaresCode B γ hγ hlower x
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hnorm := nonnegativeLeastSquares_synthesis_distance_le hv hu
  rw [sub_self, norm_zero] at hnorm
  have heq : representationToEuclidean d (B.mulVec v) =
      representationToEuclidean d (B.mulVec u) := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  have hinj := (euclideanDictionarySynthesis_antilipschitz B γ hγ hlower).injective
  apply (representationToEuclidean M).injective
  apply hinj
  simpa only [euclideanDictionarySynthesis_apply, (representationToEuclidean M).symm_apply_apply] using heq

/-- Global stability and nonexpansiveness give a Lipschitz bound for any
two actual optimal coefficient vectors. -/
theorem nonnegativeLeastSquares_code_distance_le {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    {x y : EuclideanRepresentation d} {u v : FeatureVector M}
    (hu : IsNonnegativeLeastSquaresCode B x u)
    (hv : IsNonnegativeLeastSquaresCode B y v) :
    ‖representationToEuclidean M u - representationToEuclidean M v‖ ≤ ‖x - y‖ / γ := by
  have hinv := (euclideanDictionarySynthesis_antilipschitz B γ hγ hlower).le_mul_dist
    (representationToEuclidean M u) (representationToEuclidean M v)
  simp only [dist_eq_norm, euclideanDictionarySynthesis_apply,
    (representationToEuclidean M).symm_apply_apply] at hinv
  have hmul := mul_le_mul_of_nonneg_left
    (nonnegativeLeastSquares_synthesis_distance_le hu hv) (inv_pos.mpr hγ).le
  exact hinv.trans (by simpa only [div_eq_inv_mul] using hmul)

/-- Zero is an optimal nonnegative code for the zero input. -/
theorem zero_isNonnegativeLeastSquaresCode {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) : IsNonnegativeLeastSquaresCode B 0 0 := by
  constructor
  · intro j
    exact le_rfl
  · intro v _
    simp only [Matrix.mulVec_zero, map_zero, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact sq_nonneg _

/-- Optimal coefficients satisfy a stronger bound than the elementary
twice-input bound, because projection onto this cone fixes zero. -/
theorem IsNonnegativeLeastSquaresCode.norm_le {d M : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    {x : EuclideanRepresentation d} {u : FeatureVector M}
    (hu : IsNonnegativeLeastSquaresCode B x u) :
    ‖representationToEuclidean M u‖ ≤ ‖x‖ / γ := by
  simpa only [map_zero, sub_zero] using
    nonnegativeLeastSquares_code_distance_le B γ hγ hlower hu
      (zero_isNonnegativeLeastSquaresCode B)

/-- The unique actual nonnegative least-squares code for a globally stable
dictionary. Its dependence on the input is continuous, as proved below. -/
noncomputable def nonnegativeLeastSquaresCode {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) : FeatureVector M :=
  Classical.choose (exists_nonnegativeLeastSquaresCode B γ hγ hlower x)

theorem nonnegativeLeastSquaresCode_isMinimizer {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) :
    IsNonnegativeLeastSquaresCode B x (nonnegativeLeastSquaresCode B γ hγ hlower x) :=
  Classical.choose_spec (exists_nonnegativeLeastSquaresCode B γ hγ hlower x)

/-- Every actual nonnegative minimizer equals the selected code. -/
theorem IsNonnegativeLeastSquaresCode.eq_nonnegativeLeastSquaresCode {d M : ℕ}
    {B : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    {x : EuclideanRepresentation d} {u : FeatureVector M}
    (hu : IsNonnegativeLeastSquaresCode B x u) :
    u = nonnegativeLeastSquaresCode B γ hγ hlower x :=
  (existsUnique_nonnegativeLeastSquaresCode B γ hγ hlower x).unique hu
    (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower x)

/-- The Euclidean coefficient-valued solution map is globally Lipschitz
with constant the reciprocal singular margin. -/
theorem nonnegativeLeastSquaresCode_lipschitz {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    LipschitzWith ⟨γ⁻¹, (inv_pos.mpr hγ).le⟩
      (fun x => representationToEuclidean M (nonnegativeLeastSquaresCode B γ hγ hlower x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, div_eq_inv_mul] using
    nonnegativeLeastSquares_code_distance_le B γ hγ hlower
      (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower x)
      (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower y)

/-- Continuity also holds in the ordinary finite coefficient coordinates. -/
theorem continuous_nonnegativeLeastSquaresCode {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    Continuous (nonnegativeLeastSquaresCode B γ hγ hlower) := by
  simpa only [Function.comp_def, (representationToEuclidean M).symm_apply_apply] using
    (representationToEuclidean M).symm.continuous.comp
      (nonnegativeLeastSquaresCode_lipschitz B γ hγ hlower).continuous

theorem measurable_nonnegativeLeastSquaresCode {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    Measurable (nonnegativeLeastSquaresCode B γ hγ hlower) :=
  (continuous_nonnegativeLeastSquaresCode B γ hγ hlower).measurable

theorem nonnegativeLeastSquaresCode_norm_le {d M : ℕ}
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector M, γ * ‖representationToEuclidean M u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (x : EuclideanRepresentation d) :
    ‖representationToEuclidean M (nonnegativeLeastSquaresCode B γ hγ hlower x)‖ ≤ ‖x‖ / γ :=
  (nonnegativeLeastSquaresCode_isMinimizer B γ hγ hlower x).norm_le hγ hlower

end PKG26AtomicFeatures
