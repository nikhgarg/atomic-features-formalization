import PKG26AtomicFeatures.NonnegativeLeastSquaresDerivative
import PKG26AtomicFeatures.NonnegativeLeastSquaresPopulation
import PKG26AtomicFeatures.SymmetricFamilyCovariance
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual nonnegative rank-one recovery from symmetric second moments

The rank-one NNLS coefficient is proved to be the positive part of the
actual inner product. Finite input second moment controls every unit-column
risk. An actual quadratic moment identity and nonnegative inputs then force
every globally minimizing unit dictionary to use the positive symmetric
leading direction, even when the population includes a zero atom.
-/

namespace PKG26AtomicFeatures

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-- The actual one-column dictionary with the specified Euclidean column. -/
noncomputable def oneColumnDictionary {d : ℕ} (v : EuclideanRepresentation d) :
    Matrix (Fin d) (Fin 1) ℝ := fun i _ => v i

@[simp] theorem oneColumnDictionary_column {d : ℕ} (v : EuclideanRepresentation d) :
    representationToEuclidean d ((oneColumnDictionary v).col 0) = v := by
  ext j
  rfl

theorem oneColumnDictionary_unit {d : ℕ} (v : EuclideanRepresentation d) (hv : ‖v‖ = 1) :
    HasUnitEuclideanColumns (oneColumnDictionary v) := by
  intro j
  fin_cases j
  simpa using hv

/-- One-column matrix synthesis is genuine Euclidean scalar multiplication. -/
theorem one_column_euclidean_mulVec {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) (u : FeatureVector 1) :
    representationToEuclidean d (B.mulVec u) =
      u 0 • representationToEuclidean d (B.col 0) := by
  have h : B.mulVec u = u 0 • B.col 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.col, mul_comm]
  rw [h, map_smul]

/-- The actual scalar nonnegative least-squares coefficient for a unit ray. -/
noncomputable def nonnegativeRankOneCode {d : ℕ}
    (v x : EuclideanRepresentation d) : ℝ := max 0 (inner ℝ v x)

private theorem unit_ray_residual_sq {d : ℕ}
    (v x : EuclideanRepresentation d) (hv : ‖v‖ = 1) (t : ℝ) :
    ‖x - t • v‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 - 2 * t * inner ℝ v x := by
  rw [norm_sub_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs,
    real_inner_comm v x]
  ring

/-- The positive-part coefficient minimizes the actual nonnegative
one-column least-squares objective, for every input vector. -/
theorem nonnegativeRankOneCode_isMinimizer {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B)
    (x : EuclideanRepresentation d) :
    IsNonnegativeLeastSquaresCode B x
      (fun _ => nonnegativeRankOneCode (representationToEuclidean d (B.col 0)) x) := by
  refine ⟨fun _ => le_max_left _ _, ?_⟩
  intro u hu
  rw [one_column_euclidean_mulVec, one_column_euclidean_mulVec,
    unit_ray_residual_sq _ _ (hunit 0), unit_ray_residual_sq _ _ (hunit 0)]
  dsimp [nonnegativeRankOneCode]
  by_cases hi : 0 ≤ inner ℝ (representationToEuclidean d (B.col 0)) x
  · rw [max_eq_right hi]
    nlinarith [sq_nonneg (u 0 - inner ℝ (representationToEuclidean d (B.col 0)) x)]
  · rw [max_eq_left (le_of_not_ge hi)]
    have hproduct := mul_nonpos_of_nonneg_of_nonpos (hu 0) (le_of_not_ge hi)
    nlinarith [sq_nonneg (u 0)]

/-- Canonical NNLS agrees with the proved positive-part formula. -/
theorem one_column_nonnegativeLeastSquaresCode_eq {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B)
    (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector 1, γ * ‖representationToEuclidean 1 u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) (x : EuclideanRepresentation d) :
    nonnegativeLeastSquaresCode B γ hγ hlower x 0 =
      nonnegativeRankOneCode (representationToEuclidean d (B.col 0)) x := by
  have h := (nonnegativeRankOneCode_isMinimizer B hunit x).eq_nonnegativeLeastSquaresCode hγ hlower
  exact (congrArg (fun u : FeatureVector 1 => u 0) h).symm

/-- The actual squared residual removes the squared positive-part score. -/
theorem nonnegativeRankOneCode_residual_sq {d : ℕ}
    (v x : EuclideanRepresentation d) (hv : ‖v‖ = 1) :
    ‖x - nonnegativeRankOneCode v x • v‖ ^ 2 =
      ‖x‖ ^ 2 - nonnegativeRankOneCode v x ^ 2 := by
  rw [unit_ray_residual_sq v x hv]
  dsimp [nonnegativeRankOneCode]
  by_cases hi : 0 ≤ inner ℝ v x
  · rw [max_eq_right hi]
    ring
  · rw [max_eq_left (le_of_not_ge hi)]
    ring

/-- The canonical actual NNLS value is exactly this scalar residual. -/
theorem one_column_nonnegativeLeastSquaresValue_eq {d : ℕ}
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B)
    (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector 1, γ * ‖representationToEuclidean 1 u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) (x : EuclideanRepresentation d) :
    nonnegativeLeastSquaresValue B γ hγ hlower x =
      ‖x‖ ^ 2 - nonnegativeRankOneCode (representationToEuclidean d (B.col 0)) x ^ 2 := by
  rw [nonnegativeLeastSquaresValue, one_column_euclidean_mulVec,
    one_column_nonnegativeLeastSquaresCode_eq B hunit γ hγ hlower x,
    nonnegativeRankOneCode_residual_sq _ _ (hunit 0)]

/-- Actual expected NNLS squared residual for a one-column dictionary. -/
noncomputable def nonnegativeRankOnePopulationRisk
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (B : Matrix (Fin d) (Fin 1) ℝ) : ℝ :=
  ∫ ω, ‖f ω - nonnegativeRankOneCode (representationToEuclidean d (B.col 0)) (f ω) •
    representationToEuclidean d (B.col 0)‖ ^ 2 ∂μ

/-- Global minimization over actual unit-column dictionaries. At width one
nonnegative sparsity is automatic, and unit columns have global margin one. -/
def IsNonnegativeRankOnePopulationMinimizer
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (B : Matrix (Fin d) (Fin 1) ℝ) : Prop :=
  HasUnitEuclideanColumns B ∧ ∀ C : Matrix (Fin d) (Fin 1) ℝ, HasUnitEuclideanColumns C →
    nonnegativeRankOnePopulationRisk μ f B ≤ nonnegativeRankOnePopulationRisk μ f C

private theorem positive_part_sq_le_sq (r : ℝ) : (max 0 r) ^ 2 ≤ r ^ 2 := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_right hr]
  · rw [max_eq_left (le_of_not_ge hr)]
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using sq_nonneg r

private theorem unit_inner_sq_le_norm_sq {d : ℕ}
    (v x : EuclideanRepresentation d) (hv : ‖v‖ = 1) :
    inner ℝ v x ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := abs_real_inner_le_norm v x
  rw [hv, one_mul] at h
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h

/-- The finite input second moment controls every unit-direction second
moment and every clipped-score second moment. -/
theorem integrable_rank_one_scores
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (hf : Measurable f)
    (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (v : EuclideanRepresentation d) (hv : ‖v‖ = 1) :
    Integrable (fun ω => inner ℝ v (f ω) ^ 2) μ ∧
      Integrable (fun ω => nonnegativeRankOneCode v (f ω) ^ 2) μ := by
  have hmeas : Measurable (fun ω => inner ℝ v (f ω)) := measurable_const.inner hf
  constructor
  · apply hsecond.mono' (hmeas.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_sq] using unit_inner_sq_le_norm_sq v (f ω) hv
  · apply hsecond.mono' ((measurable_const.max hmeas).pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_sq] using
      (positive_part_sq_le_sq (inner ℝ v (f ω))).trans (unit_inner_sq_le_norm_sq v (f ω) hv)

/-- Finite moments justify the exact expected-loss decomposition. -/
theorem nonnegativeRankOnePopulationRisk_eq
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (hf : Measurable f)
    (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) :
    nonnegativeRankOnePopulationRisk μ f B =
      (∫ ω, ‖f ω‖ ^ 2 ∂μ) -
        ∫ ω, nonnegativeRankOneCode (representationToEuclidean d (B.col 0)) (f ω) ^ 2 ∂μ := by
  unfold nonnegativeRankOnePopulationRisk
  simp_rw [nonnegativeRankOneCode_residual_sq _ _ (hunit 0)]
  exact integral_sub hsecond (integrable_rank_one_scores μ f hf hsecond _ (hunit 0)).2

private theorem inner_nonneg_of_coordinates_nonneg
    (v x : EuclideanRepresentation 3) (hv : ∀ j, 0 ≤ v j) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ inner ℝ v x := by
  rw [PiLp.inner_apply]
  apply Finset.sum_nonneg
  intro j _
  change 0 ≤ x j * v j
  exact mul_nonneg (hx j) (hv j)

/-- The actual rank-one squared residual is integrable under a finite
input second moment, so its real expectation has no undefined-integral branch. -/
theorem integrable_nonnegativeRankOne_residual
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d) (hf : Measurable f)
    (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B) :
    Integrable (fun ω => ‖f ω - nonnegativeRankOneCode
      (representationToEuclidean d (B.col 0)) (f ω) •
        representationToEuclidean d (B.col 0)‖ ^ 2) μ := by
  have h := hsecond.sub (integrable_rank_one_scores μ f hf hsecond _ (hunit 0)).2
  exact h.congr (Filter.Eventually.of_forall fun ω =>
    (nonnegativeRankOneCode_residual_sq _ (f ω) (hunit 0)).symm)

private theorem symmetricFamily_covariance_parent_basis (a b c : ℝ) :
    inner ℝ (representationToEuclidean 3 ![1, 0, 0])
      (symmetricFamilyCovarianceAction a b c (representationToEuclidean 3 ![1, 0, 0])) = a := by
  simp only [symmetricFamilyCovarianceAction, symmetricFamilyCovariance, PiLp.inner_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [representationToEuclidean, real_inner_eq_re_inner, RCLike.inner_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The actual moment identity makes the leading value strictly positive.
In particular, no assumption that every input is nonzero is needed. -/
theorem symmetricFamilyLeadingValue_pos_of_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation 3) (a b c : ℝ) (hb : 0 < b)
    (hmoment : ∀ v : EuclideanRepresentation 3,
      (∫ ω, inner ℝ v (f ω) ^ 2 ∂μ) = inner ℝ v (symmetricFamilyCovarianceAction a b c v)) :
    0 < symmetricFamilyLeadingValue a b c := by
  have ha : 0 ≤ a := by
    rw [← symmetricFamily_covariance_parent_basis a b c, ← hmoment]
    exact integral_nonneg fun _ => sq_nonneg _
  exact ha.trans_lt (symmetricFamilyLeadingValue_gt a b c hb).1

/-- The canonical positive leading direction achieves the Rayleigh lower
loss on the actual nonnegative population, with an exact value identity. -/
theorem nonnegativeRankOnePopulationRisk_leading_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation 3) (hf : Measurable f)
    (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (a b c : ℝ) (hb : 0 < b)
    (hmoment : ∀ v : EuclideanRepresentation 3,
      (∫ ω, inner ℝ v (f ω) ^ 2 ∂μ) = inner ℝ v (symmetricFamilyCovarianceAction a b c v))
    (hnonneg : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ f ω j) :
    nonnegativeRankOnePopulationRisk μ f (oneColumnDictionary (symmetricFamilyLeadingDirection a b c)) =
      (∫ ω, ‖f ω‖ ^ 2 ∂μ) - symmetricFamilyLeadingValue a b c := by
  have hw := symmetricFamilyLeadingDirection_unit a b c
  rw [nonnegativeRankOnePopulationRisk_eq μ f hf hsecond _ (oneColumnDictionary_unit _ hw),
    oneColumnDictionary_column]
  congr 1
  calc
    _ = ∫ ω, inner ℝ (symmetricFamilyLeadingDirection a b c) (f ω) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hnonneg] with ω hω
      rw [nonnegativeRankOneCode, max_eq_right
        (inner_nonneg_of_coordinates_nonneg _ _
          (fun j => (symmetricFamilyLeadingDirection_pos a b c hb j).le) hω)]
    _ = _ := hmoment _
    _ = _ := (symmetricFamilyCovariance_rayleigh_eq_iff a b c hb _ hw).mpr (Or.inl rfl)

/-- The positive leading dictionary actually minimizes NNLS population
risk among all unit width-one dictionaries. -/
theorem leading_isNonnegativeRankOnePopulationMinimizer
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation 3) (hf : Measurable f)
    (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (a b c : ℝ) (hb : 0 < b)
    (hmoment : ∀ v : EuclideanRepresentation 3,
      (∫ ω, inner ℝ v (f ω) ^ 2 ∂μ) = inner ℝ v (symmetricFamilyCovarianceAction a b c v))
    (hnonneg : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ f ω j) :
    IsNonnegativeRankOnePopulationMinimizer μ f
      (oneColumnDictionary (symmetricFamilyLeadingDirection a b c)) := by
  refine ⟨oneColumnDictionary_unit _ (symmetricFamilyLeadingDirection_unit a b c), ?_⟩
  intro B hunit
  rw [nonnegativeRankOnePopulationRisk_leading_eq μ f hf hsecond a b c hb hmoment hnonneg,
    nonnegativeRankOnePopulationRisk_eq μ f hf hsecond B hunit]
  have hint := integrable_rank_one_scores μ f hf hsecond _ (hunit 0)
  have hclip : (∫ ω, nonnegativeRankOneCode (representationToEuclidean 3 (B.col 0)) (f ω) ^ 2 ∂μ) ≤
      ∫ ω, inner ℝ (representationToEuclidean 3 (B.col 0)) (f ω) ^ 2 ∂μ :=
    integral_mono hint.2 hint.1 fun _ => positive_part_sq_le_sq _
  rw [hmoment] at hclip
  have hray := symmetricFamilyCovariance_rayleigh_le a b c hb _ (hunit 0)
  linarith

/-- Every actual global unit-dictionary optimum has the positive leading
column. The negative Rayleigh maximizer has zero nonnegative scores and
strictly larger loss, even if the distribution has an atom at zero. -/
theorem IsNonnegativeRankOnePopulationMinimizer.column_eq_positive_leading
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → EuclideanRepresentation 3}
    {B : Matrix (Fin 3) (Fin 1) ℝ}
    (hmin : IsNonnegativeRankOnePopulationMinimizer μ f B)
    (hf : Measurable f) (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (a b c : ℝ) (hb : 0 < b)
    (hmoment : ∀ v : EuclideanRepresentation 3,
      (∫ ω, inner ℝ v (f ω) ^ 2 ∂μ) = inner ℝ v (symmetricFamilyCovarianceAction a b c v))
    (hnonneg : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ f ω j) :
    representationToEuclidean 3 (B.col 0) = symmetricFamilyLeadingDirection a b c := by
  have hcompare := hmin.2 (oneColumnDictionary (symmetricFamilyLeadingDirection a b c))
    (oneColumnDictionary_unit _ (symmetricFamilyLeadingDirection_unit a b c))
  rw [nonnegativeRankOnePopulationRisk_eq μ f hf hsecond B hmin.1,
    nonnegativeRankOnePopulationRisk_leading_eq μ f hf hsecond a b c hb hmoment hnonneg] at hcompare
  have hint := integrable_rank_one_scores μ f hf hsecond _ (hmin.1 0)
  have hclip : (∫ ω, nonnegativeRankOneCode (representationToEuclidean 3 (B.col 0)) (f ω) ^ 2 ∂μ) ≤
      ∫ ω, inner ℝ (representationToEuclidean 3 (B.col 0)) (f ω) ^ 2 ∂μ :=
    integral_mono hint.2 hint.1 fun _ => positive_part_sq_le_sq _
  rw [hmoment] at hclip
  have hray := symmetricFamilyCovariance_rayleigh_le a b c hb _ (hmin.1 0)
  have heq : inner ℝ (representationToEuclidean 3 (B.col 0))
      (symmetricFamilyCovarianceAction a b c (representationToEuclidean 3 (B.col 0))) =
        symmetricFamilyLeadingValue a b c := by linarith
  rcases (symmetricFamilyCovariance_rayleigh_eq_iff a b c hb _ (hmin.1 0)).mp heq with hpos | hneg
  · exact hpos
  · have hzero : (∫ ω, nonnegativeRankOneCode (representationToEuclidean 3 (B.col 0)) (f ω) ^ 2 ∂μ) = 0 := by
      calc
        _ = ∫ _ω, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hnonneg] with ω hω
          rw [nonnegativeRankOneCode, hneg, inner_neg_left]
          have hnonnegative := inner_nonneg_of_coordinates_nonneg
            (symmetricFamilyLeadingDirection a b c) (f ω)
            (fun j => (symmetricFamilyLeadingDirection_pos a b c hb j).le) hω
          rw [max_eq_left (neg_nonpos.mpr hnonnegative)]
          norm_num
        _ = 0 := integral_zero _ _
    have hpositive := symmetricFamilyLeadingValue_pos_of_moments μ f a b c hb hmoment
    linarith

/-- The unique actual NNLS coefficient of every optimum is the unclipped
positive leading score almost surely on the actual population. -/
theorem IsNonnegativeRankOnePopulationMinimizer.ae_code_eq_positive_leading_score
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → EuclideanRepresentation 3}
    {B : Matrix (Fin 3) (Fin 1) ℝ}
    (hmin : IsNonnegativeRankOnePopulationMinimizer μ f B)
    (hf : Measurable f) (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (a b c : ℝ) (hb : 0 < b)
    (hmoment : ∀ v : EuclideanRepresentation 3,
      (∫ ω, inner ℝ v (f ω) ^ 2 ∂μ) = inner ℝ v (symmetricFamilyCovarianceAction a b c v))
    (hnonneg : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ f ω j)
    (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector 1, γ * ‖representationToEuclidean 1 u‖ ≤
      ‖representationToEuclidean 3 (B.mulVec u)‖) :
    ∀ᵐ ω ∂μ, nonnegativeLeastSquaresCode B γ hγ hlower (f ω) 0 =
      inner ℝ (symmetricFamilyLeadingDirection a b c) (f ω) := by
  have hcolumn := hmin.column_eq_positive_leading hf hsecond a b c hb hmoment hnonneg
  filter_upwards [hnonneg] with ω hω
  rw [one_column_nonnegativeLeastSquaresCode_eq B hmin.1 γ hγ hlower (f ω),
    hcolumn, nonnegativeRankOneCode]
  exact max_eq_right (inner_nonneg_of_coordinates_nonneg _ _
    (fun j => (symmetricFamilyLeadingDirection_pos a b c hb j).le) hω)

/-- The population objective is exactly the integral of the canonical
actual NNLS value, for any supplied valid global margin. -/
theorem nonnegativeRankOnePopulationRisk_eq_integral_nnls
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (f : Ω → EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin 1) ℝ) (hunit : HasUnitEuclideanColumns B)
    (γ : ℝ) (hγ : 0 < γ)
    (hlower : ∀ u : FeatureVector 1, γ * ‖representationToEuclidean 1 u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖) :
    nonnegativeRankOnePopulationRisk μ f B =
      ∫ ω, nonnegativeLeastSquaresValue B γ hγ hlower (f ω) ∂μ := by
  unfold nonnegativeRankOnePopulationRisk
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [nonnegativeRankOneCode_residual_sq _ _ (hunit 0),
    one_column_nonnegativeLeastSquaresValue_eq B hunit γ hγ hlower]

/-- A formulation with no supplied stability witness: the unit optimum
itself provides the global margin used to define its actual canonical code. -/
theorem IsNonnegativeRankOnePopulationMinimizer.ae_canonical_code_eq_positive_leading_score
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → EuclideanRepresentation 3}
    {B : Matrix (Fin 3) (Fin 1) ℝ}
    (hmin : IsNonnegativeRankOnePopulationMinimizer μ f B)
    (hf : Measurable f) (hsecond : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (a b c : ℝ) (hb : 0 < b)
    (hmoment : ∀ v : EuclideanRepresentation 3,
      (∫ ω, inner ℝ v (f ω) ^ 2 ∂μ) = inner ℝ v (symmetricFamilyCovarianceAction a b c v))
    (hnonneg : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ f ω j) :
    ∀ᵐ ω ∂μ, nonnegativeLeastSquaresCode B 1 (by norm_num)
      ((one_column_unit_stable B hmin.1 1).global_bound_of_width_le (by norm_num)) (f ω) 0 =
        inner ℝ (symmetricFamilyLeadingDirection a b c) (f ω) :=
  hmin.ae_code_eq_positive_leading_score hf hsecond a b c hb hmoment hnonneg
    1 (by norm_num) ((one_column_unit_stable B hmin.1 1).global_bound_of_width_le (by norm_num))

end PKG26AtomicFeatures
