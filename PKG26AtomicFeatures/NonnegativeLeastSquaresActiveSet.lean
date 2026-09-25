import PKG26AtomicFeatures.NonnegativeLeastSquaresContinuity
import PKG26AtomicFeatures.SparseCodeGeometry

/-!
# KKT conditions and strict active-set stability for actual NNLS

The residual-column inner products are minus one half of the squared-loss
coordinate derivatives. Their nonpositivity and coordinate complementarity
are equivalent to actual nonnegative least-squares optimality. Joint
continuity then preserves strictly positive active coordinates and strictly
negative inactive scores; complementarity gives exact inactive zeros.
-/

namespace PKG26AtomicFeatures

open Set Topology
open scoped BigOperators InnerProductSpace

/-- Residual-column inner product, equal to minus half the squared-loss
partial derivative in the selected coefficient. -/
noncomputable def nnlsResidualColumnInner {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (x : EuclideanRepresentation d)
    (u : FeatureVector m) (j : Fin m) : ℝ :=
  inner ℝ (x - representationToEuclidean d (B.mulVec u))
    (representationToEuclidean d (B.col j))

/-- Increasing one nonnegative coordinate is a feasible variation, so the
corresponding residual-column score is nonpositive. -/
theorem IsNonnegativeLeastSquaresCode.columnResidual_nonpos {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {x : EuclideanRepresentation d}
    {u : FeatureVector m} (hu : IsNonnegativeLeastSquaresCode B x u) (j : Fin m) :
    nnlsResidualColumnInner B x u j ≤ 0 := by
  have hfeasible : ∀ k : Fin m, 0 ≤ u k + (Pi.single j 1 : FeatureVector m) k := by
    intro k
    apply add_nonneg (hu.1 k)
    by_cases hkj : k = j <;> simp [Pi.single_apply, hkj]
  have h := hu.inner_le_zero (u + Pi.single j 1) hfeasible
  simpa only [Matrix.mulVec_add, Matrix.mulVec_single_one, map_add,
    add_sub_cancel_left] using h

/-- Removing a coordinate completely is also a feasible variation.
Combined with its upward variation, this gives exact complementarity. -/
theorem IsNonnegativeLeastSquaresCode.coordinate_complementarity {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {x : EuclideanRepresentation d}
    {u : FeatureVector m} (hu : IsNonnegativeLeastSquaresCode B x u) (j : Fin m) :
    u j * nnlsResidualColumnInner B x u j = 0 := by
  have hfeasible : ∀ k : Fin m, 0 ≤ u k - (Pi.single j (u j) : FeatureVector m) k := by
    intro k
    by_cases hkj : k = j
    · subst k
      simp
    · simpa [Pi.single_apply, hkj] using hu.1 k
  have h := hu.inner_le_zero (u - Pi.single j (u j)) hfeasible
  have hchange : representationToEuclidean d (B.mulVec (u - Pi.single j (u j))) -
      representationToEuclidean d (B.mulVec u) =
        -(u j) • representationToEuclidean d (B.col j) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_single, op_smul_eq_smul, map_sub, map_smul]
    module
  rw [hchange, real_inner_smul_right] at h
  change -(u j) * nnlsResidualColumnInner B x u j ≤ 0 at h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (hu.1 j) (hu.columnResidual_nonpos j)
  linarith

/-- A strictly negative score forces an exactly zero coefficient at every
actual optimum. -/
theorem IsNonnegativeLeastSquaresCode.eq_zero_of_columnResidual_neg {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {x : EuclideanRepresentation d}
    {u : FeatureVector m} (hu : IsNonnegativeLeastSquaresCode B x u) (j : Fin m)
    (hj : nnlsResidualColumnInner B x u j < 0) : u j = 0 :=
  (mul_eq_zero.mp (hu.coordinate_complementarity j)).resolve_right hj.ne

/-- Every positive coefficient has zero coordinate score. -/
theorem IsNonnegativeLeastSquaresCode.columnResidual_eq_zero_of_pos {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {x : EuclideanRepresentation d}
    {u : FeatureVector m} (hu : IsNonnegativeLeastSquaresCode B x u) (j : Fin m)
    (hj : 0 < u j) : nnlsResidualColumnInner B x u j = 0 :=
  (mul_eq_zero.mp (hu.coordinate_complementarity j)).resolve_left hj.ne'

/-- Full KKT equivalence for the actual nonnegative quadratic program.
No rank or uniqueness assumption is needed for this characterization. -/
theorem isNonnegativeLeastSquaresCode_iff_kkt {d m : ℕ}
    (B : Matrix (Fin d) (Fin m) ℝ) (x : EuclideanRepresentation d)
    (u : FeatureVector m) :
    IsNonnegativeLeastSquaresCode B x u ↔
      (∀ j, 0 ≤ u j) ∧ (∀ j, nnlsResidualColumnInner B x u j ≤ 0) ∧
        ∀ j, u j * nnlsResidualColumnInner B x u j = 0 := by
  constructor
  · intro hu
    exact ⟨hu.1, hu.columnResidual_nonpos, hu.coordinate_complementarity⟩
  · rintro ⟨hnonneg, hscore, hcomplement⟩
    refine ⟨hnonneg, fun v hv => ?_⟩
    let r := x - representationToEuclidean d (B.mulVec u)
    have hcross : inner ℝ r (representationToEuclidean d (B.mulVec v) -
        representationToEuclidean d (B.mulVec u)) ≤ 0 := by
      rw [inner_sub_right, euclidean_mulVec_eq_sum B v, euclidean_mulVec_eq_sum B u,
        inner_sum, inner_sum]
      simp only [real_inner_smul_right]
      change (∑ j, v j * nnlsResidualColumnInner B x u j) -
        (∑ j, u j * nnlsResidualColumnInner B x u j) ≤ 0
      simp only [hcomplement, Finset.sum_const_zero, sub_zero]
      exact Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonneg_of_nonpos (hv j) (hscore j)
    have heq : x - representationToEuclidean d (B.mulVec v) =
        r - (representationToEuclidean d (B.mulVec v) -
          representationToEuclidean d (B.mulVec u)) := by dsimp [r]; abel
    conv_rhs => rw [heq, norm_sub_sq_real]
    change ‖r‖ ^ 2 ≤ _
    nlinarith [sq_nonneg ‖representationToEuclidean d (B.mulVec v) -
      representationToEuclidean d (B.mulVec u)‖]

/-- The canonical NNLS residual-column score on the actual stable
dictionary/input product. -/
noncomputable def stableDictionaryNNLSColumnResidual {d m : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (p : GlobalStableDictionary d m γ × EuclideanRepresentation d) (j : Fin m) : ℝ :=
  nnlsResidualColumnInner p.1.1 p.2 (stableDictionaryNNLSCode γ hγ p) j

theorem stableDictionaryNNLSCode_isMinimizer {d m : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (p : GlobalStableDictionary d m γ × EuclideanRepresentation d) :
    IsNonnegativeLeastSquaresCode p.1.1 p.2 (stableDictionaryNNLSCode γ hγ p) :=
  nonnegativeLeastSquaresCode_isMinimizer p.1.1 γ hγ p.1.2 p.2

/-- Each coordinate score is jointly continuous in the dictionary and
input; it is calculated from the actual continuous NNLS solution. -/
theorem continuous_stableDictionaryNNLSColumnResidual {d m : ℕ}
    (γ : ℝ) (hγ : 0 < γ) (j : Fin m) :
    Continuous (fun p : GlobalStableDictionary d m γ × EuclideanRepresentation d =>
      stableDictionaryNNLSColumnResidual γ hγ p j) := by
  have hs : Continuous (fun p : GlobalStableDictionary d m γ × EuclideanRepresentation d =>
      euclideanDictionarySynthesis p.1.1) :=
    continuous_euclideanDictionarySynthesis.comp (continuous_subtype_val.comp continuous_fst)
  have hc := continuous_stableDictionaryNNLSCode_euclidean (d := d) (m := m) γ hγ
  have hres := continuous_snd.sub (hs.clm_apply hc)
  have hcol := hs.clm_apply (continuous_const (y := representationToEuclidean m (Pi.single j 1)))
  simpa only [stableDictionaryNNLSColumnResidual, nnlsResidualColumnInner,
    euclideanDictionarySynthesis_apply, (representationToEuclidean m).symm_apply_apply,
    Matrix.mulVec_single_one] using hres.inner hcol

/-- Strict activity and strict inactivity persist on a neighborhood.
Complementarity gives exact inactive zeros, so the support itself is
locally constant without any assumption that support is continuous. -/
theorem eventually_stableDictionaryNNLS_support_eq {d m : ℕ}
    (γ : ℝ) (hγ : 0 < γ)
    (p : GlobalStableDictionary d m γ × EuclideanRepresentation d)
    (S : Finset (Fin m))
    (hactive : ∀ j ∈ S, 0 < stableDictionaryNNLSCode γ hγ p j)
    (hinactive : ∀ j ∉ S, stableDictionaryNNLSColumnResidual γ hγ p j < 0) :
    ∀ᶠ q in 𝓝 p,
      nonzeroSupport (stableDictionaryNNLSCode γ hγ q) = S ∧
        (∀ j ∈ S, 0 < stableDictionaryNNLSCode γ hγ q j) ∧
        ∀ j ∉ S, stableDictionaryNNLSColumnResidual γ hγ q j < 0 := by
  have hcoordinate (j : Fin m) :
      Continuous (fun q : GlobalStableDictionary d m γ × EuclideanRepresentation d =>
        stableDictionaryNNLSCode γ hγ q j) :=
    (continuous_apply j).comp (continuous_stableDictionaryNNLSCode γ hγ)
  have hlocal (j : Fin m) : ∀ᶠ q in 𝓝 p,
      (j ∈ S → 0 < stableDictionaryNNLSCode γ hγ q j) ∧
      (j ∉ S → stableDictionaryNNLSColumnResidual γ hγ q j < 0) := by
    by_cases hj : j ∈ S
    · have h := continuousAt_const.eventually_lt (hcoordinate j).continuousAt (hactive j hj)
      exact h.mono fun q hq => ⟨fun _ => hq, fun hn => (hn hj).elim⟩
    · have h := (continuous_stableDictionaryNNLSColumnResidual γ hγ j).continuousAt.eventually_lt
        continuousAt_const (hinactive j hj)
      exact h.mono fun q hq => ⟨fun hy => (hj hy).elim, fun _ => hq⟩
  filter_upwards [Filter.eventually_all.mpr hlocal] with q hq
  refine ⟨?_, fun j hj => (hq j).1 hj, fun j hj => (hq j).2 hj⟩
  ext j
  rw [mem_nonzeroSupport_iff]
  by_cases hj : j ∈ S
  · exact ⟨fun _ => hj, fun _ => ((hq j).1 hj).ne'⟩
  · have hzero := (stableDictionaryNNLSCode_isMinimizer γ hγ q).eq_zero_of_columnResidual_neg j
      ((hq j).2 hj)
    simp [hj, hzero]

/-- An explicit open neighborhood version of strict active-set stability. -/
theorem exists_open_stableDictionaryNNLS_support_eq {d m : ℕ}
    (γ : ℝ) (hγ : 0 < γ)
    (p : GlobalStableDictionary d m γ × EuclideanRepresentation d)
    (S : Finset (Fin m))
    (hactive : ∀ j ∈ S, 0 < stableDictionaryNNLSCode γ hγ p j)
    (hinactive : ∀ j ∉ S, stableDictionaryNNLSColumnResidual γ hγ p j < 0) :
    ∃ U : Set (GlobalStableDictionary d m γ × EuclideanRepresentation d),
      IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U,
        nonzeroSupport (stableDictionaryNNLSCode γ hγ q) = S ∧
          (∀ j ∈ S, 0 < stableDictionaryNNLSCode γ hγ q j) ∧
          ∀ j ∉ S, stableDictionaryNNLSColumnResidual γ hγ q j < 0 := by
  obtain ⟨U, hU, hopen, hp⟩ := mem_nhds_iff.mp
    (eventually_stableDictionaryNNLS_support_eq γ hγ p S hactive hinactive)
  exact ⟨U, hopen, hp, fun q hq => hU hq⟩

end PKG26AtomicFeatures
