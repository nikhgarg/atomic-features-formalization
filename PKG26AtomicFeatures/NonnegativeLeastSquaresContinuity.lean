import PKG26AtomicFeatures.NonnegativeLeastSquaresPopulation
import PKG26AtomicFeatures.MesoscaleReferenceBenchmark
import Mathlib.Topology.Order.Compact

/-!
# Joint continuity of nonnegative least squares

On dictionaries with one common positive global lower singular margin, the
actual unique nonnegative least-squares code is jointly continuous in the
dictionary and input. The proof derives a quantitative perturbation bound
from the two actual optimality inequalities and the previously proved code
norm bound. No continuity or minimizer-selection premise is assumed.
-/

namespace PKG26AtomicFeatures

open Set Topology
open scoped InnerProductSpace

/-- Synthesis is linear in the actual matrix, with values in Euclidean
continuous linear maps. -/
noncomputable def euclideanDictionarySynthesisLinear {d m : ℕ} :
    Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ]
      (EuclideanRepresentation m →L[ℝ] EuclideanRepresentation d) where
  toFun := euclideanDictionarySynthesis
  map_add' B C := by
    ext u
    simp only [euclideanDictionarySynthesis_apply, ContinuousLinearMap.add_apply,
      Matrix.add_mulVec, map_add]
  map_smul' a B := by
    ext u
    simp only [euclideanDictionarySynthesis_apply, ContinuousLinearMap.smul_apply,
      Matrix.smul_mulVec, map_smul, RingHom.id_apply]

theorem continuous_euclideanDictionarySynthesis {d m : ℕ} :
    Continuous (euclideanDictionarySynthesis (d := d) (M := m)) :=
  (euclideanDictionarySynthesisLinear (d := d) (m := m)).continuous_of_finiteDimensional

/-- The comparison with the zero code bounds the actual residual norm. -/
theorem IsNonnegativeLeastSquaresCode.residual_norm_le {d m : ℕ}
    {B : Matrix (Fin d) (Fin m) ℝ} {x : EuclideanRepresentation d}
    {u : FeatureVector m} (hu : IsNonnegativeLeastSquaresCode B x u) :
    ‖x - representationToEuclidean d (B.mulVec u)‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [Matrix.mulVec_zero, map_zero, sub_zero] using hu.2 0 (fun _ => le_rfl)

private theorem code_perturbation_of_variational_inequalities {d m : ℕ}
    (P Q : EuclideanRepresentation m →L[ℝ] EuclideanRepresentation d)
    (x y : EuclideanRepresentation d) (u v : EuclideanRepresentation m)
    (γ : ℝ) (hγ : 0 < γ)
    (hlower : γ * ‖u - v‖ ≤ ‖P (u - v)‖)
    (hfirst : 0 ≤ inner ℝ (x - P u) (P (u - v)))
    (hsecond : inner ℝ (y - Q v) (Q (u - v)) ≤ 0)
    (hv : ‖v‖ ≤ ‖y‖ / γ) (hr : ‖y - Q v‖ ≤ ‖y‖) :
    ‖u - v‖ ≤
      (‖P‖ * ‖x - y‖ + (‖P‖ / γ + 1) * ‖y‖ * ‖P - Q‖) / γ ^ 2 := by
  let w := u - v
  let r := y - Q v
  let a := x - y - (P - Q) v
  have halgebra :
      inner ℝ (x - P u) (P w) - inner ℝ r (Q w) =
        inner ℝ a (P w) + inner ℝ r ((P - Q) w) - ‖P w‖ ^ 2 := by
    dsimp [w, r, a]
    rw [← real_inner_self_eq_norm_sq]
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hsq : ‖P w‖ ^ 2 ≤ inner ℝ a (P w) + inner ℝ r ((P - Q) w) := by
    change 0 ≤ inner ℝ (x - P u) (P w) at hfirst
    change inner ℝ r (Q w) ≤ 0 at hsecond
    linarith
  have ha : ‖a‖ ≤ ‖x - y‖ + ‖P - Q‖ * (‖y‖ / γ) := by
    calc
      _ ≤ ‖x - y‖ + ‖(P - Q) v‖ := norm_sub_le _ _
      _ ≤ ‖x - y‖ + ‖P - Q‖ * ‖v‖ := add_le_add le_rfl ((P - Q).le_opNorm v)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (norm_nonneg (P - Q)))
  have hPw : ‖P w‖ ≤ ‖P‖ * ‖w‖ := P.le_opNorm w
  have hPQw : ‖(P - Q) w‖ ≤ ‖P - Q‖ * ‖w‖ := (P - Q).le_opNorm w
  have hbound : ‖P w‖ ^ 2 ≤
      (‖x - y‖ + ‖P - Q‖ * (‖y‖ / γ)) * (‖P‖ * ‖w‖) +
        ‖y‖ * (‖P - Q‖ * ‖w‖) := by
    calc
      _ ≤ ‖a‖ * ‖P w‖ + ‖r‖ * ‖(P - Q) w‖ :=
        hsq.trans (add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _))
      _ ≤ _ := add_le_add
        (mul_le_mul ha hPw (norm_nonneg _) (by positivity))
        (mul_le_mul hr hPQw (norm_nonneg _) (norm_nonneg _))
  have hstable : γ ^ 2 * ‖w‖ ^ 2 ≤ ‖P w‖ ^ 2 := by
    have h := (sq_le_sq₀ (mul_nonneg hγ.le (norm_nonneg _)) (norm_nonneg _)).mpr hlower
    simpa only [mul_pow] using h
  have hcombined : (γ ^ 2 * ‖w‖) * ‖w‖ ≤
      (‖P‖ * ‖x - y‖ + (‖P‖ / γ + 1) * ‖y‖ * ‖P - Q‖) * ‖w‖ := by
    calc
      _ = γ ^ 2 * ‖w‖ ^ 2 := by ring
      _ ≤ _ := hstable.trans hbound
      _ = _ := by ring
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ≤ _
    rw [hw]
    positivity
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    have hlinear := (mul_le_mul_iff_left₀ hwpos).mp hcombined
    apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
    simpa only [mul_comm] using hlinear

/-- Quantitative joint perturbation bound for any two actual nonnegative
least-squares minimizers. Only the dictionaries' common global margin is used. -/
theorem nonnegativeLeastSquares_joint_distance_le {d m : ℕ}
    (B C : Matrix (Fin d) (Fin m) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hB : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (B.mulVec u)‖)
    (hC : ∀ u : FeatureVector m, γ * ‖representationToEuclidean m u‖ ≤
      ‖representationToEuclidean d (C.mulVec u)‖)
    {x y : EuclideanRepresentation d} {u v : FeatureVector m}
    (hu : IsNonnegativeLeastSquaresCode B x u)
    (hv : IsNonnegativeLeastSquaresCode C y v) :
    ‖representationToEuclidean m u - representationToEuclidean m v‖ ≤
      (‖euclideanDictionarySynthesis B‖ * ‖x - y‖ +
        (‖euclideanDictionarySynthesis B‖ / γ + 1) * ‖y‖ *
          ‖euclideanDictionarySynthesis B - euclideanDictionarySynthesis C‖) / γ ^ 2 := by
  let P := euclideanDictionarySynthesis B
  let Q := euclideanDictionarySynthesis C
  have hP (w : FeatureVector m) : P (representationToEuclidean m w) =
      representationToEuclidean d (B.mulVec w) := by simp [P]
  have hQ (w : FeatureVector m) : Q (representationToEuclidean m w) =
      representationToEuclidean d (C.mulVec w) := by simp [Q]
  apply code_perturbation_of_variational_inequalities P Q x y
    (representationToEuclidean m u) (representationToEuclidean m v) γ hγ
  · simpa only [← map_sub, hP] using hB (u - v)
  · have h := hu.inner_le_zero v hv.1
    rw [show representationToEuclidean d (B.mulVec v) -
      representationToEuclidean d (B.mulVec u) =
      -(representationToEuclidean d (B.mulVec u) - representationToEuclidean d (B.mulVec v)) by abel,
      inner_neg_right] at h
    simp only [map_sub, hP]
    linarith
  · simpa only [map_sub, hQ] using hv.inner_le_zero u hu.1
  · exact hv.norm_le hγ hC
  · simpa only [hQ] using hv.residual_norm_le

/-- Actual dictionaries with a common global Euclidean lower margin. -/
abbrev GlobalStableDictionary (d m : ℕ) (γ : ℝ) :=
  {B : Matrix (Fin d) (Fin m) ℝ // ∀ u : FeatureVector m,
    γ * ‖representationToEuclidean m u‖ ≤ ‖representationToEuclidean d (B.mulVec u)‖}

/-- The canonical code on the stable-dictionary/input product. -/
noncomputable def stableDictionaryNNLSCode {d m : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (p : GlobalStableDictionary d m γ × EuclideanRepresentation d) : FeatureVector m :=
  nonnegativeLeastSquaresCode p.1.1 γ hγ p.1.2 p.2

/-- Joint continuity in the genuine Euclidean coefficient norm. -/
theorem continuous_stableDictionaryNNLSCode_euclidean {d m : ℕ}
    (γ : ℝ) (hγ : 0 < γ) :
    Continuous (fun p : GlobalStableDictionary d m γ × EuclideanRepresentation d =>
      representationToEuclidean m (stableDictionaryNNLSCode γ hγ p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let P := euclideanDictionarySynthesis p.1.1
  let g := fun q : GlobalStableDictionary d m γ × EuclideanRepresentation d =>
    (‖P‖ * ‖p.2 - q.2‖ + (‖P‖ / γ + 1) * ‖q.2‖ *
      ‖P - euclideanDictionarySynthesis q.1.1‖) / γ ^ 2
  have hg : Continuous g := by
    have hs : Continuous (fun q : GlobalStableDictionary d m γ × EuclideanRepresentation d =>
        euclideanDictionarySynthesis q.1.1) :=
      continuous_euclideanDictionarySynthesis.comp (continuous_subtype_val.comp continuous_fst)
    exact ((continuous_const.mul (continuous_const.sub continuous_snd).norm).add
      ((continuous_const.mul continuous_snd.norm).mul (continuous_const.sub hs).norm)).div_const _
  have hgp : g p = 0 := by simp [g, P]
  have hgtendsto : Filter.Tendsto g (𝓝 p) (𝓝 0) := hgp ▸ hg.continuousAt.tendsto
  apply squeeze_zero (fun q => norm_nonneg _) _ hgtendsto
  intro q
  rw [norm_sub_rev]
  exact nonnegativeLeastSquares_joint_distance_le p.1.1 q.1.1 γ hγ p.1.2 q.1.2
    (nonnegativeLeastSquaresCode_isMinimizer p.1.1 γ hγ p.1.2 p.2)
    (nonnegativeLeastSquaresCode_isMinimizer q.1.1 γ hγ q.1.2 q.2)

/-- The ordinary coordinate-valued canonical code is jointly continuous. -/
theorem continuous_stableDictionaryNNLSCode {d m : ℕ} (γ : ℝ) (hγ : 0 < γ) :
    Continuous (stableDictionaryNNLSCode (d := d) (m := m) γ hγ) := by
  simpa only [Function.comp_def, (representationToEuclidean m).symm_apply_apply] using
    (representationToEuclidean m).symm.continuous.comp
      (continuous_stableDictionaryNNLSCode_euclidean (d := d) (m := m) γ hγ)

/-- Joint continuity of the actual squared residual, with the same
canonical nonnegative code. -/
theorem continuous_stableDictionaryNNLS_squaredResidual {d m : ℕ}
    (γ : ℝ) (hγ : 0 < γ) :
    Continuous (fun p : GlobalStableDictionary d m γ × EuclideanRepresentation d =>
      ‖p.2 - representationToEuclidean d
        (p.1.1.mulVec (stableDictionaryNNLSCode γ hγ p))‖ ^ 2) := by
  have hs : Continuous (fun p : GlobalStableDictionary d m γ × EuclideanRepresentation d =>
      euclideanDictionarySynthesis p.1.1) :=
    continuous_euclideanDictionarySynthesis.comp (continuous_subtype_val.comp continuous_fst)
  have hc := continuous_stableDictionaryNNLSCode_euclidean (d := d) (m := m) γ hγ
  have hcompose := hs.clm_apply hc
  simpa only [euclideanDictionarySynthesis_apply,
    (representationToEuclidean m).symm_apply_apply] using
      (continuous_snd.sub hcompose).norm.pow 2


/-- Unit Euclidean column normalization is a closed constraint on the
actual finite matrix space. -/
theorem isClosed_hasUnitEuclideanColumns (d m : ℕ) :
    IsClosed {B : Matrix (Fin d) (Fin m) ℝ | HasUnitEuclideanColumns B} := by
  have heq : {B : Matrix (Fin d) (Fin m) ℝ | HasUnitEuclideanColumns B} =
      ⋂ j : Fin m, {B | ‖representationToEuclidean d (B.col j)‖ = 1} := by
    ext B
    simp [HasUnitEuclideanColumns]
  rw [heq]
  apply isClosed_iInter
  intro j
  have hc : Continuous (fun B : Matrix (Fin d) (Fin m) ℝ =>
      representationToEuclidean d (B.col j)) :=
    (representationToEuclidean d).continuous.comp (continuous_pi fun i =>
      (continuous_apply j).comp (continuous_apply i))
  exact isClosed_eq hc.norm continuous_const

/-- Every sparse singular-margin constraint is closed, including orders
smaller or larger than the dictionary width. -/
theorem isClosed_sparseLowerStable (d m s : ℕ) (γ : ℝ) :
    IsClosed {B : Matrix (Fin d) (Fin m) ℝ | SparseLowerStable B γ s} := by
  have heq : {B : Matrix (Fin d) (Fin m) ℝ | SparseLowerStable B γ s} =
      ⋂ v : FeatureVector m, {B | (nonzeroSupport v).card ≤ s →
        γ * ‖representationToEuclidean m v‖ ≤
          ‖representationToEuclidean d (B.mulVec v)‖} := by
    ext B
    simp [SparseLowerStable]
  rw [heq]
  apply isClosed_iInter
  intro v
  by_cases hv : (nonzeroSupport v).card ≤ s
  · simp only [hv, true_implies]
    have hc : Continuous (fun B : Matrix (Fin d) (Fin m) ℝ =>
        representationToEuclidean d (B.mulVec v)) := by
      simpa only [euclideanDictionarySynthesis_apply,
        (representationToEuclidean m).symm_apply_apply] using
        (continuous_euclideanDictionarySynthesis (d := d) (m := m)).clm_apply
          (continuous_const (y := representationToEuclidean m v))
    exact isClosed_le continuous_const hc.norm
  · simp only [hv, false_implies, setOf_true]
    exact isClosed_univ

/-- The actual unit-column, sparse-stable dictionary feasible set is
compact. Column normalization bounds every real matrix entry by one. -/
theorem isCompact_unitSparseLowerStable (d m s : ℕ) (γ : ℝ) :
    IsCompact {B : Matrix (Fin d) (Fin m) ℝ |
      HasUnitEuclideanColumns B ∧ SparseLowerStable B γ s} := by
  have hcube : IsCompact {B : Matrix (Fin d) (Fin m) ℝ |
      ∀ i j, B i j ∈ Set.Icc (-1 : ℝ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  apply hcube.of_isClosed_subset
    ((isClosed_hasUnitEuclideanColumns d m).inter (isClosed_sparseLowerStable d m s γ))
  intro B hB i j
  have hcoord := PiLp.norm_apply_le (representationToEuclidean d (B.col j)) i
  have hbound : |B i j| ≤ 1 := by
    simpa only [hB.1 j, Real.norm_eq_abs] using hcoord
  exact abs_le.mp hbound


/-- The literal normalized half-stable width-two reference dictionary class. -/
abbrev MesoscaleReferenceDictionary :=
  {B : Matrix (Fin 3) (Fin 2) ℝ //
    HasUnitEuclideanColumns B ∧ SparseLowerStable B (1 / 2) 4}

/-- Continuity of the actual reference objective on its feasible class. -/
theorem continuous_mesoscaleReferenceNNLSRisk :
    Continuous (fun B : MesoscaleReferenceDictionary => mesoscaleReferenceNNLSRisk B.1 B.2.2) := by
  unfold mesoscaleReferenceNNLSRisk
  apply continuous_finset_sum
  intro s _
  apply continuous_const.mul
  have hdict : Continuous (fun B : MesoscaleReferenceDictionary =>
      (⟨B.1, B.2.2.global_bound_of_width_le (by norm_num)⟩ :
        GlobalStableDictionary 3 2 (1 / 2))) := continuous_subtype_val.subtype_mk _
  have hpair := hdict.prodMk (continuous_const (y := mesoscaleReferenceInput s))
  simpa only [stableDictionaryNNLSCode] using
    (continuous_stableDictionaryNNLS_squaredResidual (d := 3) (m := 2) (1 / 2)
      (by norm_num)).comp hpair

/-- The actual NNLS reference objective attains its minimum on the actual
feasible dictionary class, and that minimum is below 49/100. -/
theorem exists_mesoscaleReferenceNNLSRisk_minimizer :
    ∃ B : Matrix (Fin 3) (Fin 2) ℝ,
      ∃ hB : HasUnitEuclideanColumns B ∧ SparseLowerStable B (1 / 2) 4,
        mesoscaleReferenceNNLSRisk B hB.2 < 49 / 100 ∧
        ∀ C : Matrix (Fin 3) (Fin 2) ℝ,
          ∀ hC : HasUnitEuclideanColumns C ∧ SparseLowerStable C (1 / 2) 4,
            mesoscaleReferenceNNLSRisk B hB.2 ≤ mesoscaleReferenceNNLSRisk C hC.2 := by
  letI : CompactSpace MesoscaleReferenceDictionary :=
    isCompact_iff_compactSpace.mp (isCompact_unitSparseLowerStable 3 2 4 (1 / 2))
  let benchmark : MesoscaleReferenceDictionary :=
    ⟨mesoscaleBenchmarkDictionary, mesoscaleBenchmarkDictionary_unit,
      mesoscaleBenchmarkDictionary_stable⟩
  obtain ⟨B, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (⟨benchmark, Set.mem_univ _⟩ : (Set.univ : Set MesoscaleReferenceDictionary).Nonempty)
    continuous_mesoscaleReferenceNNLSRisk.continuousOn
  refine ⟨B.1, B.2, ?_, ?_⟩
  · exact (@hmin benchmark (Set.mem_univ benchmark)).trans_lt mesoscaleBenchmark_referenceRisk_lt
  · intro C hC
    exact @hmin (⟨C, hC⟩ : MesoscaleReferenceDictionary) (Set.mem_univ _)

/-- The full set of actual reference minimizers is compact, a prerequisite
for preserving strict clipping uniformly near every minimizer. -/
theorem isCompact_mesoscaleReferenceNNLSRisk_minimizers :
    IsCompact {B : MesoscaleReferenceDictionary |
      ∀ C : MesoscaleReferenceDictionary,
        mesoscaleReferenceNNLSRisk B.1 B.2.2 ≤ mesoscaleReferenceNNLSRisk C.1 C.2.2} := by
  letI : CompactSpace MesoscaleReferenceDictionary :=
    isCompact_iff_compactSpace.mp (isCompact_unitSparseLowerStable 3 2 4 (1 / 2))
  have heq : {B : MesoscaleReferenceDictionary |
      ∀ C : MesoscaleReferenceDictionary,
        mesoscaleReferenceNNLSRisk B.1 B.2.2 ≤ mesoscaleReferenceNNLSRisk C.1 C.2.2} =
      ⋂ C : MesoscaleReferenceDictionary, {B |
        mesoscaleReferenceNNLSRisk B.1 B.2.2 ≤ mesoscaleReferenceNNLSRisk C.1 C.2.2} := by
    ext B
    simp
  rw [heq]
  exact (isClosed_iInter fun _ =>
    isClosed_le continuous_mesoscaleReferenceNNLSRisk continuous_const).isCompact

end PKG26AtomicFeatures
