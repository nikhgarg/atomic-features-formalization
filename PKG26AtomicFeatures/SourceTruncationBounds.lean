import PKG26AtomicFeatures.SelectedSourceMaps
import PKG26AtomicFeatures.WeightedGoodSupports
import PKG26AtomicFeatures.RegularPopulationModel

/-!
# Feasible source truncation and omitted prevalence

Retaining any distinct source columns preserves normalization and the
decoding margin. Bounded source activations give squared truncation loss at
most K times the number of omitted active features. Averaging this bound
produces the prevalence-tail comparator without independence assumptions.
-/

namespace PKG26AtomicFeatures

open scoped BigOperators ENNReal
open MeasureTheory Set

/-- Inserting zeros along an injective coordinate map does not increase
sparsity. -/
theorem insertSupportCode_card_le {m M : ℕ} (e : Fin m ↪ Fin M)
    (z : FeatureVector m) :
    (nonzeroSupport (insertSupportCode e z)).card ≤ (nonzeroSupport z).card :=
  (Finset.card_le_card (nonzeroSupport_embedSourceCode_subset e (fun _ => 1) z)).trans
    Finset.card_image_le

/-- Every source subdictionary inherits the same decoding margin through
the same sparsity order, even when that order exceeds its width. -/
theorem SparseLowerStable.subdictionary {d M m s : ℕ}
    {A : Matrix (Fin d) (Fin M) ℝ} {γ : ℝ}
    (hA : SparseLowerStable A γ s) (e : Fin m ↪ Fin M) :
    SparseLowerStable (A.submatrix id e) γ s := by
  intro z hz
  have h := hA (insertSupportCode e z) ((insertSupportCode_card_le e z).trans hz)
  rw [insertSupportCode_norm] at h
  have hsynth := mulVec_embedSourceCode (A.submatrix id e) A e (fun _ => 1)
    (fun _ => by rw [one_smul]; rfl) z
  simpa only [insertSupportCode, hsynth] using h

theorem HasUnitEuclideanColumns.subdictionary {d M m : ℕ}
    {A : Matrix (Fin d) (Fin M) ℝ} (hA : HasUnitEuclideanColumns A)
    (e : Fin m ↪ Fin M) : HasUnitEuclideanColumns (A.submatrix id e) :=
  fun j => hA (e j)

/-- Restricting a code to distinct selected coordinates preserves its
sparsity budget. -/
theorem restrictSupportCode_card_le {m M : ℕ} (e : Fin m ↪ Fin M)
    (z : FeatureVector M) :
    (nonzeroSupport (fun i => z (e i))).card ≤ (nonzeroSupport z).card := by
  classical
  apply Finset.card_le_card_of_injOn e
  · intro i hi
    simpa only [Finset.mem_coe, mem_nonzeroSupport_iff] using hi
  · exact fun _ _ _ _ h => e.injective h

/-- Omitted coefficients are precisely the active coordinates outside the
retained support. -/
theorem nonzeroSupport_truncation_residual {m M : ℕ} (e : Fin m ↪ Fin M)
    (z : FeatureVector M) :
    nonzeroSupport (z - insertSupportCode e (fun i => z (e i))) =
      nonzeroSupport z \ Finset.univ.image e := by
  classical
  ext j
  by_cases hj : j ∈ Finset.univ.image e
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    simp [Finset.mem_sdiff]
  · have hz : insertSupportCode e (fun i => z (e i)) j = 0 := by
      by_contra hn
      exact hj (insertSupportCode_support_subset e _ ((mem_nonzeroSupport_iff _ _).mpr hn))
    simp [Finset.mem_sdiff, hj, hz]

/-- With source coefficients in the unit cube, omitting r active features
costs at most K*r squared error. No coefficient independence is used. -/
theorem source_truncation_squared_error_le_omitted_count {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (e : Fin m ↪ Fin M)
    (hA : ∀ j, ‖representationToEuclidean d (A.col j)‖ ≤ 1)
    (z : FeatureVector M) (hz : (nonzeroSupport z).card ≤ K)
    (hbounded : ∀ j, |z j| ≤ 1) :
    ‖representationToEuclidean d (A.mulVec z) -
      representationToEuclidean d ((A.submatrix id e).mulVec (fun i => z (e i)))‖ ^ 2 ≤
      (K : ℝ) * ((nonzeroSupport z \ Finset.univ.image e).card : ℝ) := by
  classical
  let v := z - insertSupportCode e (fun i => z (e i))
  have hsupport := nonzeroSupport_truncation_residual e z
  have hcard : (nonzeroSupport v).card ≤ K := by
    rw [show nonzeroSupport v = nonzeroSupport z \ Finset.univ.image e from hsupport]
    exact (Finset.card_le_card Finset.sdiff_subset).trans hz
  have hcoeff : ∀ j ∈ nonzeroSupport v, |v j| ≤ 1 := by
    intro j hj
    have hout : j ∉ Finset.univ.image e := (Finset.mem_sdiff.mp (hsupport ▸ hj)).2
    have hins : insertSupportCode e (fun i => z (e i)) j = 0 := by
      by_contra hn
      exact hout (insertSupportCode_support_subset e _ ((mem_nonzeroSupport_iff _ _).mpr hn))
    simpa only [v, Pi.sub_apply, hins, sub_zero] using hbounded j
  have hnorm : ‖representationToEuclidean d (A.mulVec v)‖ ≤ (nonzeroSupport v).card := by
    calc
      _ ≤ ∑ j ∈ nonzeroSupport v, |v j| := euclidean_mulVec_norm_le_sum_abs A hA v
      _ ≤ ∑ _j ∈ nonzeroSupport v, (1 : ℝ) := Finset.sum_le_sum hcoeff
      _ = _ := by simp
  have hsq : ‖representationToEuclidean d (A.mulVec v)‖ ^ 2 ≤
      (K : ℝ) * (nonzeroSupport v).card := by
    have hc : ((nonzeroSupport v).card : ℝ) ≤ K := by exact_mod_cast hcard
    nlinarith [norm_nonneg (representationToEuclidean d (A.mulVec v)),
      (Nat.cast_nonneg ((nonzeroSupport v).card) : (0 : ℝ) ≤ (nonzeroSupport v).card)]
  have hsynth := mulVec_embedSourceCode (A.submatrix id e) A e (fun _ => 1)
    (fun _ => by rw [one_smul]; rfl) (fun i => z (e i))
  rw [show nonzeroSupport v = nonzeroSupport z \ Finset.univ.image e from hsupport] at hsq
  simpa only [v, Matrix.mulVec_sub, map_sub, insertSupportCode, hsynth] using hsq

/-- The omitted marginal mass for an arbitrary retained set of features.
For the most prevalent m features this is the paper's prevalence tail. -/
noncomputable def omittedFeaturePrevalence
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (retained : Finset (Fin M)) : ℝ :=
  ∑ i ∈ Finset.univ \ retained, featurePrevalence μ z i

/-- Counting omitted active coordinates commutes with expectation. The
identity does not use independence, regularity, or a density assumption. -/
theorem lintegral_omitted_support_card
    {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (μ : Measure Ω) (z : Ω → FeatureVector M) (hz : Measurable z)
    (retained : Finset (Fin M)) :
    (∫⁻ x, ENNReal.ofReal (((nonzeroSupport (z x) \ retained).card : ℕ) : ℝ) ∂μ) =
      ∑ i ∈ Finset.univ \ retained, μ {x | z x i ≠ 0} := by
  classical
  have hevent (i : Fin M) : MeasurableSet {x | z x i ≠ 0} :=
    (measurableSet_eq_fun (measurable_pi_apply i |>.comp hz) measurable_const).compl
  have hcount (x : Ω) :
      ENNReal.ofReal (((nonzeroSupport (z x) \ retained).card : ℕ) : ℝ) =
        ∑ i ∈ Finset.univ \ retained,
          ({y | z y i ≠ 0} : Set Ω).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    rw [ENNReal.ofReal_natCast, Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [show nonzeroSupport (z x) \ retained =
      (Finset.univ \ retained).filter (fun i => z x i ≠ 0) by ext i; simp; tauto,
      Finset.sum_filter]
    simp [Set.indicator_apply]
  simp_rw [hcount]
  rw [lintegral_finset_sum _ (fun i _ => measurable_const.indicator (hevent i))]
  apply Finset.sum_congr rfl
  intro i _
  simp [lintegral_indicator_const (hevent i)]

/-- An actual truncated source dictionary has expected squared loss at
most K times the omitted feature prevalence. -/
theorem actualPopulationSquaredLoss_source_truncation_le
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (e : Fin m ↪ Fin M)
    (hA : HasUnitEuclideanColumns A) (hz : Measurable z)
    (hsparse : KSparse (K := K) z) (hnonneg : ∀ x j, 0 ≤ z x j)
    (hbounded : ∀ x j, z x j ≤ 1) :
    actualPopulationSquaredLoss μ A z (A.submatrix id e) (fun x j => z x (e j)) ≤
      ENNReal.ofReal ((K : ℝ) * omittedFeaturePrevalence μ z (Finset.univ.image e)) := by
  classical
  have hevent (j : Fin M) : {x | z x j ≠ 0} = {x | 0 < z x j} := by
    ext x
    simpa only [Set.mem_setOf_eq, ne_comm] using (hnonneg x j).lt_iff_ne.symm
  unfold actualPopulationSquaredLoss
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((K : ℝ) *
        ((nonzeroSupport (z x) \ Finset.univ.image e).card : ℝ)) ∂μ := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      exact source_truncation_squared_error_le_omitted_count A e (fun j => (hA j).le)
        (z x) (hsparse x) (fun j => by rw [abs_of_nonneg (hnonneg x j)]; exact hbounded x j)
    _ = ENNReal.ofReal (K : ℝ) *
        ∑ i ∈ Finset.univ \ Finset.univ.image e, μ {x | z x i ≠ 0} := by
      simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg K)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_omitted_support_card μ z hz]
    _ = _ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg K)]
      congr 1
      simp only [omittedFeaturePrevalence, featurePrevalence]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun i _ => measureReal_nonneg)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hevent, ofReal_measureReal]

/-- Source truncation is genuinely in the optimization class, including
the common decoding margin, normalization, nonnegative codes and sparsity. -/
theorem IsFeasibleRecoveryPair.source_truncation
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (e : Fin m ↪ Fin M) (γ : ℝ)
    (hA : HasUnitEuclideanColumns A) (hstable : SparseLowerStable A γ (2 * K))
    (hz : Measurable z) (hsparse : KSparse (K := K) z)
    (hnonneg : ∀ x j, 0 ≤ z x j) :
    IsFeasibleRecoveryPair (A.submatrix id e) (fun x j => z x (e j)) γ K := by
  refine ⟨hA.subdictionary e, hstable.subdictionary e, ?_, ?_, ?_⟩
  · exact measurable_pi_lambda _ (fun j => (measurable_pi_apply (e j)).comp hz)
  · intro x
    exact (restrictSupportCode_card_le e (z x)).trans (hsparse x)
  · exact fun x j => hnonneg x (e j)

/-- Constant-factor optimality converts the feasible source comparator
into a bound on the learned model's actual population loss. -/
theorem IsApproximatelyOptimalRecoveryPair.loss_le_omitted_prevalence
    {Ω : Type*} [MeasurableSpace Ω] {d M m K : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M)
    (B : Matrix (Fin d) (Fin m) ℝ) (u : Ω → FeatureVector m)
    (e : Fin m ↪ Fin M) (γ C : ℝ)
    (hopt : IsApproximatelyOptimalRecoveryPair μ A z B u γ C K)
    (hA : HasUnitEuclideanColumns A) (hstable : SparseLowerStable A γ (2 * K))
    (hz : Measurable z) (hsparse : KSparse (K := K) z)
    (hnonneg : ∀ x j, 0 ≤ z x j) (hbounded : ∀ x j, z x j ≤ 1)
    (hC : 0 ≤ C) :
    actualPopulationSquaredLoss μ A z B u ≤
      ENNReal.ofReal (C * K * omittedFeaturePrevalence μ z (Finset.univ.image e)) := by
  have hcompare := hopt.2 (A.submatrix id e) (fun x j => z x (e j))
    (IsFeasibleRecoveryPair.source_truncation A z e γ hA hstable hz hsparse hnonneg)
  have htrunc := actualPopulationSquaredLoss_source_truncation_le μ A z e
    hA hz hsparse hnonneg hbounded
  apply hcompare.trans
  calc
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal
        ((K : ℝ) * omittedFeaturePrevalence μ z (Finset.univ.image e)) :=
      mul_le_mul_left' htrunc _
    _ = _ := by rw [← ENNReal.ofReal_mul hC, mul_assoc]

end PKG26AtomicFeatures
