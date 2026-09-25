import PKG26AtomicFeatures.DensityBoundedCoefficients
import PKG26AtomicFeatures.ProjectedCoefficientCodes
import PKG26AtomicFeatures.SupportConditioning

/-!
# Local support recovery under a lower density bound

A finite family of projected coefficient maps admits a measurable minimum
residual selector. Lower domination of the coefficient law then transports
small reconstruction loss to the uniform cube law. The uniform incidence
estimate supplies an exact `K`-column learned support, with constants that
depend on no upper density bound or support-separation parameter.
-/

namespace PKG26AtomicFeatures

universe u

open MeasureTheory Set
open scoped ENNReal

/-- A nonempty finite family of measurable candidates has a measurable
selector attaining its minimum measurable cost at every input. -/
private theorem exists_measurable_finite_minimum
    {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → X → Y)
    (q : X → Y → ℝ) (hf : ∀ i ∈ s, Measurable (f i))
    (hq : ∀ i ∈ s, Measurable fun x => q x (f i x)) :
    ∃ g : X → Y, Measurable g ∧ Measurable (fun x => q x (g x)) ∧
      (∀ x, ∃ i ∈ s, g x = f i x) ∧
      ∀ x i, i ∈ s → q x (g x) ≤ q x (f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert a s ha ih =>
    by_cases hsempty : s.Nonempty
    · obtain ⟨g, hg, hqg, hmem, hmin⟩ := ih hsempty
        (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hq i (Finset.mem_insert_of_mem hi))
      let g' := fun x => if q x (f a x) ≤ q x (g x) then f a x else g x
      refine ⟨g', (hf a (Finset.mem_insert_self _ _)).ite
        (measurableSet_le (hq a (Finset.mem_insert_self _ _)) hqg) hg, ?_, ?_, ?_⟩
      · have heq : (fun x => q x (g' x)) = fun x =>
            if q x (f a x) ≤ q x (g x) then q x (f a x) else q x (g x) := by
          funext x
          dsimp [g']; split_ifs <;> rfl
        rw [heq]
        exact (hq a (Finset.mem_insert_self _ _)).ite
          (measurableSet_le (hq a (Finset.mem_insert_self _ _)) hqg) hqg
      · intro x
        dsimp [g']
        split_ifs
        · exact ⟨a, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨i, hi, heq⟩ := hmem x
          exact ⟨i, Finset.mem_insert_of_mem hi, heq⟩
      · intro x i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · dsimp [g']; split_ifs with h
          · exact le_rfl
          · exact (lt_of_not_ge h).le
        · dsimp [g']; split_ifs with h
          · exact h.trans (hmin x i hi)
          · exact hmin x i hi
    · have hseq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsempty
      subst s
      refine ⟨f a, hf a (by simp), hq a (by simp), fun x => ⟨a, by simp, rfl⟩, ?_⟩
      intro x i hi
      have heq : i = a := by simpa using hi
      subst i
      exact le_rfl

/-- Stable sparse least-squares approximation has a measurable encoder.
Its residual is no greater than that of any other at-most-`K` code. -/
theorem exists_measurable_best_sparse_code
    {d M K : ℕ}
    (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
    (B : Matrix (Fin d) (Fin M) ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hstable : SparseLowerStable B γ (2 * K)) :
    ∃ code : EuclideanRepresentation K → FeatureVector M,
      Measurable code ∧ (∀ z, (nonzeroSupport (code z)).card ≤ K) ∧
      ∀ z v, (nonzeroSupport v).card ≤ K →
        ‖F z - representationToEuclidean d (B.mulVec (code z))‖ ≤
          ‖F z - representationToEuclidean d (B.mulVec v)‖ := by
  classical
  let I := {T : Finset (Fin M) // T.card ≤ K}
  have hD (T : I) := exists_projected_support_coefficient_map F B T.1 γ hγ hstable T.2
  choose D hsupp hproj using hD
  let f : I → EuclideanRepresentation K → FeatureVector M :=
    fun T z => (representationToEuclidean M).symm (D T z)
  let q := fun z v => ‖F z - representationToEuclidean d (B.mulVec v)‖
  have hf (T : I) : Measurable (f T) :=
    (representationToEuclidean M).symm.continuous.measurable.comp (D T).continuous.measurable
  have hq (T : I) : Measurable fun z => q z (f T z) :=
    (F.continuous.measurable.sub ((representationToEuclidean d).continuous.measurable.comp
      (B.mulVecLin.continuous_of_finiteDimensional.measurable.comp (hf T)))).norm
  have hnonempty : (Finset.univ : Finset I).Nonempty := ⟨⟨∅, by simp⟩, Finset.mem_univ _⟩
  obtain ⟨code, hcode, _, hmem, hmin⟩ := exists_measurable_finite_minimum
    Finset.univ hnonempty f q (fun T _ => hf T) (fun T _ => hq T)
  refine ⟨code, hcode, ?_, ?_⟩
  · intro z
    obtain ⟨T, _, heq⟩ := hmem z
    rw [heq]
    exact (Finset.card_le_card (hsupp T z)).trans T.2
  · intro z v hv
    let T : I := ⟨nonzeroSupport v, hv⟩
    have hminimal := hmin z T (Finset.mem_univ _)
    dsimp [q, f] at hminimal
    rw [hproj T z] at hminimal
    have hvspan : representationToEuclidean d (B.mulVec v) ∈ euclideanColumnSpan B T.1 :=
      (mem_euclideanColumnSpan_iff_exists_code B T.1 _).mpr ⟨v, Finset.Subset.refl _, rfl⟩
    have hproject := norm_orthogonal_projection_le_sub_of_mem
      (euclideanColumnSpan B T.1) (F z) _ hvspan
    rw [Submodule.starProjection_orthogonal, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply] at hproject
    exact hminimal.trans hproject

/-- Lower cube-density domination alone gives a width-independent small-loss
threshold for matching one source span to an exact `K`-column learned span. -/
theorem exists_lower_density_local_support_threshold
    (K : ℕ) (γ cLower ε : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcLower : 0 < cLower) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Z : Ω → EuclideanRepresentation K), Measurable Z →
        ENNReal.ofReal cLower • uniformCubeCoefficientLaw K ≤ Measure.map Z μ →
        ∀ (d m : ℕ) (F : EuclideanRepresentation K →L[ℝ] EuclideanRepresentation d)
          (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          (∀ z, γ * ‖z‖ ≤ ‖F z‖) → (∀ z, ‖F z‖ ≤ (K : ℝ) * ‖z‖) →
          (∀ j, ‖representationToEuclidean d (B.col j)‖ ≤ 1) →
          SparseLowerStable B γ (2 * K) →
          (∀ ω, (nonzeroSupport (code ω)).card ≤ K) →
          (∫⁻ ω, ENNReal.ofReal
            (‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ^ 2) ∂μ)
              ≤ ENNReal.ofReal δ →
          ∃ T : Finset (Fin m), T.card = K ∧
            ‖(LinearMap.range F.toLinearMap).starProjection -
              (euclideanColumnSpan B T).starProjection‖ ≤ ε := by
  let r := min ε (1 / 2 : ℝ)
  have hr : 0 < r := lt_min hε (by norm_num)
  have hrone : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  obtain ⟨δ₀, hδ₀, hinc⟩ := exists_density_bounded_sparse_subspace_incidence_threshold
    K γ 1 γ (K : ℝ) r hK hγ hγone zero_lt_one hγ hKr hr hrone
  refine ⟨cLower * δ₀, mul_pos hcLower hδ₀, ?_⟩
  intro Ω _ μ _ Z hZ hdom d m F B code hlower hupper hunit hstable hsparse hloss
  obtain ⟨best, hbest, hbestSparse, hbestMin⟩ :=
    exists_measurable_best_sparse_code F B γ hγ hstable
  let q := fun z => ENNReal.ofReal
    (‖F z - representationToEuclidean d (B.mulVec (best z))‖ ^ 2)
  have hq : Measurable q :=
    ((F.continuous.measurable.sub ((representationToEuclidean d).continuous.measurable.comp
      (B.mulVecLin.continuous_of_finiteDimensional.measurable.comp hbest))).norm.pow_const 2).ennreal_ofReal
  have htransfer : ENNReal.ofReal cLower * (∫⁻ z, q z ∂uniformCubeCoefficientLaw K) ≤
      ENNReal.ofReal cLower * ENNReal.ofReal δ₀ := by
    calc
      _ = ∫⁻ z, q z ∂(ENNReal.ofReal cLower • uniformCubeCoefficientLaw K) := by
        rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ z, q z ∂Measure.map Z μ := lintegral_mono' hdom le_rfl
      _ = ∫⁻ ω, q (Z ω) ∂μ := lintegral_map hq hZ
      _ ≤ ∫⁻ ω, ENNReal.ofReal
          (‖F (Z ω) - representationToEuclidean d (B.mulVec (code ω))‖ ^ 2) ∂μ := by
        apply lintegral_mono
        intro ω
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
          (hbestMin (Z ω) (code ω) (hsparse ω)) 2)
      _ ≤ ENNReal.ofReal (cLower * δ₀) := hloss
      _ = _ := ENNReal.ofReal_mul hcLower.le
  have hbestLoss : (∫⁻ z, q z ∂uniformCubeCoefficientLaw K) ≤ ENNReal.ofReal δ₀ :=
    (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr hcLower))
      ENNReal.ofReal_ne_top).mp htransfer
  obtain ⟨T, hT, hgap⟩ := hinc (EuclideanRepresentation K) (uniformCubeCoefficientLaw K)
    id measurable_id (by simp) d m F B best hbest hlower hupper hunit hstable hbestSparse hbestLoss
  exact ⟨T, hT, hgap.trans (min_le_left _ _)⟩

/-- Small conditional loss on any positive-probability source support gives
an exact `K`-column learned support with the requested span accuracy. The
threshold is chosen before the population, widths, and source support. -/
theorem exists_local_support_recovery_threshold
    (K : ℕ) (γ cLower ε : ℝ)
    (hK : 0 < K) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcLower : 0 < cLower) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (d M m : ℕ) (A : Matrix (Fin d) (Fin M) ℝ) (z : Ω → FeatureVector M),
        Measurable z → HasUnitEuclideanColumns A → SparseLowerStable A γ (2 * K) →
        ∀ (B : Matrix (Fin d) (Fin m) ℝ) (code : Ω → FeatureVector m),
          IsFeasibleRecoveryPair B code γ K →
          ∀ S : ExactSourceSupport M K, μ (sourceSupportEvent z S.1) ≠ 0 →
          ENNReal.ofReal cLower • uniformCubeCoefficientLaw K ≤
            Measure.map (sourceSupportCoordinates z S) (sourceSupportConditionalLaw μ z S.1) →
          actualPopulationSquaredLoss (sourceSupportConditionalLaw μ z S.1) A z B code ≤
            ENNReal.ofReal δ →
          ∃ T : Finset (Fin m), T.card = K ∧
            ‖(euclideanColumnSpan A S.1).starProjection -
              (euclideanColumnSpan B T).starProjection‖ ≤ ε := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_lower_density_local_support_threshold
    K γ cLower ε hK hγ hγone hcLower hε
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ μ _ d M m A z hz hAunit hAstable B code hfeas S hS hdom hloss
  have hsynth := sourceSupportConditionalLaw_ae_synthesis_eq μ A z hz S hS
  have hloss' : (∫⁻ x, ENNReal.ofReal
      (‖selectedSourceSynthesis A (sourceSupportEnumeration S) (sourceSupportCoordinates z S x) -
        representationToEuclidean d (B.mulVec (code x))‖ ^ 2)
        ∂sourceSupportConditionalLaw μ z S.1) ≤ ENNReal.ofReal δ := by
    apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hloss
    filter_upwards [hsynth] with x hx
    rw [hx]
  obtain ⟨T, hT, hgap⟩ := hlocal Ω (sourceSupportConditionalLaw μ z S.1)
    (sourceSupportCoordinates z S) (measurable_sourceSupportCoordinates z hz S) hdom d m
    (selectedSourceSynthesis A (sourceSupportEnumeration S)) B code
    (selectedSourceSynthesis_lower A _ γ hAstable)
    (selectedSourceSynthesis_upper A _ (fun j => (hAunit j).le))
    (fun j => (hfeas.1 j).le) hfeas.2.1 hfeas.2.2.2.1 hloss'
  exact ⟨T, hT, by simpa only [range_selectedSourceSynthesis, sourceSupportEnumeration_image] using hgap⟩

end PKG26AtomicFeatures
